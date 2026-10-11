"""Recursive-descent parser for Λ in ASCII or Unicode notation.

    \\x. M   λx. M   \\x:e. M   \\x : φ . M  (H&K domain condition ⇒ λx. ∂[φ] M)
    forall x. φ   ∀x[φ]   exists   iota   max d[φ]   card x[φ]
    ~ ¬   & ∧   | ∨   -> →   <-> ↔   = != < <= > >=   @[φ] M  ∂[φ] M   f(a)(b) = f(a, b)
"""
from __future__ import annotations

import re

from .typesys import Basic, Fun, BASIC_NAMES, TVar, D, fresh_tvar
from .terms import Var, Const, Num, App, Bind, Op, TOP, BOT


class ParseError(ValueError):
    pass


_TOKEN = re.compile(r"""
    (?P<ws>\s+)
  | (?P<num>\d+(?:\.\d+)?)
  | (?P<sym><->|->|<=|>=|!=|[=<>&|~()\[\],.:\\@λ∀∃ι¬∧∨→↔≤≥≠∂⊤⊥])
  | (?P<id>[A-Za-z_][A-Za-z0-9_']*)
""", re.X)

BINDER_KW = {"\\": "lam", "λ": "lam", "lambda": "lam", "forall": "forall", "∀": "forall",
             "exists": "exists", "∃": "exists", "iota": "iota", "ι": "iota",
             "max": "max", "card": "card"}
NOT_KW, AND_KW, OR_KW = {"~", "¬", "not"}, {"&", "∧", "and"}, {"|", "∨", "or"}
IMP_KW, IFF_KW = {"->", "→"}, {"<->", "↔"}
REL_KW = {"=": "eq", "!=": "neq", "≠": "neq", "<": "lt", "<=": "le", "≤": "le",
          ">": "gt", ">=": "ge", "≥": "ge"}


def tokenize(src: str) -> list:
    pos, out = 0, []
    while pos < len(src):
        m = _TOKEN.match(src, pos)
        if not m:
            raise ParseError(f"unexpected character {src[pos]!r} at {pos} in {src!r}")
        pos = m.end()
        if m.lastgroup != "ws":
            out.append((m.lastgroup, m.group()))
    return out


class _Parser:
    def __init__(self, src, free, consts):
        self.src, self.toks, self.i = src, tokenize(src), 0
        self.free, self.consts, self.scope = free, consts, []

    def peek(self):
        return self.toks[self.i][1] if self.i < len(self.toks) else None

    def kind(self):
        return self.toks[self.i][0] if self.i < len(self.toks) else None

    def next(self):
        if self.i >= len(self.toks):
            raise ParseError(f"unexpected end of term {self.src!r}")
        self.i += 1
        return self.toks[self.i - 1][1]

    def expect(self, tok):
        got = self.next()
        if got != tok:
            raise ParseError(f"expected {tok!r} but found {got!r} in {self.src!r}")

    def lookup(self, name):
        for frame in reversed(self.scope):
            if name in frame:
                return frame[name]
        if name in self.free:
            return self.free[name]
        if name not in self.consts:
            self.consts[name] = Const(name, TVar("κ:" + name))
        return self.consts[name]

    # precedence climbing: iff < imp < or < and < not/∂ < relations < application
    def term(self):
        t = self.imp()
        while self.peek() in IFF_KW:
            self.next()
            t = Op("iff", (t, self.imp()))
        return t

    def imp(self):
        t = self.disj()
        if self.peek() in IMP_KW:
            self.next()
            return Op("imp", (t, self.imp()))
        return t

    def disj(self):
        t = self.conj()
        while self.peek() in OR_KW:
            self.next()
            t = Op("or", (t, self.conj()))
        return t

    def conj(self):
        t = self.unary()
        while self.peek() in AND_KW:
            self.next()
            t = Op("and", (t, self.unary()))
        return t

    def unary(self):
        tok = self.peek()
        if tok in NOT_KW:
            self.next()
            return Op("not", (self.unary(),))
        if tok in ("∂", "@"):
            self.next()
            self.expect("[")
            c = self.term()
            self.expect("]")
            return Op("presup", (c, self.unary()))
        t = self.app()
        if self.peek() in REL_KW:
            op = REL_KW[self.next()]
            return Op(op, (t, self.app()))
        return t

    def app(self):
        t = self.atom()
        while self.peek() == "(":
            self.next()
            args = [self.term()]
            while self.peek() == ",":
                self.next()
                args.append(self.term())
            self.expect(")")
            for a in args:
                t = App(t, a)
        return t

    def atom(self):
        tok, kind = self.peek(), self.kind()
        if tok is None:
            raise ParseError(f"unexpected end of term {self.src!r}")
        if tok == "(":
            self.next()
            t = self.term()
            self.expect(")")
            return t
        if tok in BINDER_KW:
            return self.binder()
        if tok in ("⊤", "TRUE"):
            self.next()
            return TOP
        if tok in ("⊥", "FALSE"):
            self.next()
            return BOT
        if kind == "num":
            self.next()
            return Num(float(tok) if "." in tok else int(tok))
        if kind == "id":
            self.next()
            return self.lookup(tok)
        raise ParseError(f"unexpected token {tok!r} in {self.src!r}")

    def type_expr(self):
        tok = self.peek()
        if tok == "<":
            self.next()
            a = self.type_expr()
            self.expect(",")
            b = self.type_expr()
            self.expect(">")
            return Fun(a, b)
        if tok in BASIC_NAMES:
            self.next()
            return Basic(tok)
        raise ParseError("not a type")

    def try_type(self):
        save = self.i
        try:
            ty = self.type_expr()
        except ParseError:
            self.i = save
            return None
        if self.peek() in (".", "[", ":") or self.kind() == "id":
            return ty
        self.i = save
        return None

    def binder(self):
        kind = BINDER_KW[self.next()]
        vs, cond_pending = [], False
        while self.kind() == "id" and self.peek() not in BINDER_KW:
            name, ty = self.next(), None
            if self.peek() == ":":
                save = self.i
                self.next()
                ty = self.try_type()
                if ty is None:
                    self.i, cond_pending = save, True
            vs.append(Var(name, ty or (D if kind == "max" else fresh_tvar())))
            if cond_pending:
                break
        if not vs:
            raise ParseError(f"binder without a variable in {self.src!r}")
        self.scope.append({v.name: v for v in vs})
        try:
            cond = None
            if cond_pending:
                if kind != "lam":
                    raise ParseError(f"domain conditions are only allowed on λ in {self.src!r}")
                self.expect(":")
                cond = self.term()
            if self.peek() == "[" and kind != "lam":
                self.next()
                body = self.term()
                self.expect("]")
            else:
                self.expect(".")
                body = self.term()
        finally:
            self.scope.pop()
        if cond is not None:
            body = Op("presup", (cond, body))
        for v in reversed(vs):
            body = Bind(kind, v, body)
        return body


def parse_term(src: str, free: dict | None = None, consts: dict | None = None):
    """Parse src into an (as yet untyped) term; free identifiers become constants
    unless declared in `free` (e.g. the evaluation-world variable w)."""
    p = _Parser(src, free or {}, {} if consts is None else consts)
    t = p.term()
    if p.i != len(p.toks):
        raise ParseError(f"unexpected {p.peek()!r} after a complete term in {src!r}")
    return t
