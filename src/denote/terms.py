"""The term language Λ: a simply typed λ-calculus with logical constants, the binders
λ ∀ ∃ ι max card, and a definedness operator ∂ for partial (presuppositional) meanings."""
from __future__ import annotations

import re
from dataclasses import dataclass
from functools import lru_cache

from .typesys import Type, Fun, T, D


class Term:
    __slots__ = ()

    def __str__(self):
        return show(self)

    def __repr__(self):
        return show(self, "ascii")


@dataclass(frozen=True, repr=False)
class Var(Term):
    name: str
    type: Type


@dataclass(frozen=True, repr=False)
class Const(Term):
    name: str
    type: Type


@dataclass(frozen=True, repr=False)
class Num(Term):
    value: object


@dataclass(frozen=True, repr=False)
class App(Term):
    fun: Term
    arg: Term


@dataclass(frozen=True, repr=False)
class Bind(Term):
    kind: str            # lam | forall | exists | iota | max | card
    var: Var
    body: Term


@dataclass(frozen=True, repr=False)
class Op(Term):
    op: str              # not and or imp iff eq neq lt le gt ge presup top bot
    args: tuple


RELATIONS = ("eq", "neq", "lt", "le", "gt", "ge")
TOP, BOT = Op("top", ()), Op("bot", ())


def lam(v, b): return Bind("lam", v, b)
def forall(v, b): return Bind("forall", v, b)
def exists(v, b): return Bind("exists", v, b)
def neg(a): return Op("not", (a,))
def conj(a, b): return Op("and", (a, b))
def disj(a, b): return Op("or", (a, b))
def imp(a, b): return Op("imp", (a, b))
def eq(a, b): return Op("eq", (a, b))
def presup(c, b): return Op("presup", (c, b))


@lru_cache(maxsize=200_000)
def typeof(t: Term):
    if isinstance(t, (Var, Const)):
        return t.type
    if isinstance(t, Num):
        return D
    if isinstance(t, App):
        ft = typeof(t.fun)
        return ft.res if isinstance(ft, Fun) else None
    if isinstance(t, Bind):
        if t.kind == "lam":
            return Fun(t.var.type, typeof(t.body))
        if t.kind == "iota":
            return t.var.type
        return D if t.kind in ("max", "card") else T
    return typeof(t.args[1]) if t.op == "presup" else T


@lru_cache(maxsize=200_000)
def fv(t: Term) -> frozenset:
    if isinstance(t, Var):
        return frozenset((t,))
    if isinstance(t, (Const, Num)):
        return frozenset()
    if isinstance(t, App):
        return fv(t.fun) | fv(t.arg)
    if isinstance(t, Bind):
        return fv(t.body) - {t.var}
    out = frozenset()
    for a in t.args:
        out |= fv(a)
    return out


def walk(t: Term):
    yield t
    if isinstance(t, App):
        yield from walk(t.fun)
        yield from walk(t.arg)
    elif isinstance(t, Bind):
        yield from walk(t.body)
    elif isinstance(t, Op):
        for a in t.args:
            yield from walk(a)


def size(t: Term) -> int:
    return sum(1 for _ in walk(t))


def constants(t: Term, acc: dict | None = None) -> dict:
    acc = {} if acc is None else acc
    for s in walk(t):
        if isinstance(s, Const):
            acc[s.name] = s.type
    return acc


def fresh(base: str, ty: Type, *terms) -> Var:
    """A variable named base(′…) not free in any of `terms`."""
    avoid = set()
    for t in terms:
        if t is not None:
            avoid |= {v.name for v in fv(t)}
    n = base
    while n in avoid:
        n += "'"
    return Var(n, ty)


ALPHA = [0]  # global count of α-conversions performed by subst (for complexity metrics)


def subst(t: Term, v: Var, s: Term) -> Term:
    """Capture-avoiding substitution t[v := s]."""
    if v not in fv(t):
        return t
    if isinstance(t, Var):
        return s
    if isinstance(t, App):
        return App(subst(t.fun, v, s), subst(t.arg, v, s))
    if isinstance(t, Bind):
        if t.var in fv(s):
            avoid = {x.name for x in fv(s) | fv(t.body)} | {v.name}
            n = t.var.name
            while n in avoid:
                n += "'"
            nv = Var(n, t.var.type)
            ALPHA[0] += 1
            return Bind(t.kind, nv, subst(subst(t.body, t.var, nv), v, s))
        return Bind(t.kind, t.var, subst(t.body, v, s))
    return Op(t.op, tuple(subst(a, v, s) for a in t.args))


def replace_sub(t: Term, target: Term, repl: Term) -> Term:
    """Replace free occurrences of the subterm `target` by `repl`."""
    if t == target:
        return repl
    if isinstance(t, App):
        return App(replace_sub(t.fun, target, repl), replace_sub(t.arg, target, repl))
    if isinstance(t, Bind):
        if t.var in fv(target):
            return t
        return Bind(t.kind, t.var, replace_sub(t.body, target, repl))
    if isinstance(t, Op):
        return Op(t.op, tuple(replace_sub(a, target, repl) for a in t.args))
    return t


def alpha_key(t: Term, env: dict | None = None, depth: int = 0):
    """A hashable key identifying t up to α-equivalence (de Bruijn-style)."""
    env = {} if env is None else env
    if isinstance(t, Var):
        return ("b", env[t]) if t in env else ("v", t.name, str(t.type))
    if isinstance(t, Const):
        return ("c", t.name)
    if isinstance(t, Num):
        return ("n", t.value)
    if isinstance(t, App):
        return ("a", alpha_key(t.fun, env, depth), alpha_key(t.arg, env, depth))
    if isinstance(t, Bind):
        e2 = dict(env)
        e2[t.var] = depth
        return ("B", t.kind, str(t.var.type), alpha_key(t.body, e2, depth + 1))
    return ("o", t.op) + tuple(alpha_key(a, env, depth) for a in t.args)


# ----------------------------------------------------------------------------- printing

SYMS = {
    "unicode": dict(lam="λ", forall="∀", exists="∃", iota="ι", max="max ", card="card ",
                    not_="¬", and_=" ∧ ", or_=" ∨ ", imp=" → ", iff=" ↔ ", eq=" = ", neq=" ≠ ",
                    lt=" < ", le=" ≤ ", gt=" > ", ge=" ≥ ", top="⊤", bot="⊥", presup="∂"),
    "ascii": dict(lam="\\", forall="forall ", exists="exists ", iota="iota ", max="max ",
                  card="card ", not_="~", and_=" & ", or_=" | ", imp=" -> ", iff=" <-> ",
                  eq=" = ", neq=" != ", lt=" < ", le=" <= ", gt=" > ", ge=" >= ",
                  top="TRUE", bot="FALSE", presup="@"),
    "latex": dict(lam=r"\lambda ", forall=r"\forall ", exists=r"\exists ", iota=r"\iota ",
                  max=r"\textsc{max}\,", card=r"\textsc{card}\,", not_=r"\neg ",
                  and_=r" \wedge ", or_=r" \vee ", imp=r" \rightarrow ", iff=r" \leftrightarrow ",
                  eq=" = ", neq=r" \neq ", lt=" < ", le=r" \leq ", gt=" > ", ge=r" \geq ",
                  top=r"\top", bot=r"\bot", presup=r"\partial"),
}
PREC = {"iff": 1, "imp": 2, "or": 3, "and": 4, "not": 5, "presup": 5, **{r: 6 for r in RELATIONS}}
_KEY = {"and": "and_", "or": "or_", "not": "not_"}


def _name(n: str, style: str, const: bool = False) -> str:
    if style != "latex":
        return n
    base = n.rstrip("'")
    primes = "'" * (len(n) - len(base))
    m = re.match(r"^(.*?)(\d+)$", base)
    sub = ""
    if m and m.group(1):
        base, sub = m.group(1), "_{%s}" % m.group(2)
    base = base.replace("_", r"\_")
    if const or len(base) > 1:
        base = r"\mathit{%s}" % base
    return base + sub + primes


def show(t: Term, style: str = "unicode") -> str:
    return _show(t, style, 0)


def _wrap(s: str, p: int, ctx: int) -> str:
    return "(" + s + ")" if p < ctx else s


def _show(t: Term, st: str, ctx: int) -> str:
    S = SYMS[st]
    if isinstance(t, Var):
        return _name(t.name, st)
    if isinstance(t, Const):
        return _name(t.name, st, const=True)
    if isinstance(t, Num):
        return str(t.value)
    if isinstance(t, App):
        head, args = t, []
        while isinstance(head, App):
            args.append(head.arg)
            head = head.fun
        args.reverse()
        h = _show(head, st, 8)
        if isinstance(head, Const):                        # relations uncurried: R(a, b) ≡ R(a)(b)
            return h + "(" + ", ".join(_show(a, st, 0) for a in args) + ")"
        return h + "".join("(" + _show(a, st, 0) + ")" for a in args)
    if isinstance(t, Bind):
        v = _name(t.var.name, st)
        if t.kind == "lam":
            b = t.body
            if isinstance(b, Op) and b.op == "presup":
                s = f"{S['lam']}{v} : {_show(b.args[0], st, 0)} . {_show(b.args[1], st, 0)}"
            else:
                s = f"{S['lam']}{v}.{_show(b, st, 0)}"
            return _wrap(s, 0, ctx)
        if st == "latex" and t.kind in ("max", "card"):
            inner = r"\{%s \mid %s\}" % (v, _show(t.body, st, 0))
            return r"\textsc{max}\," + inner if t.kind == "max" else "|" + inner + "|"
        return f"{S[t.kind]}{v}[{_show(t.body, st, 0)}]"
    op, a = t.op, t.args
    if op in ("top", "bot"):
        return S[op]
    if op == "not":
        return _wrap(S["not_"] + _show(a[0], st, 5), 5, ctx)
    if op == "presup":
        return _wrap(f"{S['presup']}[{_show(a[0], st, 0)}] {_show(a[1], st, 5)}", 5, ctx)
    p = PREC[op]
    if op in ("and", "or"):
        left, right = _show(a[0], st, p), _show(a[1], st, p)
    elif op == "imp":
        left, right = _show(a[0], st, p + 1), _show(a[1], st, p)
    elif op == "iff":
        left, right = _show(a[0], st, p), _show(a[1], st, p + 1)
    else:
        left, right = _show(a[0], st, 7), _show(a[1], st, 7)
    return _wrap(left + S[_KEY.get(op, op)] + right, p, ctx)
