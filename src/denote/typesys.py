"""Simple type theory over the basic types e, t, s, v, i, d (Church 1940; Gallin 1975)."""
from __future__ import annotations

import itertools
import re
from dataclasses import dataclass

BASIC_NAMES = {
    "e": "entities", "t": "truth values", "s": "possible worlds",
    "v": "eventualities", "i": "times", "d": "degrees",
}


class Type:
    __slots__ = ()

    def __repr__(self):
        return str(self)


@dataclass(frozen=True, repr=False)
class Basic(Type):
    name: str

    def __str__(self):
        return self.name


@dataclass(frozen=True, repr=False)
class Fun(Type):
    arg: Type
    res: Type

    def __str__(self):
        return f"<{self.arg},{self.res}>"


@dataclass(frozen=True, repr=False)
class TVar(Type):
    name: str

    def __str__(self):
        return "'" + self.name.split("#")[0]


E, T, S, V, I, D = (Basic(n) for n in "etsvid")
ET = Fun(E, T)
GQ = Fun(ET, T)

_fresh = itertools.count()


def fresh_tvar() -> TVar:
    return TVar(f"τ{next(_fresh)}")


def defaultable(tv: TVar) -> bool:
    """Fresh inference variables and constant-type placeholders may be defaulted;
    named type variables from declarations ('a) are genuinely polymorphic."""
    return tv.name.startswith(("τ", "κ:"))


class TypeClash(Exception):
    pass


def parse_type(src: str) -> Type:
    s = re.sub(r"\s+", "", src)
    pos = 0

    def p() -> Type:
        nonlocal pos
        if pos >= len(s):
            raise ValueError(f"unexpected end of type {src!r}")
        c = s[pos]
        if c == "<":
            pos += 1
            a = p()
            if s[pos:pos + 1] != ",":
                raise ValueError(f"expected ',' at {pos} in type {src!r}")
            pos += 1
            b = p()
            if s[pos:pos + 1] != ">":
                raise ValueError(f"expected '>' at {pos} in type {src!r}")
            pos += 1
            return Fun(a, b)
        if c == "'":
            m = re.match(r"'([A-Za-z]\w*)", s[pos:])
            if not m:
                raise ValueError(f"bad type variable in {src!r}")
            pos += m.end()
            return TVar(m.group(1))
        if c in BASIC_NAMES:
            pos += 1
            return Basic(c)
        raise ValueError(f"unknown type symbol {c!r} in {src!r}")

    t = p()
    if pos != len(s):
        raise ValueError(f"trailing material in type {src!r}")
    return t


def order(t: Type) -> int:
    """Functional order: basic types 0; ord(<a,b>) = max(ord(a)+1, ord(b))."""
    return max(order(t.arg) + 1, order(t.res)) if isinstance(t, Fun) else 0


def final(t: Type) -> Type:
    while isinstance(t, Fun):
        t = t.res
    return t


def arg_types(t: Type) -> list:
    out = []
    while isinstance(t, Fun):
        out.append(t.arg)
        t = t.res
    return out


def conjoinable(t: Type) -> bool:
    """Partee & Rooth (1983): t, and <a,b> for conjoinable b."""
    return final(t) == T


def tvars(t: Type) -> set:
    if isinstance(t, TVar):
        return {t}
    if isinstance(t, Fun):
        return tvars(t.arg) | tvars(t.res)
    return set()


def resolve(t: Type, sub: dict) -> Type:
    while isinstance(t, TVar) and t.name in sub:
        t = sub[t.name]
    if isinstance(t, Fun):
        return Fun(resolve(t.arg, sub), resolve(t.res, sub))
    return t


def _occurs(v: TVar, t: Type, sub: dict) -> bool:
    t = resolve(t, sub)
    return t == v or (isinstance(t, Fun) and (_occurs(v, t.arg, sub) or _occurs(v, t.res, sub)))


def unify(a: Type, b: Type, sub: dict) -> None:
    a, b = resolve(a, sub), resolve(b, sub)
    if a == b:
        return
    if isinstance(a, TVar):
        if _occurs(a, b, sub):
            raise TypeClash(f"occurs check: {a} in {b}")
        sub[a.name] = b
    elif isinstance(b, TVar):
        unify(b, a, sub)
    elif isinstance(a, Fun) and isinstance(b, Fun):
        unify(a.arg, b.arg, sub)
        unify(a.res, b.res, sub)
    else:
        raise TypeClash(f"cannot unify {a} with {b}")


def type_str(t: Type, style: str = "unicode") -> str:
    if isinstance(t, Fun):
        a, b = type_str(t.arg, style), type_str(t.res, style)
        if style == "latex":
            return rf"\langle {a},{b}\rangle"
        return f"⟨{a},{b}⟩" if style == "unicode" else f"<{a},{b}>"
    if isinstance(t, TVar):
        base = t.name.split("#")[0]
        return rf"\alpha_{{{base}}}" if style == "latex" else "'" + base
    return t.name
