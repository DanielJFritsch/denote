"""Unification-based type inference for Λ (first-order unification over simple types,
in the manner of Hindley 1969 / Milner 1978, without let-polymorphism)."""
from __future__ import annotations

from .typesys import (Fun, TVar, E, T, S, V, D, ET, unify, resolve, fresh_tvar, defaultable,
                      tvars, final, TypeClash)
from .terms import Var, Const, Num, App, Bind, Op, walk


class SemTypeError(Exception):
    pass


_CONVENTIONS = {"x": E, "y": E, "z": E, "u": E, "P": ET, "Q": ET, "R": Fun(E, ET),
                "p": Fun(S, T), "q": Fun(S, T), "w": S, "e": V, "d": D}


def default_for(name: str):
    base = name.rstrip("'").rstrip("0123456789") or name
    return _CONVENTIONS.get(base)


def _u(a, b, sub, where):
    try:
        unify(a, b, sub)
    except TypeClash as ex:
        raise SemTypeError(f"type clash in {where!r}: {resolve(a, sub)} vs {resolve(b, sub)}") from ex


def infer(t, sub: dict):
    if isinstance(t, (Var, Const)):
        return t.type
    if isinstance(t, Num):
        return D
    if isinstance(t, App):
        f, a, r = infer(t.fun, sub), infer(t.arg, sub), fresh_tvar()
        try:
            unify(f, Fun(a, r), sub)
        except TypeClash as ex:
            raise SemTypeError(f"cannot apply {t.fun!r} : {resolve(f, sub)} "
                               f"to {t.arg!r} : {resolve(a, sub)}") from ex
        return r
    if isinstance(t, Bind):
        b = infer(t.body, sub)
        if t.kind == "lam":
            return Fun(t.var.type, b)
        _u(b, T, sub, t)
        if t.kind == "iota":
            return t.var.type
        if t.kind == "max":
            _u(t.var.type, D, sub, t)
        return D if t.kind in ("max", "card") else T
    if t.op in ("top", "bot"):
        return T
    if t.op == "presup":
        _u(infer(t.args[0], sub), T, sub, t)
        return infer(t.args[1], sub)
    if t.op in ("eq", "neq"):
        _u(infer(t.args[0], sub), infer(t.args[1], sub), sub, t)
        return T
    target = D if t.op in ("lt", "le", "gt", "ge") else T
    for a in t.args:
        _u(infer(a, sub), target, sub, t)
    return T


def retype(t, sub: dict):
    """Rebuild t with every type annotation resolved under sub."""
    if isinstance(t, Var):
        return Var(t.name, resolve(t.type, sub))
    if isinstance(t, Const):
        return Const(t.name, resolve(t.type, sub))
    if isinstance(t, Num):
        return t
    if isinstance(t, App):
        return App(retype(t.fun, sub), retype(t.arg, sub))
    if isinstance(t, Bind):
        return Bind(t.kind, retype(t.var, sub), retype(t.body, sub))
    return Op(t.op, tuple(retype(a, sub) for a in t.args))


def _typed_things(t):
    for s in walk(t):
        if isinstance(s, (Var, Const)):
            yield s
        elif isinstance(s, Bind):
            yield s.var


def apply_defaults(terms, sub: dict, consts=()):
    """Resolve residual inference variables: first by the variable-naming conventions of
    the semantics literature (x:e, P:<e,t>, p:<s,t>, w:s, e:v, d:d, …), then by making
    constants' final result type t, then e everywhere else."""
    for t in terms:
        for s in walk(t):
            if isinstance(s, Bind):
                d = default_for(s.var.name)
                rt = resolve(s.var.type, sub)
                if d is not None and any(defaultable(v) for v in tvars(rt)):
                    trial = dict(sub)                    # commit only a successful unification
                    try:
                        unify(rt, d, trial)
                    except TypeClash:
                        continue
                    sub.update(trial)
    for c in consts:
        rt = resolve(c.type, sub)
        f = final(rt)
        if isinstance(rt, Fun) and isinstance(f, TVar) and defaultable(f):
            unify(f, T, sub)
    for t in list(terms) + list(consts):
        for s in _typed_things(t):
            for v in tvars(resolve(s.type, sub)):
                if defaultable(v):
                    sub[v.name] = E


def freshen_named(ty, tag):
    """Rename declared type variables ('a) apart per lexical entry."""
    if isinstance(ty, TVar) and not defaultable(ty):
        return TVar(f"{ty.name.split('#')[0]}#{tag}")
    if isinstance(ty, Fun):
        return Fun(freshen_named(ty.arg, tag), freshen_named(ty.res, tag))
    return ty


def typecheck(t, expected=None, sub: dict | None = None, defaults: bool = True):
    sub = {} if sub is None else sub
    ty = infer(t, sub)
    if expected is not None:
        _u(ty, expected, sub, t)
    if defaults:
        apply_defaults([t], sub, [s for s in walk(t) if isinstance(s, Const)])
    return retype(t, sub)
