"""Export first-order readings to TPTP FOF (Sutcliffe 2009) and SMT-LIB 2 (Barrett et al.).
Definite descriptions are first eliminated by the Russellian half of the bilateral translation;
curried atoms R(a)(b) are uncurried in application order R(a, b)."""
from __future__ import annotations

from .typesys import Basic, T, D, arg_types, final
from .terms import Var, Const, Num, App, Bind, Op, constants
from .projection import TF, has_partiality


class ExportError(Exception):
    pass


def _first_order(phi):
    return TF(phi, "strong")[0] if has_partiality(phi) else phi


def _uncurry(t):
    args = []
    while isinstance(t, App):
        args.append(t.arg)
        t = t.fun
    return t, list(reversed(args))


def _tptp(t, env):
    if isinstance(t, Var):
        return env.get(t, t.name.replace("'", "p"))
    if isinstance(t, Const):
        return t.name.lower()
    if isinstance(t, Num):
        raise ExportError("numeric terms require TFF/arithmetic; not supported in FOF")
    if isinstance(t, App):
        h, args = _uncurry(t)
        if not isinstance(h, Const):
            raise ExportError("higher-order application cannot be exported to FOF")
        return f"{_tptp(h, env)}({', '.join(_tptp(a, env) for a in args)})"
    if isinstance(t, Bind):
        if t.kind not in ("forall", "exists"):
            raise ExportError(f"binder {t.kind} has no FOF counterpart")
        V = "X" + str(len(env))
        env2 = {**env, t.var: V}
        q = "!" if t.kind == "forall" else "?"
        return f"{q}[{V}]: ({_tptp(t.body, env2)})"
    a = [(_tptp(x, env)) for x in t.args]
    ops = {"and": "&", "or": "|", "imp": "=>", "iff": "<=>", "eq": "=", "neq": "!="}
    if t.op == "not":
        return f"~ ({a[0]})"
    if t.op == "top":
        return "$true"
    if t.op == "bot":
        return "$false"
    if t.op in ops:
        return f"({a[0]} {ops[t.op]} {a[1]})"
    raise ExportError(f"operator {t.op} has no FOF counterpart")


def to_tptp(premises, hypothesis=None):
    lines = [f"fof(p{i + 1}, axiom, {_tptp(_first_order(p), {})})." for i, p in enumerate(premises)]
    if hypothesis is not None:
        lines.append(f"fof(h, conjecture, {_tptp(_first_order(hypothesis), {})}).")
    return "\n".join(lines)


_SORT = {"e": "E", "s": "W", "v": "Ev", "i": "Tm"}


def _sort(b):
    if b == T:
        return "Bool"
    if b == D:
        return "Int"
    return _SORT.get(b.name, b.name.upper())


def _smt(t, env):
    if isinstance(t, Var):
        return env.get(t, t.name.replace("'", "_p"))
    if isinstance(t, Const):
        return t.name
    if isinstance(t, Num):
        return str(t.value)
    if isinstance(t, App):
        h, args = _uncurry(t)
        if not isinstance(h, Const):
            raise ExportError("higher-order application cannot be exported")
        return f"({h.name} {' '.join(_smt(a, env) for a in args)})"
    if isinstance(t, Bind):
        if t.kind not in ("forall", "exists"):
            raise ExportError(f"binder {t.kind} not supported")
        V = f"v{len(env)}"
        return f"({t.kind} (({V} {_sort(t.var.type)})) {_smt(t.body, {**env, t.var: V})})"
    a = [_smt(x, env) for x in t.args]
    ops = {"and": "and", "or": "or", "imp": "=>", "iff": "=", "eq": "=", "lt": "<", "le": "<=", "gt": ">", "ge": ">="}
    if t.op == "not":
        return f"(not {a[0]})"
    if t.op == "neq":
        return f"(not (= {a[0]} {a[1]}))"
    if t.op in ("top", "bot"):
        return "true" if t.op == "top" else "false"
    return f"({ops[t.op]} {a[0]} {a[1]})"


def to_smtlib(premises, hypothesis=None):
    forms = [_first_order(p) for p in premises] + ([_first_order(hypothesis)] if hypothesis is not None else [])
    sig = {}
    for f in forms:
        constants(f, sig)
    sorts = {_sort(b) for ty in sig.values() for b in arg_types(ty) + [final(ty)] if isinstance(b, Basic)}
    lines = ["(set-logic ALL)"] + [f"(declare-sort {s} 0)" for s in sorted(sorts - {"Bool", "Int"})]
    for c, ty in sorted(sig.items()):
        lines.append(f"(declare-fun {c} ({' '.join(_sort(a) for a in arg_types(ty))}) {_sort(final(ty))})")
    lines += [f"(assert {_smt(f, {})})" for f in forms[: len(premises)]]
    if hypothesis is not None:
        lines.append(f"(assert (not {_smt(forms[-1], {})}))   ; unsat ⇔ premises ⊨ hypothesis")
    lines.append("(check-sat)")
    return "\n".join(lines)
