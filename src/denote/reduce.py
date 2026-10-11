"""Normal-order (leftmost-outermost) reduction with step traces.

Rules:  β   (λx.M)N ⇝ M[x:=N]
        ∂   (∂[φ]F)(N) ⇝ ∂[φ](F N)        F(∂[φ]N) ⇝ ∂[φ](F N)   (F not a λ; strictness)
        η   λx.(F x) ⇝ F   (x ∉ FV(F); only on request)
By Church–Rosser and strong normalisation of the simply typed calculus, β-normal forms are
unique and reached by any strategy; normal order additionally yields the textbook trace."""
from __future__ import annotations

from dataclasses import dataclass
from functools import lru_cache

from .terms import Term, App, Bind, Op, subst, fv, alpha_key


@dataclass(frozen=True)
class Step:
    rule: str
    redex: Term
    result: Term


def _presup(t):
    return isinstance(t, Op) and t.op == "presup"


def _contract(t, eta):
    if isinstance(t, App):
        f, a = t.fun, t.arg
        if isinstance(f, Bind) and f.kind == "lam":
            return "β", subst(f.body, f.var, a)
        if _presup(f):
            return "∂", Op("presup", (f.args[0], App(f.args[1], a)))
        if _presup(a) and not isinstance(f, Bind):
            return "∂", Op("presup", (a.args[0], App(f, a.args[1])))
    if (eta and isinstance(t, Bind) and t.kind == "lam" and isinstance(t.body, App)
            and t.body.arg == t.var and t.var not in fv(t.body.fun)):
        return "η", t.body.fun
    return None


def _step(t, eta):
    r = _contract(t, eta)
    if r:
        return r[0], t, r[1]
    if isinstance(t, App):
        s = _step(t.fun, eta)
        if s:
            return s[0], s[1], App(s[2], t.arg)
        s = _step(t.arg, eta)
        if s:
            return s[0], s[1], App(t.fun, s[2])
    elif isinstance(t, Bind):
        s = _step(t.body, eta)
        if s:
            return s[0], s[1], Bind(t.kind, t.var, s[2])
    elif isinstance(t, Op):
        for i, a in enumerate(t.args):
            s = _step(a, eta)
            if s:
                args = list(t.args)
                args[i] = s[2]
                return s[0], s[1], Op(t.op, tuple(args))
    return None


def normalize(t: Term, trace: list | None = None, eta: bool = False, limit: int = 10_000) -> Term:
    for _ in range(limit):
        s = _step(t, eta)
        if s is None:
            return t
        t = s[2]
        if trace is not None:
            trace.append(Step(s[0], s[1], t))
    raise RuntimeError("reduction limit exceeded")


@lru_cache(maxsize=100_000)
def nf(t: Term) -> Term:
    return normalize(t)


@lru_cache(maxsize=100_000)
def canonical(t: Term):
    """α-invariant key of the βη-normal form."""
    return alpha_key(normalize(t, eta=True))
