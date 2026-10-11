"""Presupposition projection by bilateral translation.

Every formula φ of the trivalent logic is mapped to two bivalent formulas T(φ) ('φ is true')
and F(φ) ('φ is false'); the presupposition is π(φ) = T(φ) ∨ F(φ) and the assertion T(φ).
Partial terms are eliminated inside atoms: ι by Russell's expansion, max by its maximality
clause, ∂ by conjunction — so the Frege–Strawson definedness condition and the Russellian
truth condition fall out as the two halves of one translation. The clauses mirror
models.Evaluator exactly for each scheme (weak = Bochvar, strong = Kleene, middle = Peters)."""
from __future__ import annotations

from .typesys import T
from .terms import Var, Const, Num, App, Bind, Op, TOP, BOT, neg, conj, disj, exists, forall, fv, \
    replace_sub, alpha_key, fresh, walk, Term
from .reduce import normalize


def _c(*xs):
    out = TOP
    for x in xs:
        out = x if out == TOP else conj(out, x)
    return out


def _d(*xs):
    out = BOT
    for x in xs:
        out = x if out == BOT else disj(out, x)
    return out


def _partial_sub(t, bound=frozenset()):
    """Leftmost partial subterm (ι, max, ∂ of non-t type) not under a local binder."""
    if isinstance(t, Bind):
        if t.kind in ("iota", "max") and not (fv(t) & bound):
            return t
        return None
    if isinstance(t, Op) and t.op == "presup":
        return t
    if isinstance(t, App):
        return _partial_sub(t.fun, bound) or _partial_sub(t.arg, bound)
    if isinstance(t, Op):
        for a in t.args:
            r = _partial_sub(a, bound)
            if r is not None:
                return r
    return None


def _total_cards(t, sch):
    """card x[φ] counts T(φ)-instances: replace bodies accordingly."""
    if isinstance(t, Bind):
        if t.kind == "card":
            return Bind("card", t.var, TF(t.body, sch)[0])
        return t
    if isinstance(t, App):
        return App(_total_cards(t.fun, sch), _total_cards(t.arg, sch))
    if isinstance(t, Op):
        return Op(t.op, tuple(_total_cards(a, sch) for a in t.args))
    return t


def _atom(A, sch):
    p = _partial_sub(A)
    if p is None:
        A = _total_cards(A, sch)
        return A, neg(A)
    if isinstance(p, Op):                                   # ∂[c] M inside an atom
        tc = TF(p.args[0], sch)[0]
        t_, f_ = _atom(replace_sub(A, p, p.args[1]), sch)
        return _c(tc, t_), _c(tc, f_)
    z = fresh("z", p.var.type, A)
    body_z = normalize(App(Bind("lam", p.var, p.body), z))
    y = fresh("y", p.var.type, A, z)
    body_y = normalize(App(Bind("lam", p.var, p.body), y))
    if p.kind == "iota":                                    # Russell (1905)
        unique = forall(y, Op("imp", (TF(body_y, sch)[0], Op("eq", (y, z)))))
    else:                                                   # maximality
        unique = forall(y, Op("imp", (TF(body_y, sch)[0], Op("le", (y, z)))))
    core = _c(TF(body_z, sch)[0], unique)
    t_, f_ = _atom(replace_sub(A, p, z), sch)
    return exists(z, _c(core, t_)), exists(z, _c(core, f_))


def TF(phi: Term, sch: str = "strong"):
    """(T(φ), F(φ)) for a formula φ of type t (β-normal)."""
    if isinstance(phi, Op):
        op, a = phi.op, phi.args
        if op == "top":
            return TOP, BOT
        if op == "bot":
            return BOT, TOP
        if op == "not":
            t_, f_ = TF(a[0], sch)
            return f_, t_
        if op == "presup":
            tc = TF(a[0], sch)[0]
            t_, f_ = TF(a[1], sch)
            return _c(tc, t_), _c(tc, f_)
        if op in ("and", "or", "imp", "iff"):
            (ta, fa), (tb, fb) = TF(a[0], sch), TF(a[1], sch)
            da, db = _d(ta, fa), _d(tb, fb)
            if op == "iff":
                return _d(_c(ta, tb), _c(fa, fb)), _d(_c(ta, fb), _c(fa, tb))
            if op == "imp":                                  # φ → ψ  ≡  ¬φ ∨ ψ
                ta, fa = fa, ta
                op = "or"
            if op == "and":
                if sch == "weak":
                    return _c(ta, tb), _c(da, db, neg(_c(ta, tb)))
                if sch == "strong":
                    return _c(ta, tb), _d(fa, fb)
                return _c(ta, tb), _d(fa, _c(ta, fb))
            if sch == "weak":
                return _c(da, db, _d(ta, tb)), _c(fa, fb)
            if sch == "strong":
                return _d(ta, tb), _c(fa, fb)
            return _d(ta, _c(fa, tb)), _c(fa, fb)
        return _atom(phi, sch)
    if isinstance(phi, Bind) and phi.kind in ("forall", "exists"):
        t_, f_ = TF(phi.body, sch)
        d_ = _d(t_, f_)
        v = phi.var
        if phi.kind == "forall":
            if sch == "weak":
                return forall(v, t_), _c(forall(v, d_), exists(v, f_))
            return forall(v, t_), exists(v, f_)
        if sch == "weak":
            return _c(forall(v, d_), exists(v, t_)), forall(v, f_)
        return exists(v, t_), forall(v, f_)
    return _atom(phi, sch)


# ---------------------------------------------------------------------------- simplification

def nnf(t: Term, positive: bool = True) -> Term:
    """Negation normal form (quantifier and De Morgan duality)."""
    if isinstance(t, Op) and t.op == "not":
        return nnf(t.args[0], not positive)
    if isinstance(t, Op) and t.op in ("and", "or"):
        op = t.op if positive else ("or" if t.op == "and" else "and")
        return Op(op, (nnf(t.args[0], positive), nnf(t.args[1], positive)))
    if isinstance(t, Op) and t.op in ("top", "bot"):
        return t if positive else (BOT if t == TOP else TOP)
    if isinstance(t, Bind) and t.kind in ("forall", "exists"):
        kind = t.kind if positive else ("exists" if t.kind == "forall" else "forall")
        return Bind(kind, t.var, nnf(t.body, positive))
    return t if positive else neg(t)


def _neg_of(a, b):
    return alpha_key(nnf(a)) == alpha_key(nnf(b, False))


def _flat(t, op):
    if isinstance(t, Op) and t.op == op:
        return _flat(t.args[0], op) + _flat(t.args[1], op)
    return [t]


def simplify(t: Term) -> Term:
    """Truth-preserving clean-up (bivalent): units, double negation, idempotence,
    complementation, absorption (A ∨ (¬A ∧ X) ⇒ A ∨ X), vacuous quantification
    (domains are non-empty), and ∃-factoring ∃x[C ∧ L] ∨ ∃x[C ∧ ¬L] ⇒ ∃x[C]."""
    for _ in range(12):
        new = _simp(t)
        if alpha_key(new) == alpha_key(t):
            return new
        t = new
    return t


def _simp(t):
    if isinstance(t, Bind):
        b = _simp(t.body)
        if t.kind in ("forall", "exists"):
            if t.var not in fv(b):
                return b
        return Bind(t.kind, t.var, b)
    if isinstance(t, App):
        return App(_simp(t.fun), _simp(t.arg))
    if not isinstance(t, Op):
        return t
    if t.op == "not":
        a = _simp(t.args[0])
        if a == TOP:
            return BOT
        if a == BOT:
            return TOP
        if isinstance(a, Op) and a.op == "not":
            return a.args[0]
        return neg(a)
    if t.op in ("and", "or"):
        unit, zero = (TOP, BOT) if t.op == "and" else (BOT, TOP)
        items, keys = [], set()
        for x in _flat(t, t.op):
            x = _simp(x)
            for y in (_flat(x, t.op) if isinstance(x, Op) and x.op == t.op else [x]):
                if y == zero:
                    return zero
                k = alpha_key(y)
                if y != unit and k not in keys:
                    keys.add(k)
                    items.append(y)
        if any(_neg_of(a, b) for i, a in enumerate(items) for b in items[i + 1:]):
            return zero
        dual = "or" if t.op == "and" else "and"
        items = _absorb(items, dual)
        if t.op == "or":
            items = _factor(items)
        out = unit
        for x in items:
            out = x if out == unit else Op(t.op, (out, x))
        return out
    return Op(t.op, tuple(_simp(a) for a in t.args))


def _absorb(items, dual):
    lits = [x for x in items if not (isinstance(x, Op) and x.op == dual)]
    out = []
    for x in items:
        if isinstance(x, Op) and x.op == dual:
            parts = [p for p in _flat(x, dual) if not any(_neg_of(p, l) for l in lits)]
            if any(alpha_key(p) == alpha_key(l) for p in parts for l in lits):
                continue                                     # A ∨ (A ∧ X) ⇒ A
            if not parts:
                parts = [TOP if dual == "and" else BOT]
            y = parts[0]
            for p in parts[1:]:
                y = Op(dual, (y, p))
            out.append(y)
        else:
            out.append(x)
    return out


def _factor(items):
    def split(x):
        if isinstance(x, Bind) and x.kind == "exists":
            return x.var, _flat(x.body, "and")
        return None, _flat(x, "and")
    changed = True
    while changed:
        changed = False
        for i in range(len(items)):
            for j in range(i + 1, len(items)):
                vi, ci = split(items[i])
                vj, cj = split(items[j])
                if (vi is None) != (vj is None) or len(ci) != len(cj) or len(ci) < 2:
                    continue
                if vi is not None:
                    if vi.type != vj.type:
                        continue
                    cj = [normalize(App(Bind("lam", vj, c), vi)) for c in cj]
                ki = [alpha_key(c) for c in ci]
                kj = [alpha_key(c) for c in cj]
                common = [c for c, k in zip(ci, ki) if k in kj]
                rest_i = [c for c, k in zip(ci, ki) if k not in kj]
                rest_j = [c for c, k in zip(cj, kj) if k not in ki]
                if len(rest_i) == 1 == len(rest_j) and _neg_of(rest_i[0], rest_j[0]) and common:
                    body = _c(*common)
                    items[i] = exists(vi, body) if vi is not None else body
                    del items[j]
                    changed = True
                    break
            if changed:
                break
    return items


def _def_weak(phi):
    """Bochvar definedness: every subformula must be defined (D(φ∘ψ) = D(φ) ∧ D(ψ), D(∀xφ) = ∀x D(φ))."""
    if isinstance(phi, Op):
        if phi.op in ("top", "bot"):
            return TOP
        if phi.op == "not":
            return _def_weak(phi.args[0])
        if phi.op == "presup":
            return _c(TF(phi.args[0], "weak")[0], _def_weak(phi.args[1]))
        if phi.op in ("and", "or", "imp", "iff"):
            return _c(_def_weak(phi.args[0]), _def_weak(phi.args[1]))
    if isinstance(phi, Bind) and phi.kind in ("forall", "exists"):
        return forall(phi.var, _def_weak(phi.body))
    t_, f_ = _atom(phi, "weak")
    return _d(t_, f_)


def project(phi: Term, sch: str = "strong"):
    """(assertion, presupposition) of a closed formula under a projection scheme."""
    t_, f_ = TF(phi, sch)
    pi = _def_weak(phi) if sch == "weak" else _d(t_, f_)
    return simplify(t_), simplify(pi)


def has_partiality(phi: Term) -> bool:
    return any((isinstance(s, Bind) and s.kind in ("iota", "max")) or (isinstance(s, Op) and s.op == "presup")
               for s in walk(phi))
