"""Derivational complexity, semantic informativity, and corpus coverage."""
from __future__ import annotations

import math
from collections import Counter

from ..typesys import order, type_str
from ..terms import Bind, Op, size, walk, ALPHA
from ..models import Evaluator, model_sample, random_model
from .ambiguity import signature_of


def complexity(deriv) -> dict:
    """A vector-valued profile of a derivation (not a single 'difficulty' score)."""
    nodes = list(deriv.walk())
    steps = [s for d in nodes for s in d.steps]

    def qdepth(t):
        if isinstance(t, Bind):
            return qdepth(t.body) + (t.kind in ("forall", "exists", "iota", "max", "card"))
        if isinstance(t, Op):
            return max((qdepth(a) for a in t.args), default=0)
        if hasattr(t, "fun"):
            return max(qdepth(t.fun), qdepth(t.arg))
        return 0

    return {
        "nodes": len(nodes),
        "β-steps": sum(s.rule == "β" for s in steps),
        "∂-steps": sum(s.rule == "∂" for s in steps),
        "type-shifts": len(deriv.shifts),
        "max type order": max(order(d.type) for d in nodes if d.type is not None),
        "max redex size": max((size(d.raw) for d in nodes if d.raw is not None), default=0),
        "normal-form size": size(deriv.term),
        "quantifier depth": qdepth(deriv.term),
        "rules": dict(Counter(d.rule for d in nodes)),
    }


def informativity(term, scheme="strong", sizes=(1, 2, 3, 4), samples=800, theta=0.5, seed=0):
    """Bar-Hillel & Carnap (1952): inf(φ) = −log₂ m(φ), cont(φ) = 1 − m(φ), with the logical
    measure m estimated by μ_{n,θ}; also the definedness rate for partial meanings."""
    models = model_sample(signature_of([term]), sizes, samples, theta, seed)
    vals = [Evaluator(M, scheme)(term) for M in models]
    N = len(vals)
    p = sum(v is True for v in vals) / N
    defined = sum(v is not None for v in vals) / N
    return {"models": N, "m(φ)": p, "inf(φ) bits": (-math.log2(p) if p > 0 else math.inf),
            "cont(φ)": 1 - p, "P(defined)": defined}


def finite_size_profile(term, ns=(1, 2, 3, 4, 5, 6, 8), samples=300, theta=0.5, seed=0, scheme="strong"):
    """m(φ) as a function of domain size: under the first-order 0–1 law (Glebskii et al. 1969;
    Fagin 1976) relational sentences tend to probability 0 or 1, so every measure here is
    a finite-size statistic and is reported as such."""
    import random
    rng, sig, out = random.Random(seed), signature_of([term]), []
    for n in ns:
        vals = [Evaluator(random_model(sig, n, theta, rng), scheme)(term) for _ in range(samples)]
        out.append((n, sum(v is True for v in vals) / samples))
    return out


def coverage(items, make_interpreter):
    """items: [(id, tree)]. Returns per-item status plus aggregate failure statistics."""
    results, gaps, mismatches, by_label = [], Counter(), Counter(), Counter()
    for ident, tree in items:
        I = make_interpreter()
        ds = I.interpret(tree)
        ok = bool(ds)
        if not ok:
            for f in I.failures:
                if f.kind == "lexical gap":
                    gaps[f.detail.split("'")[1]] += 1
                elif f.kind == "type mismatch":
                    mismatches[" + ".join(type_str(t) for t in f.types)] += 1
                    by_label[f.node.label] += 1
        results.append((ident, ok, len(ds), I.failures if not ok else []))
    n = len(results)
    return {"items": n, "covered": sum(r[1] for r in results), "rate": (sum(r[1] for r in results) / n) if n else 0,
            "results": results, "lexical gaps": gaps, "type mismatches": mismatches, "failing labels": by_label}
