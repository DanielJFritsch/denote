"""Model-theoretic statistics over a set of readings ρ₁…ρ_k.

  scope sensitivity    Δ = μ{M : ∃i,j ⟦ρᵢ⟧^M ≠ ⟦ρⱼ⟧^M}
  disagreement metric  δ(ρᵢ,ρⱼ) = μ{M : ⟦ρᵢ⟧^M ≠ ⟦ρⱼ⟧^M}   (a pseudometric; δ = 0 on model-equivalence)
  profile entropy      H = −Σ_v μ(v) log₂ μ(v) over joint truth-value vectors v
  entailment preorder  ρᵢ ⊑ ρⱼ iff no sampled M has ⟦ρᵢ⟧^M = 1 ≠ ⟦ρⱼ⟧^M, reduced to a Hasse diagram
Statistics are relative to the sample (sizes, θ); exhaustive small models make ⊑ a bounded proof."""
from __future__ import annotations

import math
from collections import Counter
from dataclasses import dataclass

from ..terms import constants
from ..models import Evaluator, model_sample


@dataclass
class AmbiguityReport:
    k: int
    n_models: int
    classes: list            # list of lists of reading indices (model-equivalence classes)
    sensitivity: float
    entropy: float
    delta: list              # k×k matrix
    entails: list            # k×k booleans
    hasse: list              # edges (i, j): ρ_i ⊏ ρ_j immediately (i stronger)
    p_true: list
    weakest: list
    strongest: list


def signature_of(terms):
    sig = {}
    for t in terms:
        constants(t, sig)
    return sig


def analyse(terms, scheme="strong", sizes=(1, 2, 3, 4), samples=600, theta=0.5, seed=0):
    sig = signature_of(terms)
    models = model_sample(sig, sizes, samples, theta, seed)
    rows = []
    for M in models:
        E = Evaluator(M, scheme)
        rows.append(tuple(E(t) for t in terms))
    k, N = len(terms), len(rows)
    cols = list(zip(*rows)) if rows else [()] * k
    classes, seen = [], {}
    for i, c in enumerate(cols):
        seen.setdefault(c, []).append(i)
    classes = list(seen.values())
    sensitivity = sum(len(set(r)) > 1 for r in rows) / N if N else 0.0
    counts = Counter(rows)
    entropy = -sum(c / N * math.log2(c / N) for c in counts.values()) if N else 0.0
    delta = [[sum(r[i] != r[j] for r in rows) / N for j in range(k)] for i in range(k)]
    ent = [[all(not (r[i] is True and r[j] is not True) for r in rows) for j in range(k)] for i in range(k)]
    # Hasse diagram over class representatives (strict order modulo equivalence)
    reps = [c[0] for c in classes]
    strict = {(i, j) for i in reps for j in reps if i != j and ent[i][j] and not ent[j][i]}
    hasse = [(i, j) for (i, j) in strict
             if not any((i, m) in strict and (m, j) in strict for m in reps)]
    p_true = [sum(r[i] is True for r in rows) / N for i in range(k)]
    weakest = [i for i in reps if not any((i, j) in strict for j in reps)]
    strongest = [j for j in reps if not any((i, j) in strict for i in reps)]
    return AmbiguityReport(k, N, classes, sensitivity, entropy, delta, ent, sorted(hasse), p_true,
                           weakest, strongest)


def to_dot(terms, report, show_fn, names=None):
    names = names or [f"ρ{i + 1}" for i in range(len(terms))]
    lines = ["digraph entailment {", '  rankdir=BT; node [shape=box, fontname="Helvetica"];']
    for c in report.classes:
        label = " ≡ ".join(names[i] for i in c) + "\\n" + show_fn(terms[c[0]]).replace('"', "'")
        lines.append(f'  n{c[0]} [label="{label}"];')
    for i, j in report.hasse:
        lines.append(f"  n{i} -> n{j};   // {names[i]} ⊨ {names[j]}")
    lines.append("}")
    return "\n".join(lines)
