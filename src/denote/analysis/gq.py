"""Generalized-quantifier theory by exhaustive model enumeration.

For a determiner denotation Q : ⟨⟨e,t⟩,⟨⟨e,t⟩,t⟩⟩ we test, over all A, B ⊆ D with |D| ≤ n:
  CONS  Q(A)(B) ⇔ Q(A)(A∩B)                      (Barwise & Cooper 1981; Keenan & Stavi 1986)
  EXT   Q_D(A)(B) ⇔ Q_D′(A)(B) for D ⊆ D′        (van Benthem 1984)
  QUANT Q is invariant under permutations of D   (isomorphism closure; Mostowski 1957)
  ↑MON / MON↓, ↑MON / ↓MON on scope and restrictor, SYM, INT (intersectivity), triviality
plus a graded monotonicity index and van Benthem's number-triangle representation."""
from __future__ import annotations

import itertools
import random

from ..typesys import Fun, ET, GQ, T, final, arg_types
from ..terms import App, Var, Bind, Op, constants, lam
from ..models import Model, Evaluator, _pred, random_model, ModelError

DET = Fun(ET, GQ)


def _subsets(D):
    return [frozenset(c) for r in range(len(D) + 1) for c in itertools.combinations(D, r)]


def _charf(A):
    return _pred(1, {(x,) for x in A})


def determiner_table(term, n, model_extra=None):
    """{(A, B): truth} for all A, B ⊆ D, |D| = n (entities 0..n-1)."""
    D = list(range(n))
    M = Model({"e": D}, model_extra or {}, name=f"D{n}")
    q = Evaluator(M, "strong")(term)
    subs = _subsets(D)
    return D, {(A, B): _app2(q, A, B) for A in subs for B in subs}


def _app2(q, A, B):
    """Q(A)(B), propagating undefinedness (#) from a presuppositional restrictor."""
    qa = q(_charf(A))
    return None if qa is None else qa(_charf(B))


def universals(term, max_n=4):
    if constants(term):
        raise ModelError("determiner contains non-logical constants; GQ universals presuppose a logical determiner")
    tables = {n: determiner_table(term, n) for n in range(1, max_n + 1)}
    props = {k: True for k in ("CONS", "EXT", "QUANT", "↑MON", "MON↓", "↑mon (restrictor)",
                                "↓mon (restrictor)", "SYM", "INT")}
    viol = {k: None for k in props}
    graded = {"↑MON": [0, 0], "MON↓": [0, 0]}
    values = set()

    def fail(k, witness):
        if props[k]:
            props[k], viol[k] = False, witness

    for n, (D, tab) in tables.items():
        U = frozenset(D)
        for (A, B), v in tab.items():
            values.add(v)
            if tab[(A, A & B)] != v:
                fail("CONS", (n, A, B))
            if tab[(B, A)] != v:
                fail("SYM", (n, A, B))
            for x in U - B:
                w = tab[(A, B | {x})]
                graded["↑MON"][1] += v is True
                graded["↑MON"][0] += v is True and w is not True
                if v is True and w is not True:
                    fail("↑MON", (n, A, B, x))
                graded["MON↓"][1] += w is True
                graded["MON↓"][0] += w is True and v is not True
                if w is True and v is not True:
                    fail("MON↓", (n, A, B, x))
            for x in U - A:
                w = tab[(A | {x}, B)]
                if v is True and w is not True:
                    fail("↑mon (restrictor)", (n, A, B, x))
                if w is True and v is not True:
                    fail("↓mon (restrictor)", (n, A, B, x))
        by_inter = {}
        for (A, B), v in tab.items():
            if by_inter.setdefault(A & B, v) != v:
                fail("INT", (n, A, B))
        for perm in itertools.permutations(D):
            pm = dict(zip(D, perm))
            for (A, B), v in tab.items():
                if tab[(frozenset(pm[x] for x in A), frozenset(pm[x] for x in B))] != v:
                    fail("QUANT", (n, A, B, perm))
                    break
            if not props["QUANT"]:
                break
        if n < max_n:
            _, big = tables[n + 1]
            for (A, B), v in tab.items():
                if big[(A, B)] != v:
                    fail("EXT", (n, A, B))
    props["non-trivial"] = len(values) > 1
    graded_idx = {k: (1 - a / b if b else 1.0) for k, (a, b) in graded.items()}
    return props, viol, graded_idx


def number_triangle(term, max_n=6):
    """van Benthem's tree of numbers: row n = |A|; position k = |A∩B| (requires CONS+EXT+QUANT)."""
    rows = []
    for size in range(max_n + 1):
        D = list(range(size))
        M = Model({"e": D or [0]}, {}, name="tri")
        q = Evaluator(M, "strong")(term)
        A = frozenset(D)
        row = []
        for k in range(size + 1):
            v = _app2(q, A, frozenset(D[:k]))
            row.append("+" if v is True else ("−" if v is False else "#"))
        rows.append(row)
    width = 2 * max_n + 1
    lines = []
    for size, row in enumerate(rows):
        lines.append(f"|A|={size}  " + " " * (max_n - size) + " ".join(row))
    lines.append(" " * 8 + "(left: |A∩B| = 0 … right: |A∩B| = |A|)")
    return "\n".join(lines)


def position_polarity(abstracted, var, sig, sizes=(2, 3), samples=150, seed=0, scheme="strong",
                      strawson=False):
    """Monotonicity of λX.φ in a set-typed X (Ladusaw 1979; van Benthem 1986): test
    φ[A] ⇒ φ[A ∪ {a}] (↑) and the converse (↓) over random models. With strawson=True,
    pairs on which either side is undefined are skipped: Strawson entailment (von Fintel 1999)."""
    ty = var.type
    if final(ty) != T or not arg_types(ty):
        raise ModelError("polarity requires a position of a set type <σ1,…,<σn,t>>")
    rng = random.Random(seed)
    up = down = tested = skipped = 0
    fn = lam(var, abstracted)
    for n in sizes:
        for _ in range(samples):
            M = random_model(sig, n, 0.5, rng)
            f = Evaluator(M, scheme)(fn)
            cells = list(itertools.product(*(M.domain(a) for a in arg_types(ty))))
            A = {c for c in cells if rng.random() < 0.5}
            rest = [c for c in cells if c not in A]
            if not rest:
                continue
            c = rng.choice(rest)
            v1, v2 = f(_pred(len(c), A)), f(_pred(len(c), A | {c}))
            if strawson and (v1 is None or v2 is None):
                skipped += 1
                continue
            tested += 1
            up += v1 is True and v2 is not True
            down += v2 is True and v1 is not True
    if not up and not down:
        label = "constant (both ↑ and ↓)"
    elif not up:
        label = "↑ upward entailing"
    elif not down:
        label = "↓ downward entailing"
    else:
        label = "non-monotone"
    return label, {"tested": tested, "↑-violations": up, "↓-violations": down,
                   **({"skipped (undefined)": skipped} if strawson else {})}
