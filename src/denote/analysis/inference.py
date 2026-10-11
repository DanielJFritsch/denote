"""Bounded model-theoretic inference: P ⊨ H is refuted by a counter-model or confirmed for all
models up to a size bound (a semi-decision in one direction, cf. Blackburn & Bos 2005, who
pair model builders with theorem provers). Labels follow FraCaS: yes | no | unknown."""
from __future__ import annotations

from dataclasses import dataclass

from ..terms import neg
from ..models import Evaluator, all_models, random_model, count_models
from .ambiguity import signature_of


@dataclass
class Verdict:
    label: str                     # yes | no | unknown
    checked: int
    exhaustive_up_to: int
    counter_model: object = None   # model refuting P ⊨ H (if label != yes)
    witness: object = None         # model satisfying P ∧ H (if label != no)


def _models(sig, max_n, limit, samples, seed):
    import random
    rng = random.Random(seed)
    for n in range(1, max_n + 1):
        if count_models(sig, n) <= limit:
            for M in all_models(sig, n, limit):
                yield n, True, M
        else:
            for _ in range(samples):
                yield n, False, random_model(sig, n, 0.5, rng)


def entails(premises, hyp, scheme="strong", max_n=4, limit=20_000, samples=400, seed=0):
    """FraCaS-style verdict for P1…Pn ⊨ H: 'yes' if no checked model makes every Pi true and H
    not true; 'no' if no checked model makes every Pi and H true; otherwise 'unknown'."""
    sig = signature_of(list(premises) + [hyp])
    counter = witness = None
    checked = exhaustive = 0
    for n, exh, M in _models(sig, max_n, limit, samples, seed):
        checked += 1
        if exh:
            exhaustive = n
        E = Evaluator(M, scheme)
        if all(E(p) is True for p in premises):
            h = E(hyp)
            if h is not True and counter is None:
                counter = M
            if h is True and witness is None:
                witness = M
        if counter is not None and witness is not None:
            break
    label = "yes" if counter is None else ("no" if witness is None else "unknown")
    return Verdict(label, checked, exhaustive, counter, witness)
