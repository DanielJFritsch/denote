"""Four routes to scope: Quantifier Raising (May 1977; H&K ch. 7), Cooper storage (1983),
continuations (Barker 2002), flexible types / argument raising (Hendriks 1993)."""
from __future__ import annotations

import itertools
from dataclasses import dataclass, field, replace

from .typesys import GQ, E
from .terms import fv
from .trees import Tree
from .compose import Interpreter, Options, index_var
from .reduce import canonical

CLAUSE = ("S", "TP", "CP", "IP")
METHODS = ("qr", "cooper", "cont", "ar")


@dataclass
class Reading:
    term: object
    deriv: object
    methods: dict = field(default_factory=dict)    # method -> provenance (LF / rule trail)


def _is_clause(n):
    return n.label.split("_")[0] in CLAUSE


def qr_lfs(tree, lex, opts=None, bounded=True):
    """The surface structure plus one LF per linear order of the quantificational DPs, each
    raised to the nearest clause (the root if bounded=False) and adjoined with a λ-binder.
    Returns triples (name, LF, indices of the QR traces)."""
    opts = opts or Options()
    probe = Interpreter(lex, replace(opts, lens="hk", shifts="off"))
    pm = tree.parent_map()
    cands = [n for n, p in tree.walk() if p is not None and any(d.type == GQ for d in probe._node(n))]
    ids = {c.uid for c in cands}
    cands = [c for c in cands if not (pm[c.uid].uid in ids and len(pm[c.uid].children) == 1)]
    base = max([n.index for n, _ in tree.walk() if n.index is not None] or [0])
    lfs = [("surface", tree, ())]
    for perm in itertools.permutations(cands):
        lf, idx, used = tree.copy(), base, []
        for c in reversed(perm):                      # narrowest first ⇒ perm[0] widest
            idx += 1
            used.append(idx)
            node, pmap = lf.find(c.uid), lf.parent_map()
            parent = pmap[node.uid]
            target = parent
            while not _is_clause(target) and pmap[target.uid] is not None:
                target = pmap[target.uid]
            if not bounded:
                target = lf
            while pmap[target.uid] is not None and pmap[target.uid].adjoined:
                target = pmap[target.uid]
            parent.children[parent.children.index(node)] = Tree("t", word="t", index=idx)
            new = Tree(target.label, [node, Tree(str(idx), [target], index=idx, adjoined=True)], adjoined=True)
            tp = pmap[target.uid]
            if tp is None:
                lf = new
            else:
                tp.children[tp.children.index(target)] = new
        lfs.append((" ≫ ".join(c.text() or c.label for c in perm), lf, tuple(used)))
    seen, out = set(), []
    for name, lf, used in lfs:
        if str(lf) not in seen:
            seen.add(str(lf))
            out.append((name, lf, used))
    return out


def readings(tree, lex, methods=METHODS, opts=None, bounded=True):
    """Distinct readings (up to α/βη-equivalence) with the mechanisms that derive them."""
    opts = opts or Options()
    found, stats = {}, {}

    def add(d, method, prov):
        k = canonical(d.term)
        if k not in found:
            found[k] = Reading(d.term, d)
        found[k].methods.setdefault(method, prov)

    for m in methods:
        if m == "qr":
            n = unbound = 0
            for name, lf, used in qr_lfs(tree, lex, opts, bounded):
                shifts = "off" if name == "surface" else "last-resort"
                I = Interpreter(lex, replace(opts, shifts=shifts, lens="hk"))
                traces = {index_var(i, E) for i in used}
                for d in I.interpret(lf):
                    if fv(d.term) & traces:               # a QR trace escaped its binder
                        unbound += 1
                        continue
                    add(d, "qr", f"LF: {lf}")
                    n += 1
            stats["qr"] = n
            if unbound:
                stats["qr_unbound_trace"] = unbound
        elif m == "cooper":
            I = Interpreter(lex, replace(opts, shifts="off", lens="cooper"))
            ds = I.interpret(tree)
            for d in ds:
                add(d, "cooper", "retrieval order: " + "; ".join(x.note for x in d.walk() if x.rule == "RETRIEVE"))
            stats["cooper"] = len(ds)
            stats["cooper_ill_formed"] = I.discarded
        elif m == "cont":
            I = Interpreter(lex, replace(opts, shifts="off", lens="cont"))
            ds = I.interpret(tree)
            for d in ds:
                add(d, "cont", " ".join(x.rule for x in d.walk() if x.rule.startswith("CONT")))
            stats["cont"] = len(ds)
        elif m == "ar":
            I = Interpreter(lex, replace(opts, shifts="last-resort", lens="hk"))
            ds = I.interpret(tree)
            for d in ds:
                add(d, "ar", "shifts: " + (",".join(d.shifts) or "none"))
            stats["ar"] = len(ds)
        else:
            raise ValueError(f"unknown scope method {m!r}")
    return list(found.values()), stats
