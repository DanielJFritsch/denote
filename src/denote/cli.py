"""denote — command-line interface. Run `denote <command> -h` for details."""
from __future__ import annotations

import argparse
import sys
import tomllib
from pathlib import Path

from .typesys import ET, GQ, Fun, type_str, order
from .terms import Const, Var, show, constants, lam
from .parser import parse_term, ParseError
from .typecheck import typecheck, SemTypeError
from .reduce import normalize, canonical
from .trees import load_trees
from .lexicon import Lexicon, LexiconError
from .compose import Interpreter, Options, SHIFTS, DEFAULT_SHIFTS
from .scope import readings, qr_lfs, METHODS
from .models import Model, Evaluator, SCHEMES, ModelError
from .projection import project
from . import render, export, __version__
from .analysis import ambiguity, gq, metrics, inference


class NoDerivation(Exception):
    pass


def _tv(v):
    return "#" if v is None else str(int(v))


def _opts(a, **kw):
    senses = dict(s.split("=", 1) for s in (a.sense or []))
    allowed = tuple(a.allow.split(",")) if a.allow else DEFAULT_SHIFTS
    return Options(shifts=a.shifts, lens=a.lens, senses=senses, allowed=allowed, **kw)


def _derive(lex, tree, a, opts=None):
    I = Interpreter(lex, opts or _opts(a))
    return I.interpret(tree), I


def _report_failure(I):
    print("✗ no derivation reaches type t")
    seen = set()
    for f in I.failures:
        key = (f.kind, f.node.label, f.detail)
        if key in seen:
            continue
        seen.add(key)
        print(f"  [{f.kind}] at {f.node.label}: {f.detail}")
        for s in f.suggestions:
            print(f"      ↳ try: {s}")


def _first(lex, spec, a, quiet=False):
    ident, tree = load_trees(spec)[0]
    ds, I = _derive(lex, tree, a)
    if not ds:
        if not quiet:
            _report_failure(I)
        raise NoDerivation(tree.text())
    return ds[0], tree


def _formula(lex, src):
    consts = {c: Const(c, ty) for c, ty in lex.signature.items()}
    return typecheck(parse_term(src, lex.free, consts))


def _meanings(lex, specs, a, quiet=False):
    out = []
    for spec in specs:
        s = spec.strip()
        if s.startswith(("[", "(")) or ".trees" in s:
            out.append(_first(lex, s, a, quiet)[0].term)
        else:
            out.append(_formula(lex, s))
    return out


# ----------------------------------------------------------------------------- commands

def cmd_derive(a):
    lex = Lexicon.load(a.lexicon)
    tex = []
    for ident, tree in load_trees(a.tree):
        ds, I = _derive(lex, tree, a)
        if a.format == "text":
            print(f"── {ident}: {tree.text()}")
        if not ds:
            _report_failure(I)
            print()
            continue
        for i, d in enumerate(ds[: a.max], 1):
            if a.format == "latex":
                tex.append((tree.text(), d))
            elif a.format == "json":
                print(render.to_json(d))
            else:
                print(f"derivation {i}/{len(ds)}" + (f"   senses: {dict(d.senses)}" if d.senses else "")
                      + (f"   type-shifts: {', '.join(d.shifts)}" if d.shifts else ""))
                print(render.text_tree(d, a.style, a.steps))
                if a.metrics:
                    for k, v in metrics.complexity(d).items():
                        print(f"   {k:>18}: {v}")
                print()
    if tex:
        print(render.latex_document(tex) if a.standalone else
              "\n\n".join(render.latex_tree(d) + "\n" + render.latex_equations(d) for _, d in tex))


def cmd_readings(a):
    lex = Lexicon.load(a.lexicon)
    ident, tree = load_trees(a.tree)[0]
    methods = METHODS if a.method == "all" else tuple(a.method.split(","))
    rs, stats = readings(tree, lex, methods, _opts(a), bounded=not a.unbounded)
    print(f"sentence: {tree.text()}")
    print(f"mechanisms: {', '.join(methods)}{'   (QR unbounded)' if a.unbounded else ''}   "
          f"distinct readings modulo α/βη: {len(rs)}\n")
    for i, r in enumerate(rs, 1):
        print(f"ρ{i}  {show(r.term, a.style)}")
    print("\nmechanism concordance (✓ = derivable)")
    print("      " + "".join(f"{m:^8}" for m in methods))
    for i, r in enumerate(rs, 1):
        print(f"ρ{i:<5}" + "".join(f"{'✓' if m in r.methods else '·':^8}" for m in methods))
    print("derivation counts: " + ", ".join(f"{k}={v}" for k, v in stats.items()))
    if a.lfs:
        print("\nlogical forms (QR):")
        for name, lf, _ in qr_lfs(tree, lex, _opts(a), not a.unbounded):
            print(f"  [{name}]  {lf}")
    if a.model:
        ev = Evaluator(Model.load(a.model), a.scheme)
        print(f"\ntruth values in {a.model}: " + ", ".join(f"ρ{i} = {_tv(ev(r.term))}" for i, r in enumerate(rs, 1)))
    if len(rs) > 1:
        terms = [r.term for r in rs]
        rep = ambiguity.analyse(terms, a.scheme, samples=a.samples, seed=a.seed)
        print(f"\nmodel-theoretic profile over {rep.n_models} models (exhaustive where ≤ 4096 per size):")
        print("  equivalence classes: " + "  ".join("{" + ",".join(f"ρ{i + 1}" for i in c) + "}" for c in rep.classes))
        print(f"  scope sensitivity Δ = {rep.sensitivity:.3f}    profile entropy H = {rep.entropy:.3f} bits")
        print("  disagreement δ(ρi,ρj):")
        for i, row in enumerate(rep.delta):
            print(f"    ρ{i + 1:<3}" + " ".join(f"{x:5.3f}" for x in row))
        print("  m(ρi) = " + ", ".join(f"ρ{i + 1}: {p:.3f}" for i, p in enumerate(rep.p_true)))
        print("  entailment (Hasse): " + (", ".join(f"ρ{i + 1} ⊨ ρ{j + 1}" for i, j in rep.hasse)
                                        or "none (logically independent)"))
        print("  weakest: " + ", ".join(f"ρ{i + 1}" for i in rep.weakest)
              + "    strongest: " + ", ".join(f"ρ{i + 1}" for i in rep.strongest))
        if a.dot:
            Path(a.dot).write_text(ambiguity.to_dot(terms, rep, show), encoding="utf-8")
            print(f"  Hasse diagram written to {a.dot}")


def cmd_lattice(a):
    lex = Lexicon.load(a.lexicon)
    terms, names = [], []
    for ident, tree in load_trees(a.trees):
        ds, I = _derive(lex, tree, a)
        if not ds:
            print(f"✗ {ident}: no derivation (skipped)")
            continue
        terms.append(ds[0].term)
        names.append(ident)
        print(f"{ident:<8} {tree.text()}\n{'':<8} {show(ds[0].term, a.style)}")
    rep = ambiguity.analyse(terms, a.scheme, samples=a.samples, seed=a.seed)
    print(f"\nentailment matrix over {rep.n_models} models (row ⊨ column):")
    print("        " + "".join(f"{n:^8}" for n in names))
    for i, n in enumerate(names):
        print(f"{n:<8}" + "".join(f"{('⊨' if rep.entails[i][j] else '·'):^8}" for j in range(len(names))))
    print("Hasse diagram: " + (", ".join(f"{names[i]} ⊨ {names[j]}" for i, j in rep.hasse) or "no entailments"))
    print("m(φ): " + ", ".join(f"{n} = {p:.3f}" for n, p in zip(names, rep.p_true)))
    if a.dot:
        Path(a.dot).write_text(ambiguity.to_dot(terms, rep, show, names), encoding="utf-8")
        print(f"DOT written to {a.dot}")


def cmd_eval(a):
    lex = Lexicon.load(a.lexicon)
    ev = Evaluator(Model.load(a.model), a.scheme)
    for ident, tree in load_trees(a.tree):
        ds, I = _derive(lex, tree, a)
        if not ds:
            print(f"{ident:<12} —   (no derivation)")
        for d in ds:
            try:
                v = _tv(ev(d.term))
            except ModelError as ex:
                v = f"!  ({ex})"
            print(f"{ident:<12} {v:<3} {show(d.term, a.style)}")


def cmd_presup(a):
    lex = Lexicon.load(a.lexicon)
    d, tree = _first(lex, a.tree, a)
    print(f"sentence: {tree.text()}\nmeaning : {show(d.term, a.style)}\n")
    for sch in SCHEMES:
        asr, pre = project(d.term, sch)
        print(f"[{sch:^6}] presupposition π = {show(pre, a.style)}")
        print(f"         assertion      α = {show(asr, a.style)}")


def cmd_focus(a):
    lex = Lexicon.load(a.lexicon)
    if a.question:
        q, _ = _first(lex, a.question, a)
        ans, _ = _first(lex, a.tree, a)
        if not q.focus or not ans.focus:
            sys.exit("the question needs a wh-marked and the answer an F-marked constituent")
        bq, ba = lam(q.focus[0][0], q.term), lam(ans.focus[0][0], ans.focus[1])
        ok = canonical(bq) == canonical(ba)
        print(f"question abstract  λz.Q = {show(normalize(bq), a.style)}")
        print(f"answer background  λz.B = {show(normalize(ba), a.style)}")
        print(f"Q–A congruence (Rooth 1992: ⟦Q⟧ ⊆ ⟦A⟧^f): {'✓ congruent' if ok else '✗ incongruent'}")
        return
    d, tree = _first(lex, a.tree, a)
    print(f"sentence: {tree.text()}\nordinary value  ⟦S⟧° = {show(d.term, a.style)}")
    if d.focus:
        vs, tpl, vals = d.focus
        print(f"focus value     ⟦S⟧ᶠ = {{ {show(tpl, a.style)} | "
              + ", ".join(f"{v.name} ∈ D_{type_str(v.type)}" for v in vs) + " }")
        print("structured meaning ⟨B, F⟩ = ⟨" + show(normalize(lam(vs[0], tpl)), a.style) + ", "
              + ", ".join(show(x, a.style) for x in vals if x is not None) + "⟩")
    for x in d.walk():
        if x.rule == "FOC":
            print("focus operator: " + x.note)


def cmd_universals(a):
    lex = Lexicon.load(a.lexicon)
    names = ["CONS", "EXT", "QUANT", "↑MON", "MON↓", "↑mon (restrictor)", "↓mon (restrictor)", "SYM", "INT", "non-trivial"]
    short = ["CONS", "EXT", "QUANT", "MON↑", "MON↓", "↑MON", "↓MON", "SYM", "INT", "NTRIV"]
    pick = set(a.det.split(",")) if a.det else None
    print(f"generalized-quantifier properties, exhaustive over all A, B ⊆ D with |D| ≤ {a.max_n}\n")
    print(f"{'determiner':<14}" + "".join(f"{s:>6}" for s in short) + "   graded MON↑/MON↓")
    tri = []
    for w, es in sorted(lex.entries.items()):
        for e in es:
            if e.type != Fun(ET, GQ) or constants(e.term) or (pick and e.name not in pick):
                continue
            props, viol, graded = gq.universals(e.term, a.max_n)
            print(f"{e.name:<14}" + "".join(f"{('✓' if props[n] else '✗'):>6}" for n in names)
                  + f"   {graded['↑MON']:.2f}/{graded['MON↓']:.2f}")
            if a.triangle:
                tri.append((e.name, gq.number_triangle(e.term, a.triangle)))
    print("\nMON↑/MON↓ = scope (right) monotonicity; ↑MON/↓MON = restrictor (left) monotonicity;\n"
          "graded = 1 − proportion of monotonicity violations among applicable pairs")
    for name, t in tri:
        print(f"\nnumber triangle for '{name}' (van Benthem 1986):\n{t}")


def cmd_polarity(a):
    lex = Lexicon.load(a.lexicon)
    ident, tree = load_trees(a.tree)[0]
    targets = [n for n, _ in tree.walk() if n.is_leaf and n.word == a.at]
    if not targets:
        sys.exit(f"no leaf '{a.at}' in the tree")
    base = Interpreter(lex, _opts(a))._node(targets[0])
    if not base:
        sys.exit(f"'{a.at}' has no interpretation")
    X = Var("X", base[0].type)
    ds, I = _derive(lex, tree, a, _opts(a, override={targets[0].uid: X}))
    if not ds:
        _report_failure(I)
        raise NoDerivation(tree.text())
    label, counts = gq.position_polarity(ds[0].term, X, constants(ds[0].term), seed=a.seed, strawson=a.strawson)
    print(f"sentence: {tree.text()}\nposition '{a.at}' abstracted, X : {type_str(X.type)}:  {show(lam(X, ds[0].term), a.style)}")
    print(f"{'Strawson-' if a.strawson else ''}polarity: {label}   {counts}")
    print("NPI prediction (Fauconnier 1975; Ladusaw 1979" + ("; von Fintel 1999" if a.strawson else "")
          + "): 'any'/'ever' " + ("licensed" if label.startswith("↓") else "not licensed") + " in this position")


def cmd_info(a):
    lex = Lexicon.load(a.lexicon)
    for ident, tree in load_trees(a.tree):
        ds, I = _derive(lex, tree, a)
        if not ds:
            continue
        info = metrics.informativity(ds[0].term, a.scheme, samples=a.samples, seed=a.seed)
        print(f"{ident}: {tree.text()}\n   {show(ds[0].term, a.style)}")
        print("   " + "   ".join(f"{k} = {v:.3f}" if isinstance(v, float) else f"{k} = {v}" for k, v in info.items()))
        if a.profile:
            prof = metrics.finite_size_profile(ds[0].term, seed=a.seed)
            print("   finite-size profile m_n(φ): " + "  ".join(f"n={n}:{p:.2f}" for n, p in prof))


def cmd_entail(a):
    lex = Lexicon.load(a.lexicon)
    prem = _meanings(lex, a.premise, a)
    hyp = _meanings(lex, [a.hypothesis], a)[0]
    v = inference.entails(prem, hyp, a.scheme, a.max_n)
    for i, p in enumerate(prem, 1):
        print(f"P{i}: {show(p, a.style)}")
    print(f"H : {show(hyp, a.style)}\nverdict: {v.label}   ({v.checked} models; exhaustive up to |D| = {v.exhaustive_up_to})")
    if v.label != "yes":
        print("counter-model (premises true, hypothesis not true):\n  " + v.counter_model.describe().replace("\n", "\n  "))
    if a.tptp:
        print("\n% TPTP FOF\n" + export.to_tptp(prem, hyp))
    if a.smt:
        print("\n; SMT-LIB 2\n" + export.to_smtlib(prem, hyp))


def _suite_item(lex, it, base, a):
    if "hypothesis" in it:
        prem = _meanings(lex, it["premises"], a, quiet=True)
        hyp = _meanings(lex, [it["hypothesis"]], a, quiet=True)[0]
        return inference.entails(prem, hyp, a.scheme, a.max_n).label
    if "readings" in it:
        ident, tree = load_trees(it["tree"])[0]
        rs, _ = readings(tree, lex, ("qr",), _opts(a))
        if len(rs) < 2:
            return str(len(rs))
        return str(len(ambiguity.analyse([r.term for r in rs], a.scheme, samples=300, seed=a.seed).classes))
    d, _ = _first(lex, it["tree"], a, quiet=True)
    return _tv(Evaluator(Model.load(base / it["model"]), a.scheme)(d.term))


def cmd_suite(a):
    base = Path(a.suite).parent
    with open(a.suite, "rb") as fh:
        suite = tomllib.load(fh)
    lexes = [Lexicon.load(p) for p in a.lexicon]
    names = [Path(p).name for p in a.lexicon]
    score = {n: [0, 0] for n in names}
    print(suite.get("title", a.suite) + "\n")
    print(f"{'item':<18}{'gold':<9}" + "".join(f"{n:<20}" for n in names))
    notes = []
    for it in suite.get("item", []):
        gold = str(it.get("gold", it.get("readings", it.get("truth"))))
        row = f"{it['id']:<18}{gold:<9}"
        for lex, n in zip(lexes, names):
            try:
                got = _suite_item(lex, it, base, a)
            except NoDerivation:
                got = "fail"
            except Exception as ex:                      # report, never crash, in batch mode
                got = f"error:{type(ex).__name__}"
            ok = got == gold
            score[n][0] += ok
            score[n][1] += 1
            row += f"{('✓ ' if ok else '✗ ') + got:<20}"
        print(row)
        if "note" in it:
            notes.append(f"  {it['id']}: {it['note']}")
    print("\naccuracy: " + "   ".join(f"{n}: {c}/{t} = {c / t:.2f}" for n, (c, t) in score.items() if t))
    if notes:
        print("notes:\n" + "\n".join(notes))


def cmd_coverage(a):
    lex = Lexicon.load(a.lexicon)
    rep = metrics.coverage(load_trees(a.corpus), lambda: Interpreter(lex, _opts(a)))
    print(f"coverage: {rep['covered']}/{rep['items']} = {rep['rate']:.1%}")
    for ident, ok, n, fails in rep["results"]:
        why = "" if ok else "   ← " + "; ".join(dict.fromkeys(f.detail for f in fails[:3]))
        print(f"  {'✓' if ok else '✗'} {ident:<6} {n} derivation(s){why}")
    for key in ("lexical gaps", "type mismatches", "failing labels"):
        if rep[key]:
            print(f"{key}: " + ", ".join(f"{k} ×{v}" for k, v in rep[key].most_common()))


def cmd_lint(a):
    lex = Lexicon.load(a.lexicon)
    print(f"{a.lexicon}: {len(lex)} entries, {len(lex.entries)} words, {len(lex.signature)} constants"
          + (f", free variables {', '.join(f'{v.name} : {v.type}' for v in lex.free.values())}" if lex.free else ""))
    print("type inventory:")
    for ty, ws in lex.type_inventory().items():
        print(f"  {type_str(ty):<26} ord {order(ty)}  {', '.join(ws)}")
    print("signature Σ: " + ", ".join(f"{c} : {type_str(t)}" for c, t in sorted(lex.signature.items())))
    for level, msg in lex.lint():
        print(f"  [{level}] {msg}")


def cmd_reduce(a):
    from .terms import typeof
    t = typecheck(parse_term(a.term))
    steps = []
    normalize(t, steps, eta=a.eta)
    print(f"   {show(t, a.style)}   : {type_str(typeof(t))}")
    for s in steps:
        print(f"⇝{s.rule} {show(s.result, a.style)}")
    if not steps:
        print("(already in normal form)")


def cmd_check(a):
    lex = Lexicon.load(a.lexicon)
    ident, tree = load_trees(a.tree)[0]
    rs, _ = readings(tree, lex, METHODS, _opts(a))
    ans = _formula(lex, a.answer)
    print(f"sentence: {tree.text()}\nanswer  : {show(ans, a.style)}")
    for i, r in enumerate(rs, 1):
        if canonical(r.term) == canonical(ans):
            print(f"✓ identical (modulo α/βη) to reading ρ{i}")
            return
    for i, r in enumerate(rs, 1):
        if (inference.entails([ans], r.term, a.scheme, 3).label == "yes"
                and inference.entails([r.term], ans, a.scheme, 3).label == "yes"):
            print(f"≈ not identical, but equivalent (bounded, |D| ≤ 3) to ρ{i}: {show(r.term, a.style)}")
            return
    print("✗ matches no derivable reading")
    for i, r in enumerate(rs, 1):
        v = inference.entails([ans], r.term, a.scheme, 3)
        print(f"  ρ{i}: {show(r.term, a.style)}\n      answer ⊨ ρ{i}? {v.label}")
        if v.counter_model is not None:
            print("      model separating them:\n        " + v.counter_model.describe().replace("\n", "\n        "))


def cmd_export(a):
    lex = Lexicon.load(a.lexicon)
    d, _ = _first(lex, a.tree, a)
    print(export.to_tptp([d.term]) if a.to == "tptp" else export.to_smtlib([d.term]))


# ----------------------------------------------------------------------------- parser

def build_parser():
    ap = argparse.ArgumentParser(prog="denote", description="Type-driven compositional semantics workbench.")
    ap.add_argument("--version", action="version", version=f"denote {__version__}")
    sub = ap.add_subparsers(dest="cmd", required=True)

    def common(name, help_, tree=True, multi=False):
        p = sub.add_parser(name, help=help_)
        p.add_argument("lexicon", nargs="+" if multi else None, help="lexicon file (.lex)")
        if tree:
            p.add_argument("tree", help="bracketed tree, FILE.trees, or FILE.trees#id")
        p.add_argument("--lens", choices=("hk", "cooper", "cont"), default="hk")
        p.add_argument("--shifts", choices=("off", "last-resort", "free"), default="last-resort")
        p.add_argument("--allow", help=f"comma-separated subset of {','.join(SHIFTS)}")
        p.add_argument("--sense", action="append", help="select a sense, e.g. the=russell")
        p.add_argument("--style", choices=("unicode", "ascii", "latex"), default="unicode")
        p.add_argument("--scheme", choices=SCHEMES, default="strong", help="trivalent projection scheme")
        p.add_argument("--seed", type=int, default=0)
        p.add_argument("--samples", type=int, default=600)
        p.add_argument("--max-n", type=int, default=4)
        return p

    p = common("derive", "step-by-step derivation")
    p.add_argument("--steps", action="store_true", help="show every β/∂ contraction")
    p.add_argument("--format", choices=("text", "latex", "json"), default="text")
    p.add_argument("--standalone", action="store_true", help="complete LaTeX document")
    p.add_argument("--metrics", action="store_true", help="derivational complexity profile")
    p.add_argument("--max", type=int, default=8)
    p.set_defaults(fn=cmd_derive)
    p = common("readings", "scope readings across mechanisms, with model-theoretic statistics")
    p.add_argument("--method", default="all", help="all, or a comma list of " + ",".join(METHODS))
    p.add_argument("--unbounded", action="store_true", help="let QR cross clause boundaries")
    p.add_argument("--lfs", action="store_true", help="print the QR logical forms")
    p.add_argument("--model", help="also evaluate every reading in this model")
    p.add_argument("--dot", help="write the entailment Hasse diagram (Graphviz)")
    p.set_defaults(fn=cmd_readings)
    p = common("lattice", "entailment lattice over the sentences of a .trees file", tree=False)
    p.add_argument("trees")
    p.add_argument("--dot")
    p.set_defaults(fn=cmd_lattice)
    p = common("eval", "truth values in a model (TOML)")
    p.add_argument("--model", required=True)
    p.set_defaults(fn=cmd_eval)
    common("presup", "presupposition projection under weak/strong/middle Kleene").set_defaults(fn=cmd_presup)
    p = common("focus", "focus alternatives, structured meanings, Q–A congruence")
    p.add_argument("--question", help="wh-question tree for congruence checking")
    p.set_defaults(fn=cmd_focus)
    p = common("universals", "GQ universals of the lexicon's logical determiners", tree=False)
    p.add_argument("--det", help="comma-separated determiners to test")
    p.add_argument("--triangle", type=int, default=0, help="print number triangles up to |A| = n")
    p.set_defaults(fn=cmd_universals)
    p = common("polarity", "monotonicity of a position (NPI licensing)")
    p.add_argument("--at", required=True, help="leaf whose denotation is abstracted")
    p.add_argument("--strawson", action="store_true", help="Strawson entailment (skip undefined pairs)")
    p.set_defaults(fn=cmd_polarity)
    p = common("info", "Bar-Hillel–Carnap informativity")
    p.add_argument("--profile", action="store_true", help="finite-size profile (cf. the 0–1 law)")
    p.set_defaults(fn=cmd_info)
    p = common("entail", "bounded model-theoretic entailment", tree=False)
    p.add_argument("--premise", action="append", required=True, help="tree or formula (repeatable)")
    p.add_argument("--hypothesis", required=True)
    p.add_argument("--tptp", action="store_true")
    p.add_argument("--smt", action="store_true")
    p.set_defaults(fn=cmd_entail)
    p = common("suite", "score one or more lexicons against a TOML test suite", tree=False, multi=True)
    p.add_argument("--suite", required=True)
    p.set_defaults(fn=cmd_suite)
    p = common("coverage", "corpus coverage and failure taxonomy", tree=False)
    p.add_argument("corpus")
    p.set_defaults(fn=cmd_coverage)
    common("lint", "lexicon summary: type inventory, signature, warnings", tree=False).set_defaults(fn=cmd_lint)
    p = sub.add_parser("reduce", help="β-reduce a λ-term step by step")
    p.add_argument("term")
    p.add_argument("--eta", action="store_true")
    p.add_argument("--style", choices=("unicode", "ascii", "latex"), default="unicode")
    p.set_defaults(fn=cmd_reduce)
    p = common("check", "grade a formula against the derivable readings")
    p.add_argument("--answer", required=True)
    p.set_defaults(fn=cmd_check)
    p = common("export", "export the first reading to TPTP / SMT-LIB")
    p.add_argument("--to", choices=("tptp", "smt"), default="tptp")
    p.set_defaults(fn=cmd_export)
    return ap


def main(argv=None):
    if hasattr(sys.stdout, "reconfigure"):
        sys.stdout.reconfigure(encoding="utf-8")
    a = build_parser().parse_args(argv)
    try:
        a.fn(a)
    except NoDerivation:
        sys.exit(1)
    except (LexiconError, ModelError, ParseError, SemTypeError, ValueError, KeyError, OSError) as ex:
        print(f"denote: error: {ex}", file=sys.stderr)
        sys.exit(2)


if __name__ == "__main__":
    main()
