"""Regression and property tests for denote.   Run:  PYTHONPATH=src pytest -q"""
import random
from pathlib import Path

from denote import parse_type, parse_term, typecheck, normalize, canonical, parse_tree, Lexicon
from denote import Interpreter, Options, readings, Evaluator, random_model, project
from denote.typesys import E, order
from denote.terms import Var, show, constants, lam
from denote.lexicon import LexiconError
from denote.projection import TF
from denote.models import SCHEMES
from denote.analysis import ambiguity, gq, inference
from denote.trees import load_trees
from denote.export import to_tptp

EX = Path(__file__).resolve().parents[1] / "examples"
LEX = Lexicon.load(EX / "extensional.lex")
INT = Lexicon.load(EX / "intensional.lex")


def tree(spec):
    return load_trees(str(EX / spec))[0][1]


def derive(t, lex=LEX, **kw):
    return Interpreter(lex, Options(**kw)).interpret(parse_tree(t) if t.startswith("[") else tree(t))


def same(term, formula, lex=LEX):
    from denote.terms import Const
    consts = {c: Const(c, ty) for c, ty in lex.signature.items()}
    return canonical(term) == canonical(typecheck(parse_term(formula, lex.free, consts)))


# ── the object language ────────────────────────────────────────────────────────────
def test_types_and_order():
    t = parse_type("<<e,t>,<<e,t>,t>>")
    assert str(t) == "<<e,t>,<<e,t>,t>>" and order(t) == 2


def test_parse_show_roundtrip():
    t = typecheck(parse_term(r"\P.\Q. forall x. P(x) -> Q(x)"))
    assert show(t) == "λP.λQ.∀x[P(x) → Q(x)]"
    assert canonical(typecheck(parse_term(show(t, "ascii")))) == canonical(t)


def test_capture_avoiding_substitution():
    y = Var("y", E)
    t = typecheck(parse_term(r"(\x.\y. love(x, y))(y)", free={"y": y}))
    assert show(normalize(t)) == "λy'.love(y, y')"


def test_lexicon_type_error_is_reported():
    try:
        Lexicon.loads(r"bad :: <e,t> = \x.\y. love(x, y)")
    except LexiconError as ex:
        assert "declared" in str(ex)
    else:
        raise AssertionError("expected a LexiconError")


# ── composition ────────────────────────────────────────────────────────────────────
def test_functional_application():
    assert show(derive("[S [DP every dog] [VP barks]]")[0].term) == "∀x[dog(x) → bark(x)]"


def test_relative_clause_by_predicate_abstraction():
    assert same(derive("phenomena.trees#relative")[0].term, "forall x. dog(x) & chase(x, felix) -> bark(x)")


def test_type_mismatch_diagnostics():
    I = Interpreter(LEX, Options(shifts="off"))
    assert not I.interpret(tree("phenomena.trees#objquant"))
    assert any("QR" in s for f in I.failures for s in f.suggestions)


def test_copula_via_BE_shift():
    d = derive("phenomena.trees#copula")[0]
    assert "BE" in d.shifts and same(d.term, "exists x. dog(x) & x = rex")


def test_cross_categorial_only():
    a, b = derive("phenomena.trees#only")[0].term, derive("phenomena.trees#vponly")[0].term
    assert canonical(a) == canonical(b)


# ── scope ──────────────────────────────────────────────────────────────────────────
def test_scope_concordance_simple():
    rs, _ = readings(tree("scope.trees#ea"), LEX)
    assert len(rs) == 2 and all(set(r.methods) == {"qr", "cooper", "cont", "ar"} for r in rs)


def test_spurious_ambiguity_collapses_model_theoretically():
    rs, _ = readings(tree("scope.trees#ee"), LEX)
    assert len(rs) == 2 and len(ambiguity.analyse([r.term for r in rs]).classes) == 1


def test_one_level_continuations_cannot_interleave():
    rs, stats = readings(tree("scope.trees#triple"), LEX)
    assert len(rs) == 6 and stats["qr"] == 6 and stats["cont"] == 4


def test_inverse_linking_and_cooper_free_variable_problem():
    rs, stats = readings(tree("scope.trees#inverse"), LEX)
    assert len(rs) == 2 and stats["cooper_ill_formed"] >= 1


def test_de_re_requires_unbounded_qr_or_storage():
    t = load_trees(str(EX / "intensional.trees#dedicto"))[0][1]
    rs, _ = readings(t, INT)
    assert len(rs) == 2 and sum("qr" in r.methods for r in rs) == 1 and all("cooper" in r.methods for r in rs)
    rs, _ = readings(t, INT, bounded=False)
    assert all("qr" in r.methods for r in rs)


# ── partiality and projection ──────────────────────────────────────────────────────
def test_bilateral_translation_agrees_with_trivalent_evaluation():
    rng = random.Random(7)
    srcs = ["bald(iota x[king(x)])", "exists x[son(x, j)] -> bald(iota y[son(y, j)])",
            "forall x[boy(x) -> love(x, iota y[mother(y, x)])]", "exists x[boy(x) & @[tall(x)] happy(x)]",
            "card x[bald(iota y[son(y, x)])] > 1"]
    for src in srcs:
        phi = typecheck(parse_term(src))
        for sch in SCHEMES:
            t_, f_ = TF(phi, sch)
            for _ in range(80):
                ev = Evaluator(random_model(constants(phi), rng.randint(1, 4), 0.5, rng), sch)
                v = ev(phi)
                assert (ev(t_), ev(f_)) == (v is True, v is False), (src, sch)


def test_conditional_presupposition_strong_kleene():
    phi = derive("phenomena.trees#cond")[0].term
    _, pi = project(phi, "strong")
    rng = random.Random(3)
    for _ in range(200):
        M = random_model(constants(phi), rng.randint(1, 4), 0.5, rng)
        kings = [x for x in M.domains["e"] if (x,) in {tuple([k]) if isinstance(k, str) else tuple(k)
                                                        for k in M.raw.get("king", [])}]
        exist = {k[0] for k in M.raw.get("exist", [])}
        expected = (not any(k in exist for k in kings)) or len(kings) == 1
        assert Evaluator(M, "strong")(pi) is expected


def test_factive_presupposition_survives_negation():
    phi = derive("intensional.trees#negfactive", INT)[0].term
    for sch in SCHEMES:
        assert show(project(phi, sch)[1]) == "leave(w, mary)"


# ── generalized quantifiers, polarity, inference ───────────────────────────────────
def test_gq_universals():
    det = {e.name: e.term for es in Lexicon.load(EX / "determiners.lex").entries.values() for e in es}
    p, _, _ = gq.universals(det["every"], 3)
    assert p["CONS"] and p["EXT"] and p["QUANT"] and p["↑MON"] and p["↓mon (restrictor)"]
    assert not gq.universals(det["gleeb"], 3)[0]["CONS"]
    assert not gq.universals(det["equi"], 3)[0]["CONS"]


def test_strawson_downward_entailment_of_only():
    t = tree("phenomena.trees#onlynpi")
    leaf = next(n for n, _ in t.walk() if n.is_leaf and n.word == "cat")
    X = Var("X", parse_type("<e,t>"))
    phi = Interpreter(LEX, Options(override={leaf.uid: X})).interpret(t)[0].term
    assert gq.position_polarity(phi, X, constants(phi))[0] == "non-monotone"
    assert gq.position_polarity(phi, X, constants(phi), strawson=True)[0].startswith("↓")


def test_entailment_verdicts():
    every, some = derive("[S [DP every dog] [VP barks]]")[0].term, derive("[S [DP some dog] [VP barks]]")[0].term
    no = derive("[S [DP no dog] [VP barks]]")[0].term
    assert inference.entails([some], every).label == "unknown"
    assert inference.entails([no], some).label == "no"
    rex = derive("[S Rex [VP is [DP a dog]]]")[0].term
    assert inference.entails([every, rex], derive("[S Rex [VP barks]]")[0].term).label == "yes"


def test_davidsonian_diamond():
    ev = Lexicon.load(EX / "events.lex")
    terms = [Interpreter(ev).interpret(t)[0].term for _, t in load_trees(str(EX / "events.trees"))]
    assert set(ambiguity.analyse(terms).hasse) == {(1, 0), (2, 0), (3, 1), (3, 2)}


def test_question_answer_congruence():
    from denote.reduce import canonical as c
    q = derive("phenomena.trees#question")[0]
    good, bad = derive("phenomena.trees#answer")[0], derive("phenomena.trees#wrongfocus")[0]
    bq = lam(q.focus[0][0], q.term)
    assert c(bq) == c(lam(good.focus[0][0], good.focus[1]))
    assert c(bq) != c(lam(bad.focus[0][0], bad.focus[1]))


def test_tptp_export():
    assert to_tptp([derive("[S [DP every dog] [VP barks]]")[0].term]).startswith("fof(p1, axiom, ![X0]:")
