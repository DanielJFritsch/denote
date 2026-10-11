"""Regenerate examples/output/ (GALLERY.md, derivation.tex, diamond.dot) by running the CLI
on the shipped examples. Usage: python examples/build_gallery.py   (or: make gallery)"""
import os
import shlex
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / "examples" / "output"
ENV = {**os.environ, "PYTHONPATH": str(ROOT / "src"), "PYTHONIOENCODING": "utf-8"}
X, P, S = "examples/extensional.lex", "examples/phenomena.trees", "examples/scope.trees"
I, IT = "examples/intensional.lex", "examples/intensional.trees"

SECTIONS = [
    ("Lexicon inspection", "The type inventory and the globally inferred signature Σ of the "
     "extensional fragment.", [f"denote lint {X}"]),
    ("A Heim & Kratzer derivation with Predicate Abstraction", "Every node shows its type, its "
     "β-normal denotation, the rule that licensed it, and (with `--steps`) each contraction.",
     [f"denote derive {X} {P}#relative --steps"]),
    ("Type mismatch, diagnosis, and last-resort repair", "With type-shifting disabled the object "
     "quantifier is uninterpretable in situ; the diagnosis proposes repairs. With the default "
     "economy setting, Hendriks's argument raising applies.",
     [f"denote derive {X} {P}#objquant --shifts off", f"denote derive {X} {P}#copula"]),
    ("Scope: four mechanisms, one concordance", "Readings are pooled modulo α/βη and annotated with "
     "the mechanisms that derive them; model-theoretic statistics follow.",
     [f"denote readings {X} {S}#ea --lfs"]),
    ("Spurious ambiguity", "Two derivationally distinct LFs that collapse into one model-theoretic "
     "equivalence class (Δ = 0).", [f"denote readings {X} {S}#ee"]),
    ("Three quantifiers: where the mechanisms part ways", "QR and Cooper storage derive all 3! "
     "orders; one-level continuations cannot let the subject take intermediate scope.",
     [f"denote readings {X} {S}#triple"]),
    ("Inverse linking and the free-variable problem of storage", "Only argument raising yields the "
     "surface (narrow) reading; one Cooper retrieval order is discarded as ill-formed (Keller 1988).",
     [f"denote readings {X} {S}#inverse"]),
    ("De re / de dicto", "Clause-bounded QR yields only the de dicto reading; storage, or unbounded "
     "QR, adds de re. Both readings are evaluated in a Kripke model.",
     [f"denote readings {I} {IT}#dedicto --model examples/kripke.toml",
      f"denote readings {I} {IT}#dedicto --unbounded --method qr"]),
    ("Presupposition projection under three trivalent schemes", "The proviso problem (conditional "
     "presupposition), universal projection from a quantifier, and factivity under negation.",
     [f"denote presup {X} {P}#cond", f"denote presup {X} {P}#bound",
      f"denote presup {I} {IT}#negfactive"]),
    ("Focus, alternatives, and question–answer congruence", "",
     [f"denote focus {X} {P}#vponly", f"denote focus {X} {P}#answer --question {P}#question",
      f"denote focus {X} {P}#wrongfocus --question {P}#question"]),
    ("Generalized-quantifier universals", "Exhaustive verification over |D| ≤ 4, with graded "
     "monotonicity and van Benthem number triangles.",
     [f"denote universals examples/determiners.lex",
      f"denote universals examples/determiners.lex --det most,both --triangle 4"]),
    ("Polarity: classical versus Strawson entailment", "Positions are abstracted and tested for "
     "monotonicity; *only* is non-monotone classically but Strawson-downward-entailing.",
     [f"denote polarity {X} {P}#quant --at dog", f"denote polarity {X} {P}#onlynpi --at cat",
      f"denote polarity {X} {P}#onlynpi --at cat --strawson"]),
    ("Informativity and the 0–1 law", "Bar-Hillel–Carnap measures, and finite-size profiles that "
     "drift toward 0 or 1 as domains grow.",
     [f'denote info {X} "[S [DP every dog] [VP barks]]" --profile',
      f'denote info {X} "[S [DP some dog] [VP barks]]" --profile']),
    ("Davidson's diamond", "An entailment lattice over event-semantic sentences.",
     ["denote lattice examples/events.lex examples/events.trees --dot examples/output/diamond.dot"]),
    ("Bounded entailment with counter-models and prover export", "",
     [f'denote entail {X} --premise "[S [DP every dog] [VP barks]]" --premise "[S Rex [VP is [DP a dog]]]" '
      f'--hypothesis "[S Rex [VP barks]]" --tptp --smt',
      f'denote entail {X} --premise "[S [DP some dog] [VP barks]]" --hypothesis "[S [DP every dog] [VP barks]]"']),
    ("Competing analyses scored side by side", "Frege–Strawson versus Russellian definites on one suite.",
     [f"denote suite {X} examples/russell.lex --suite examples/suite.toml"]),
    ("Corpus coverage and failure taxonomy", "", [f"denote coverage {X} examples/corpus.trees"]),
    ("Grading a student's formula", "",
     [f'denote check {X} {S}#ea --answer "exists y. book(y) & forall x. student(x) -> read(x, y)"',
      f'denote check {X} {S}#ea --answer "forall y. book(y) -> exists x. student(x) & read(x, y)"']),
    ("Truth in a model and derivational complexity", "",
     [f"denote eval {X} {P} --model examples/world.toml", f"denote derive {X} {P}#bound --metrics"]),
    ("Raw λ-calculus: normal-order reduction with α-conversion", "",
     ['denote reduce "(\\R.\\x.\\y. R(y)(x))(\\x.\\y. love(x, y))"']),
]

HEADER = """# Gallery of sample outputs

Every block below is produced verbatim by `python examples/build_gallery.py` (or `make gallery`)
from the inputs in `examples/`. A LaTeX rendering of one derivation is in
[`derivation.tex`](derivation.tex); the entailment lattice of §14 is in [`diamond.dot`](diamond.dot).
"""


def run(cmd):
    args = shlex.split(cmd)
    p = subprocess.run([sys.executable, "-m", "denote", *args[1:]], cwd=ROOT, env=ENV,
                       capture_output=True, text=True, encoding="utf-8")
    return (p.stdout + p.stderr).rstrip()


def main():
    OUT.mkdir(parents=True, exist_ok=True)
    parts = [HEADER]
    for i, (title, blurb, cmds) in enumerate(SECTIONS, 1):
        parts.append(f"## {i}. {title}\n" + (f"\n{blurb}\n" if blurb else ""))
        for cmd in cmds:
            parts.append(f"```console\n$ {cmd}\n{run(cmd)}\n```\n")
    (OUT / "GALLERY.md").write_text("\n".join(parts), encoding="utf-8")
    tex = run(f"denote derive {X} {P}#relative --format latex --standalone")
    (OUT / "derivation.tex").write_text(tex + "\n", encoding="utf-8")
    print(f"wrote {OUT / 'GALLERY.md'} and {OUT / 'derivation.tex'}")


if __name__ == "__main__":
    main()
