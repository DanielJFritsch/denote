# denote

**A type-driven workbench for compositional model-theoretic semantics.**

![python](https://img.shields.io/badge/python-3.11%2B-blue) ![deps](https://img.shields.io/badge/dependencies-0-brightgreen) ![tests](https://img.shields.io/badge/tests-23%20passing-brightgreen) ![license](https://img.shields.io/badge/license-MIT-lightgrey)

`denote` realises the interpretation function $[\\![\cdot]\\!]$ of a Montagovian fragment as executable code. Given a lexicon of typed λ-terms over a many-sorted simple type theory and a labelled constituency tree, it computes, node by node, the β-normal denotation licensed by the type-driven composition principles of Klein & Sag (1985) and Heim & Kratzer (1998), and it records every contraction for inspection. Around this compositional core it provides:

* four mutually comparable **scope mechanisms**: Quantifier Raising, Cooper storage, continuations, and flexible types;
* a **trivalent model theory** with three presupposition-projection schemes, together with a bilateral translation that computes presuppositions symbolically;
* **alternative semantics** for focus;
* exhaustive verification of **generalized-quantifier universals**;
* tests of **position polarity** under classical and Strawson entailment;
* **bounded model-theoretic inference** with export to automated provers.

It also introduces a small family of **model-theoretic statistics** for ambiguity, informativity, and entailment structure that, as far as we know, no existing semantics workbench reports.

The full intellectual genealogy (≈210 works, from Frege and Church through Montague, Partee, Heim & Kratzer, Barker & Shan, and the computational-semantics literature) is set out in the companion document [`docs/theory/main.tex`](docs/theory/main.tex), an Overleaf-ready LaTeX project (prebuilt as [`docs/theory/main.pdf`](docs/theory/main.pdf), 32 pp.). Every output reproduced below, and many more, is regenerated verbatim in [`examples/output/GALLERY.md`](examples/output/GALLERY.md).

---

## Contents

1. [Synopsis](#1-synopsis)
2. [The object language Λ](#2-the-object-language-λ)
3. [Lexicons as typed signatures](#3-lexicons-as-typed-signatures)
4. [Type-driven interpretation](#4-type-driven-interpretation)
5. [Scope: four lenses](#5-scope-four-lenses)
6. [Model theory, partiality, projection](#6-model-theory-partiality-projection)
7. [Alternatives and focus](#7-alternatives-and-focus)
8. [Generalized quantifiers and polarity](#8-generalized-quantifiers-and-polarity)
9. [Model-theoretic statistics](#9-model-theoretic-statistics)
10. [Inference, coverage, competing analyses](#10-inference-coverage-competing-analyses)
11. [Command reference](#11-command-reference)
12. [Repository layout and file formats](#12-repository-layout-and-file-formats)
13. [Findings reproduced by the shipped examples](#13-findings-reproduced-by-the-shipped-examples)
14. [Limitations and roadmap](#14-limitations-and-roadmap)

---

## 1. Synopsis

```console
$ pip install -e .            # pure standard library; Python ≥ 3.11
$ denote derive examples/extensional.lex examples/phenomena.trees#relative --steps
$ denote readings examples/extensional.lex examples/scope.trees#triple
$ denote presup examples/extensional.lex examples/phenomena.trees#cond
$ make test gallery theory    # 23 tests · regenerate sample outputs · build the theory PDF
```

```console
$ denote readings examples/extensional.lex "[S [DP every student] [VP read [DP a book]]]"
ρ1  ∀x[student(x) → ∃x'[book(x') ∧ read(x, x')]]
ρ2  ∃x[book(x) ∧ ∀x'[student(x') → read(x', x)]]

mechanism concordance (✓ = derivable)
         qr    cooper   cont     ar
ρ1       ✓       ✓       ✓       ✓
ρ2       ✓       ✓       ✓       ✓
  scope sensitivity Δ = 0.069    profile entropy H = 1.294 bits
  entailment (Hasse): ρ2 ⊨ ρ1
```

---

## 2. The object language Λ

**Types.** The type hierarchy is generated from the basic sorts of a two-sorted (indeed six-sorted) extension of Church's simple theory of types, in the manner of Gallin's $\mathrm{Ty}_2$:

```math
\mathcal{T} \;::=\; e \mid t \mid s \mid v \mid i \mid d \mid \langle \mathcal{T},\mathcal{T}\rangle \mid {}'\!a
\qquad
D_t=\{0,1\},\quad D_{\langle\sigma,\tau\rangle}= D_\tau^{\,D_\sigma}
```

The sorts are entities $e$, truth values $t$, worlds $s$, eventualities $v$, times $i$, and degrees $d$. Here $'a$ is a rigid (declaration-bound) type variable that admits cross-categorial entries such as *only*. The functional order is $\mathrm{ord}(\langle\sigma,\tau\rangle)=\max(\mathrm{ord}(\sigma)+1,\mathrm{ord}(\tau))$.

**Terms.** Λ is a simply typed λ-calculus enriched with logical constants, generalized binders, and a definedness operator:

```math
M,N \;::=\; x^{\sigma} \mid c^{\sigma} \mid n \mid M\,N \mid \lambda x.M \mid \forall x.\varphi \mid \exists x.\varphi \mid \iota x.\varphi \mid \textsc{max}\,d.\varphi \mid |\{x \mid \varphi\}| \mid \neg\varphi \mid \varphi\circ\psi \mid M = N \mid \partial[\varphi]\,M
```

Here $\circ\in\\{\wedge,\vee,\rightarrow,\leftrightarrow\\}$, the comparison relations $<,\leq,>,\geq$ are defined over $D_d$, and $\partial[\varphi]M$ denotes $[\\![M]\\!]$ if $[\\![\varphi]\\!]=1$ and is otherwise undefined (#). The domain-condition notation of Heim & Kratzer, $\lambda x : \varphi\,.\,M$, is sugar for $\lambda x.\partial[\varphi]M$.

**Typing.** Typing is the usual natural-deduction system, extended with judgments for binders and partiality:

```math
\frac{\Gamma\vdash M:\langle\sigma,\tau\rangle \quad \Gamma\vdash N:\sigma}{\Gamma\vdash M\,N:\tau}
\qquad
\frac{\Gamma,x{:}\sigma\vdash M:\tau}{\Gamma\vdash\lambda x.M:\langle\sigma,\tau\rangle}
\qquad
\frac{\Gamma,x{:}\sigma\vdash\varphi:t}{\Gamma\vdash\iota x.\varphi:\sigma}
\qquad
\frac{\Gamma\vdash\varphi:t\quad\Gamma\vdash M:\tau}{\Gamma\vdash\partial[\varphi]M:\tau}
```

Types are reconstructed by first-order unification (Robinson 1965), in the manner of Hindley (1969) and Milner (1978) but without let-polymorphism. Residual type variables are then resolved by the *notational conventions of the literature*:

```math
x,y,z,u:e \qquad P,Q:\langle e,t\rangle \qquad R:\langle e,\langle e,t\rangle\rangle \qquad p,q:\langle s,t\rangle \qquad w:s \qquad e:v \qquad d:d
```

After that, constants receive result type $t$ and any remaining variables type $e$. Defaults are committed only when unification succeeds on a trial substitution, so a failed default can never leave partial bindings behind.

**Reduction.** Normal-order (leftmost-outermost) reduction applies three rules:

```math
(\lambda x.M)N \;\rightsquigarrow_\beta\; M[x:=N]
\qquad
(\partial[\varphi]F)\,N \;\rightsquigarrow_\partial\; \partial[\varphi](F\,N)
\qquad
F\,(\partial[\varphi]N) \;\rightsquigarrow_\partial\; \partial[\varphi](F\,N)
```

The ∂-rules apply only when $F$ is not an abstraction: they encode the strictness of partial application. η-contraction is available on request. Substitution is capture-avoiding, renaming by priming. By the Church–Rosser property and the strong normalisation of the simply typed calculus (Tait 1967), normal forms are unique and every strategy reaches them; normal order additionally yields the canonical textbook trace. Terms are compared modulo $\equiv_{\alpha\beta\eta}$ through nameless de Bruijn keys of their βη-normal forms.

---

## 3. Lexicons as typed signatures

A lexicon is a set of entries $w[\textit{sense}] :: \tau\ \{\textit{flags}\} = M$, where the type annotation is optional. All entries in a file (and its `@import`s) are typed **jointly**, so that every non-logical constant receives a single type. The result is a signature $\Sigma : \mathrm{Const}\to\mathcal{T}$, printed by `denote lint`. The shipped fragments are:

| file | content | theoretical commitment |
|---|---|---|
| `determiners.lex` | logical determiners, two presuppositional (*both, neither*), two unattested (*gleeb* = "only", *equi* = Härtig) | Barwise & Cooper 1981; Keenan & Stavi 1986 |
| `vocabulary.lex` | open-class extensional vocabulary; φ-features as partial identities; cross-categorial *only* with presupposed prejacent | Heim & Kratzer 1998; Cooper 1983; Horn 1969 |
| `extensional.lex` / `russell.lex` | the same fragment with Frege–Strawson $\iota$ versus Russell's total quantificational article | Frege 1892; Strawson 1950 / Russell 1905 |
| `intensional.lex` | $\mathrm{Ty}_2$ with free $w:s$; modals, belief, factive *know*, intensional *seek* | Gallin 1975; Kratzer 1977; Hintikka 1969; Zimmermann 1993 |
| `events.lex` | neo-Davidsonian predicates, Voice head, event modifiers | Davidson 1967; Parsons 1990; Kratzer 1996 |

---

## 4. Type-driven interpretation

Interpretation is the set-valued function $[\\![\cdot]\\!] : \mathrm{Tree}\to\wp(\Lambda)$. It is set-valued because lexical and structural ambiguity are first-class. At each node the applicable principles are tried and their results normalised and deduplicated modulo α:

| rule | condition | result |
|---|---|---|
| TN · NN | terminal / non-branching | lexical entry / identity; indexed traces and pronouns $\mapsto x_i$ (H&K's assignment-dependent clause) |
| **FA** | $\beta:\langle\sigma,\tau\rangle,\ \gamma:\sigma$ | $[\\![\beta]\\!]([\\![\gamma]\\!])$ (with unification for polymorphic entries) |
| **IFA** | $\beta:\langle\langle s,\sigma\rangle,\tau\rangle,\ \gamma:\sigma$ | $[\\![\beta]\\!](\lambda w.[\\![\gamma]\\!])$ |
| **PM** | $\beta,\gamma:\langle\sigma,t\rangle$ | $\lambda x.[\\![\beta]\\!](x)\wedge[\\![\gamma]\\!](x)$ |
| **PA** | binder index $i$ over $\gamma$ | $\lambda x_i.[\\![\gamma]\\!]$ |
| **EI** | $\beta:\langle e,\langle v,t\rangle\rangle,\ \gamma:\langle v,t\rangle$ | $\lambda x\lambda e.[\\![\beta]\\!](x)(e)\wedge[\\![\gamma]\\!](e)$ (Kratzer 1996) |
| **GC** | $[\beta\ \textit{and/or}\ \gamma]$, conjoinable type | pointwise $\sqcap$ / $\sqcup$ (Partee & Rooth 1983) |
| **FOC** | focus-sensitive operator, F-marked sister | $O(\lambda z.B)(F)$, cross-categorially lifted |
| EC · W | root closure | $\exists e.\varphi(e)$ for $\langle v,t\rangle$; $\varphi(w)$ for $\langle s,t\rangle$ |

**Type-shifting.** When composition fails, the following shifters can repair it. Partee's (1987) triangle supplies LIFT, IDENT, IOTA, A and BE; Geach's rule supplies FC; Hendriks's (1993) argument raising supplies AR, in two scopal variants:

```math
\begin{aligned}
\textsf{LIFT}&: e\Rightarrow\langle\langle e,t\rangle,t\rangle & a&\mapsto\lambda P.P(a) &
\textsf{IDENT}&: e\Rightarrow\langle e,t\rangle & a&\mapsto\lambda x.x=a\\
\textsf{IOTA}&: \langle e,t\rangle\Rightarrow e & P&\mapsto\iota x.P(x) &
\textsf{A}&: \langle e,t\rangle\Rightarrow\langle\langle e,t\rangle,t\rangle & P&\mapsto\lambda Q.\exists x[P(x)\wedge Q(x)]\\
\textsf{BE}&: \langle\langle e,t\rangle,t\rangle\Rightarrow\langle e,t\rangle & \mathcal{Q}&\mapsto\lambda x.\mathcal{Q}(\lambda y.y=x) &
\textsf{AR}&: \langle e,\langle e,t\rangle\rangle\times\langle\langle e,t\rangle,t\rangle & (R,\mathcal{Q})&\mapsto\lambda x.\mathcal{Q}(\lambda y.R(y)(x))
\end{aligned}
```

The economy parameter `--shifts off | last-resort | free` operationalises Partee's maxim *"type-shift only as a last resort"*. FC is opt-in (`--allow`): in testing it derives a role-reversed reading of transitive clauses with quantified objects, which is an instance of the overgeneration that Jacobson-style systems must constrain. When no rule applies, the engine emits a structured **diagnosis**: the offending node, the clashing types, and the repairs (shifts, QR, alternative lenses) that would render the node interpretable.

---

## 5. Scope: four lenses

For a tree $\tau$ with quantificational constituents $\mathcal{Q}(\tau)$, `denote readings` computes the pooled set of readings:

```math
\mathcal{R}(\tau)\;=\;\Big(\textstyle\bigcup_{m\in\{\textsf{qr},\textsf{cooper},\textsf{cont},\textsf{ar}\}}[\![\tau]\!]_m\Big)\big/\!\equiv_{\alpha\beta\eta}
```

It also reports, for each reading, which mechanisms derive it: the **mechanism concordance**.

* **QR** (May 1977; H&K ch. 7). For every $\pi\in\mathrm{Perm}(\mathcal{Q}(\tau))$, the DPs are adjoined to the nearest clausal node (or to the root with `--unbounded`), and each leaves a trace $t_i$ bound by a fresh λ-binder. Any derivation in which a QR trace remains free, as happens when a container raises above its own contents, is filtered out.
* **Cooper storage** (Cooper 1983). Interpretations are pairs $\langle\alpha,\Sigma\rangle$, and two operations act on them:
  ```math
  \textsf{STORE}:\ \langle\mathcal{Q},\varnothing\rangle\Rightarrow\langle u_i,\{\langle u_i,\mathcal{Q}\rangle\}\rangle
  \qquad
  \textsf{RETRIEVE}:\ \langle\varphi,\Sigma\uplus\{\langle u,\mathcal{Q}\rangle\}\rangle\Rightarrow\langle\mathcal{Q}(\lambda u.\varphi),\Sigma\rangle\ \ (\varphi:t)
  ```
  Retrieval orders that leave a store variable unbound are counted as `cooper_ill_formed`. This is the empirical signature of the nested-storage problem that Keller (1988) diagnosed.
* **Continuations** (Barker 2002; Barker & Shan 2014). A daughter of type $\langle\langle\sigma,t\rangle,t\rangle$ may be read as a *computation* of a σ. Values combine by FA or PM inside the monad $\eta(m)=\lambda k.k(m)$, under left-to-right or right-to-left evaluation, and are lowered at $t$ by $M\mapsto M(\lambda p.p)$. The implementation is deliberately **one-level**: it uses no towers.
* **Flexible types** (Hendriks 1993): AR in situ, with object-narrow and object-wide variants.

---

## 6. Model theory, partiality, projection

A model is $\mathcal{M}=\langle\{D_\sigma\}_\sigma, I, w_0, g\rangle$, and evaluation is the partial map $[\\![\cdot]\\!]^{\mathcal{M},g}:\Lambda_\sigma\rightharpoonup D_\sigma\cup\\{\\#\\}$. Partiality arises from ι (non-unique descriptions), from max, and from ∂. The connectives are interpreted under one of three classical trivalent schemes:

| $\varphi\wedge\psi$ | **weak** (Bochvar) | **strong** (Kleene) | **middle** (Peters) |
|---|---|---|---|
| $0\wedge\\#$ | # | 0 | 0 |
| $\\#\wedge 0$ | # | 0 | # |

**Bilateral translation.** Projection is computed symbolically. Each formula is mapped to a pair of *bivalent* formulas $\langle T(\varphi),F(\varphi)\rangle$, with clauses mirroring the evaluator for each scheme, e.g. under middle Kleene:

```math
T(\varphi\wedge\psi)=T\varphi\wedge T\psi,\qquad F(\varphi\wedge\psi)=F\varphi\vee(T\varphi\wedge F\psi),\qquad
T(\forall x\varphi)=\forall x\,T\varphi,\qquad F(\forall x\varphi)=\exists x\,F\varphi
```

Partial atoms are eliminated by Russell's expansion of ι and by the maximality clause of max:

```math
T\big(A[\iota x.\varphi]\big)=\exists z\big[T\varphi(z)\wedge\forall y\,(T\varphi(y)\rightarrow y=z)\wedge T A[z]\big]
```

The **presupposition** is then $\pi(\varphi)=T(\varphi)\vee F(\varphi)$, and the **assertion** is $T(\varphi)$. Under weak Kleene, π is computed compositionally as Bochvar definedness. The correspondence is checked by the property test `test_bilateral_translation_agrees_with_trivalent_evaluation`:

```math
[\![T(\varphi)]\!]^{\mathcal{M}}=1 \iff [\![\varphi]\!]^{\mathcal{M}}=1,
\qquad
[\![F(\varphi)]\!]^{\mathcal{M}}=1 \iff [\![\varphi]\!]^{\mathcal{M}}=0
```

A simplifier (units, idempotence, complementation modulo negation normal form, absorption, vacuous quantification, ∃-factoring) renders results legible. On the conditional *if a king exists, the king is bald*, the strong and middle schemes yield the familiar **conditional (proviso) presupposition**, while the weak scheme projects globally:

```math
\pi_{\text{strong}}=\forall x[\neg\mathit{king}(x)\vee\neg\mathit{exist}(x)]\;\vee\;\exists z[\mathit{king}(z)\wedge\forall y(\mathit{king}(y)\rightarrow y=z)]
```

---

## 7. Alternatives and focus

F-marked constituents contribute a focus variable $z$ alongside their ordinary value, which yields a **structured meaning** $\langle B,F\rangle$ (von Stechow 1990; Krifka 1991). Equivalently, it yields the Roothian focus value $[\\![S]\\!]^f=\\{B(z)\mid z\in D_\sigma\\}$ (Rooth 1985, 1992). Focus-sensitive operators carry the flag `{focus}`, and the shipped exclusive presupposes its prejacent (Horn 1969):

```math
[\![\textit{only}]\!]=\lambda B.\lambda F:B(F).\;\forall y\,[B(y)\rightarrow y=F]\qquad B:\langle{}'a,t\rangle
```

When the background is of type $\langle\sigma_1,\ldots,\langle\sigma_n,t\rangle\rangle$, the operator is lifted pointwise. VP-*only* and S-*only* are therefore provably equivalent (`test_cross_categorial_only`). **Question–answer congruence** is decided by comparing the question abstract with the answer's background modulo $\equiv_{\alpha\beta\eta}$.

---

## 8. Generalized quantifiers and polarity

For logical determiners $Q\subseteq\wp(D)^2$, `denote universals` verifies, **exhaustively** over all $A,B\subseteq D$ with $|D|\le n$, the following properties:

```math
\begin{aligned}
\textsf{CONS}&:\ Q(A,B)\Leftrightarrow Q(A,A\cap B) &
\textsf{EXT}&:\ Q_D(A,B)\Leftrightarrow Q_{D'}(A,B)\ \ (D\subseteq D')\\
\textsf{QUANT}&:\ Q(A,B)\Leftrightarrow Q(\pi A,\pi B)\ \ (\pi\in\mathrm{Sym}(D)) &
\textsf{MON}\!\uparrow&:\ Q(A,B)\wedge B\subseteq B'\Rightarrow Q(A,B')
\end{aligned}
```

It verifies restrictor monotonicity, symmetry, intersectivity and non-triviality in the same way. Alongside these it reports a **graded monotonicity index**, $1-\#\text{violations}/\#\text{applicable pairs}$, and van Benthem's **number triangle**. The two unattested determiners violate CONS, as the universal predicts.

**Polarity.** A position is abstracted to a set-typed variable $X$, and $\lambda X.\varphi[X]$ is tested for $\varphi[A]\Rightarrow\varphi[A\cup\\{a\\}]$ (↑) and the converse (↓) over random models. With `--strawson`, pairs on which either side is undefined are discarded, which yields **Strawson entailment** (von Fintel 1999). The scope of *only* is non-monotone classically but Strawson-↓, so NPI licensing is predicted only under the Strawson notion.

---

## 9. Model-theoretic statistics

Let $\mu_{n,\theta}$ be the Bernoulli measure on interpretations of $\Sigma$ over domains of size $n$, under which each tuple enters each relation independently with probability θ. Small sizes are enumerated exhaustively. For readings $\rho_1,\ldots,\rho_k$, the following statistics are defined:

```math
\begin{aligned}
\Delta &= \mu\{\mathcal{M}:\exists i,j\ [\![\rho_i]\!]^{\mathcal{M}}\neq[\![\rho_j]\!]^{\mathcal{M}}\} && \text{scope sensitivity}\\
\delta(\rho_i,\rho_j) &= \mu\{\mathcal{M}:[\![\rho_i]\!]^{\mathcal{M}}\neq[\![\rho_j]\!]^{\mathcal{M}}\} && \text{disagreement pseudometric}\\
H &= -\textstyle\sum_{\vec v}\mu(\vec v)\log_2\mu(\vec v) && \text{entropy of the joint truth profile}\\
\rho_i\sqsubseteq\rho_j &\iff \neg\exists\mathcal{M}\,\big([\![\rho_i]\!]^{\mathcal{M}}=1\wedge[\![\rho_j]\!]^{\mathcal{M}}\neq1\big) && \text{entailment preorder (Hasse-reduced)}\\
m(\varphi)&=\mu\{\mathcal{M}:[\![\varphi]\!]^{\mathcal{M}}=1\},\quad \mathrm{inf}(\varphi)=-\log_2 m(\varphi) && \text{Bar-Hillel–Carnap informativity}
\end{aligned}
```

Equivalence classes of $\delta=0$ expose **spurious ambiguity**: derivationally distinct but truth-conditionally identical readings. By the 0–1 law for first-order logic (Glebskiĭ et al. 1969; Fagin 1976), $m_n(\varphi)\to\\{0,1\\}$ as $n\to\infty$. Every statistic here is therefore a **finite-size** quantity, and `info --profile` displays its drift.

---

## 10. Inference, coverage, competing analyses

* **Bounded entailment.** `entail` returns a FraCaS-style verdict (*yes/no/unknown*). It refutes $\Gamma\models\varphi$ by exhibiting a counter-model, and it confirms entailment only relative to exhaustive enumeration up to a size bound (exact) and random sampling beyond it. Readings export to **TPTP FOF** and **SMT-LIB 2**, with ι eliminated à la Russell, for genuine theorem proving.
* **Coverage.** `coverage` runs a lexicon over a treebank and returns the rate together with a failure taxonomy: lexical gaps, type mismatches by clashing type pair, unsupported configurations, and root-type failures.
* **Competing analyses.** `suite` scores *several lexicons* against one TOML suite of entailment items, readings counts (as model-theoretic equivalence classes), and truth-value judgements. This turns theory comparison into an executable, falsifiable artefact.
* **Teaching.** `check` grades a student's formula. It matches the formula against the derivable readings modulo $\equiv_{\alpha\beta\eta}$, falls back to bounded equivalence, and otherwise exhibits a model that separates the answer from each reading.

---

## 11. Command reference

| command | purpose |
|---|---|
| `derive` | annotated derivation (`--steps`, `--format text\|latex\|json`, `--standalone`, `--metrics`) |
| `readings` | scope readings, mechanism concordance, Δ, δ, H, Hasse diagram (`--lfs`, `--unbounded`, `--model`, `--dot`) |
| `lattice` | entailment matrix and Hasse diagram over the sentences of a `.trees` file |
| `eval` | truth values (1/0/#) in a TOML model |
| `presup` | presupposition and assertion under weak, strong, middle Kleene |
| `focus` | ordinary and focus values, structured meanings, Q–A congruence (`--question`) |
| `universals` | CONS/EXT/QUANT/monotonicity tables, graded indices, number triangles |
| `polarity` | monotonicity of a position (`--at WORD`, `--strawson`) |
| `info` | $m(\varphi)$, $\mathrm{inf}(\varphi)$, $\mathrm{cont}(\varphi)$, definedness rate (`--profile`) |
| `entail` | bounded entailment, counter-models, `--tptp`, `--smt` |
| `suite` · `coverage` · `check` | theory comparison · treebank coverage · grading |
| `lint` · `reduce` · `export` | signature and type inventory · raw β-reduction · prover export |

Global options are `--lens hk|cooper|cont`, `--shifts off|last-resort|free`, `--allow`, `--sense word=sense`, `--scheme weak|strong|middle`, `--style unicode|ascii|latex`, `--seed`, `--samples` and `--max-n`.

---

## 12. Repository layout and file formats

```
denote/
├── src/denote/
│   ├── typesys.py      simple type theory, unification, order
│   ├── terms.py        Λ: terms, capture-avoiding substitution, de Bruijn keys, printers
│   ├── parser.py       ASCII/Unicode λ-term parser (domain conditions, binders, sugar)
│   ├── typecheck.py    inference with conventional defaulting
│   ├── reduce.py       traced normal-order β/∂/η reduction
│   ├── trees.py        bracketed trees: indices, traces, binders, F/WH marking
│   ├── lexicon.py      .lex files, joint signature inference, lint
│   ├── compose.py      type-driven interpretation, type-shifting, Cooper & continuation lenses
│   ├── scope.py        QR logical forms and the four-mechanism reading pool
│   ├── models.py       models, trivalent evaluation, random/exhaustive model classes
│   ├── projection.py   bilateral translation, presupposition projection, simplifier
│   ├── analysis/       ambiguity statistics · GQ theory & polarity · metrics · inference
│   ├── render.py       text trees, LaTeX (forest + H&K equations), JSON
│   ├── export.py       TPTP FOF, SMT-LIB 2
│   └── cli.py
├── examples/           six lexicons · five tree files · two models · suite · gallery builder
│   └── output/         GALLERY.md · derivation.tex · diamond.dot
├── docs/theory/        main.tex · references.bib · main.pdf (Overleaf-ready)
└── tests/              23 regression and property tests
```

* **`.lex`** files contain entries of the form `word[sense] :: type {flags} = term`. Indented lines continue the previous entry; `%` begins a comment. The directives are `@import`, `@free x : τ` and `@title`.
* **`.trees`** files contain lines of the form `id: [S [DP every dog] [VP barks]]`. Traces and pronouns are written `t_1` and `he_2`, with an optional type annotation as in `t_3:d`; binder nodes are written `[1 …]` or `[2:d …]`; focus and wh-marking are written `Felix_F`, `[DP_F …]` and `who_WH`. Individual trees are addressed as `FILE#id`.
* **Models** (TOML) list `[domains]` (with `world =` for intensional models), `[interpretation]` and `[assignment]`. Relations are lists of tuples in application order, and functions into $D_d$ are tables.
* **Suites** (TOML) contain `[[item]]` records that hold one of three things: `premises`/`hypothesis`/`gold`, `tree`/`readings`, or `tree`/`model`/`truth`.

---

## 13. Findings reproduced by the shipped examples

| observation | command (see `GALLERY.md`) |
|---|---|
| *every student read every book*: two LFs, one equivalence class (Δ = 0), i.e. spurious ambiguity | `readings … scope.trees#ee` |
| three quantifiers: QR and storage derive all 3! = 6 readings; one-level continuations derive 4, never letting the subject take intermediate scope | `readings … scope.trees#triple` |
| inverse linking: QR, storage and continuations give only the inverse reading; AR alone gives the surface one; one storage order is ill-formed | `readings … scope.trees#inverse` |
| de re *a spy* is invisible to clause-bounded QR and continuations but derivable by storage or unbounded QR | `readings intensional.lex …#dedicto` |
| *only*'s scope: classically non-monotone, Strawson-↓ | `polarity … #onlynpi --at cat [--strawson]` |
| Frege–Strawson and Russellian articles each score 11/12, and each fails exactly the truth-value judgement the other passes | `suite extensional.lex russell.lex` |
| Davidson's diamond recovered as a Hasse diagram | `lattice events.lex events.trees` |

---

## 14. Limitations and roadmap

`denote` interprets **given** trees: it does not parse. Its models interpret first-order constants only, and higher-order meanings must be defined lexically. Entailment is **bounded**: "yes" means "no counter-model up to the bound", and exported problems should be sent to a prover for proof. The continuation lens is one-level by design, so tower-style flexibility (Barker & Shan 2014) is future work. Planned extensions include:

* dynamic semantics (DPL/CDRT) and assignment-sensitive anaphora;
* plurality and mereology (Link 1983);
* hyperintensional models;
* CCG and UD front-ends;
* Lean export for machine-checked derivations;
* experimental linking of the complexity profile (`derive --metrics`) to processing data.

**Theory and citation.** See [`docs/theory/main.tex`](docs/theory/main.tex) (build with `make theory` or upload `docs/theory/` to Overleaf) and [`CITATION.cff`](CITATION.cff). Released under the MIT licence.
