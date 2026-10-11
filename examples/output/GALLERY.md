# Gallery of sample outputs

Every block below is produced verbatim by `python examples/build_gallery.py` (or `make gallery`)
from the inputs in `examples/`. A LaTeX rendering of one derivation is in
[`derivation.tex`](derivation.tex); the entailment lattice of §14 is in [`diamond.dot`](diamond.dot).

## 1. Lexicon inspection

The type inventory and the globally inferred signature Σ of the extensional fragment.

```console
$ denote lint examples/extensional.lex
examples/extensional.lex: 63 entries, 63 words, 30 constants
type inventory:
  ⟨e,t⟩                      ord 1  dog, dogs, cat, cats, student, students, professor, professors, book, books, king, boy, country, brown, gray, bald, happy, tall, barks, bark, sleeps, left, exists
  ⟨⟨e,t⟩,⟨⟨e,t⟩,t⟩⟩          ord 2  every, all, some, a, no, not-every, most, two, exactly-two, at-most-two, both, neither, gleeb, equi
  ⟨e,⟨e,t⟩⟩                  ord 1  taller, as-tall-as, chased, read, loves, saw, recommended, mother, from, in
  ⟨e,e⟩                      ord 1  than, of, he, him, she, her, it
  ⟨⟨e,t⟩,⟨e,t⟩⟩              ord 2  is, who, doesn't
  ⟨⟨'a,t⟩,⟨'a,t⟩⟩            ord 2  only
  ⟨⟨e,⟨e,t⟩⟩,⟨e,t⟩⟩          ord 2  himself
  ⟨⟨e,t⟩,e⟩                  ord 2  the
  ⟨e,⟨e,⟨e,t⟩⟩⟩              ord 1  showed
  ⟨t,⟨t,t⟩⟩                  ord 1  if
  ⟨t,t⟩                      ord 1  not
signature Σ: bald : ⟨e,t⟩, bark : ⟨e,t⟩, book : ⟨e,t⟩, boy : ⟨e,t⟩, brown : ⟨e,t⟩, cat : ⟨e,t⟩, chase : ⟨e,⟨e,t⟩⟩, country : ⟨e,t⟩, dog : ⟨e,t⟩, exist : ⟨e,t⟩, female : ⟨e,t⟩, from : ⟨e,⟨e,t⟩⟩, gray : ⟨e,t⟩, happy : ⟨e,t⟩, height : ⟨e,d⟩, in : ⟨e,⟨e,t⟩⟩, king : ⟨e,t⟩, leave : ⟨e,t⟩, love : ⟨e,⟨e,t⟩⟩, male : ⟨e,t⟩, mother : ⟨e,⟨e,t⟩⟩, nonhuman : ⟨e,t⟩, professor : ⟨e,t⟩, read : ⟨e,⟨e,t⟩⟩, recommend : ⟨e,⟨e,t⟩⟩, see : ⟨e,⟨e,t⟩⟩, show : ⟨e,⟨e,⟨e,t⟩⟩⟩, sleep : ⟨e,t⟩, stnd : d, student : ⟨e,t⟩
  [info] constant height : ⟨e,d⟩ is a (partial) function
```

## 2. A Heim & Kratzer derivation with Predicate Abstraction

Every node shows its type, its β-normal denotation, the rule that licensed it, and (with `--steps`) each contraction.

```console
$ denote derive examples/extensional.lex examples/phenomena.trees#relative --steps
── relative: every dog who chased Felix barks
derivation 1/1
S : t   [FA]
│  ∀x[dog(x) ∧ chase(x, felix) → bark(x)]
│    = (λQ.∀x[dog(x) ∧ chase(x, felix) → Q(x)])(λx.bark(x))
│    ⇝β ∀x[dog(x) ∧ chase(x, felix) → (λx.bark(x))(x)]
│    ⇝β ∀x[dog(x) ∧ chase(x, felix) → bark(x)]
├─ DP : ⟨⟨e,t⟩,t⟩   [FA]
│  │  λQ.∀x[dog(x) ∧ chase(x, felix) → Q(x)]
│  │    = (λP.λQ.∀x[P(x) → Q(x)])(λx.dog(x) ∧ chase(x, felix))
│  │    ⇝β λQ.∀x[(λx.dog(x) ∧ chase(x, felix))(x) → Q(x)]
│  │    ⇝β λQ.∀x[dog(x) ∧ chase(x, felix) → Q(x)]
│  ├─ “every” : ⟨⟨e,t⟩,⟨⟨e,t⟩,t⟩⟩   [TN]
│  │     λP.λQ.∀x[P(x) → Q(x)]
│  └─ NP : ⟨e,t⟩   [PM]
│     │  λx.dog(x) ∧ chase(x, felix)
│     │    = λx.(λx.dog(x))(x) ∧ (λx1.chase(x1, felix))(x)
│     │    ⇝β λx.dog(x) ∧ (λx1.chase(x1, felix))(x)
│     │    ⇝β λx.dog(x) ∧ chase(x, felix)
│     ├─ “dog” : ⟨e,t⟩   [TN]
│     │     λx.dog(x)
│     └─ CP : ⟨e,t⟩   [FA]
│        │  λx1.chase(x1, felix)
│        │    = (λP.P)(λx1.chase(x1, felix))
│        │    ⇝β λx1.chase(x1, felix)
│        ├─ “who” : ⟨⟨e,t⟩,⟨e,t⟩⟩   [TN]
│        │     λP.P
│        └─ λ1 : ⟨e,t⟩   [PA]
│           │  λx1.chase(x1, felix)
│           └─ S : t   [FA]
│              │  chase(x1, felix)
│              │    = (λx.chase(x, felix))(x1)
│              │    ⇝β chase(x1, felix)
│              ├─ “t_1” : e   [TN]  — Traces & Pronouns: g(1) = x1
│              │     x1
│              └─ VP : ⟨e,t⟩   [FA]
│                 │  λx.chase(x, felix)
│                 │    = (λy.λx.chase(x, y))(felix)
│                 │    ⇝β λx.chase(x, felix)
│                 ├─ “chased” : ⟨e,⟨e,t⟩⟩   [TN]
│                 │     λy.λx.chase(x, y)
│                 └─ “Felix” : e   [TN*]  — proper name (automatic entry)
│                       felix
└─ VP : ⟨e,t⟩   [NN]
   │  λx.bark(x)
   └─ “barks” : ⟨e,t⟩   [TN]
         λx.bark(x)
```

## 3. Type mismatch, diagnosis, and last-resort repair

With type-shifting disabled the object quantifier is uninterpretable in situ; the diagnosis proposes repairs. With the default economy setting, Hendriks's argument raising applies.

```console
$ denote derive examples/extensional.lex examples/phenomena.trees#objquant --shifts off
── objquant: Rex chased every cat
✗ no derivation reaches type t
  [type mismatch] at VP: chased : ⟨e,⟨e,t⟩⟩ and DP : ⟨⟨e,t⟩,t⟩ do not compose
      ↳ try: QR the quantificational DP (readings --method qr) or use --lens cooper|cont
      ↳ try: argument raising (AR) with --shifts last-resort
```

```console
$ denote derive examples/extensional.lex examples/phenomena.trees#copula
── copula: Rex is a dog
derivation 1/1   type-shifts: BE
S : t   [FA]
│  ∃x'[dog(x') ∧ x' = rex]
├─ “Rex” : e   [TN*]  — proper name (automatic entry)
│     rex
└─ VP : ⟨e,t⟩   [FA]
   │  λx.∃x'[dog(x') ∧ x' = x]
   ├─ “is” : ⟨⟨e,t⟩,⟨e,t⟩⟩   [TN]
   │     λP.P
   └─ DP : ⟨e,t⟩   [BE]  — type shift BE
      │  λx.∃x'[dog(x') ∧ x' = x]
      └─ DP : ⟨⟨e,t⟩,t⟩   [FA]
         │  λQ.∃x[dog(x) ∧ Q(x)]
         ├─ “a” : ⟨⟨e,t⟩,⟨⟨e,t⟩,t⟩⟩   [TN]
         │     λP.λQ.∃x[P(x) ∧ Q(x)]
         └─ “dog” : ⟨e,t⟩   [TN]
               λx.dog(x)
```

## 4. Scope: four mechanisms, one concordance

Readings are pooled modulo α/βη and annotated with the mechanisms that derive them; model-theoretic statistics follow.

```console
$ denote readings examples/extensional.lex examples/scope.trees#ea --lfs
sentence: every student read a book
mechanisms: qr, cooper, cont, ar   distinct readings modulo α/βη: 2

ρ1  ∀x[student(x) → ∃x'[book(x') ∧ read(x, x')]]
ρ2  ∃x[book(x) ∧ ∀x'[student(x') → read(x', x)]]

mechanism concordance (✓ = derivable)
         qr    cooper   cont     ar   
ρ1       ✓       ✓       ✓       ✓    
ρ2       ✓       ✓       ✓       ✓    
derivation counts: qr=2, cooper=2, cooper_ill_formed=0, cont=2, ar=2

logical forms (QR):
  [surface]  [S [DP every student] [VP read [DP a book]]]
  [every student ≫ a book]  [S [DP every student] [2 [S [DP a book] [1 [S t_2 [VP read t_1]]]]]]
  [a book ≫ every student]  [S [DP a book] [2 [S [DP every student] [1 [S t_1 [VP read t_2]]]]]]

model-theoretic profile over 564 models (exhaustive where ≤ 4096 per size):
  equivalence classes: {ρ1}  {ρ2}
  scope sensitivity Δ = 0.069    profile entropy H = 1.294 bits
  disagreement δ(ρi,ρj):
    ρ1  0.000 0.069
    ρ2  0.069 0.000
  m(ρi) = ρ1: 0.537, ρ2: 0.468
  entailment (Hasse): ρ2 ⊨ ρ1
  weakest: ρ1    strongest: ρ2
```

## 5. Spurious ambiguity

Two derivationally distinct LFs that collapse into one model-theoretic equivalence class (Δ = 0).

```console
$ denote readings examples/extensional.lex examples/scope.trees#ee
sentence: every student read every book
mechanisms: qr, cooper, cont, ar   distinct readings modulo α/βη: 2

ρ1  ∀x[student(x) → ∀x'[book(x') → read(x, x')]]
ρ2  ∀x[book(x) → ∀x'[student(x') → read(x', x)]]

mechanism concordance (✓ = derivable)
         qr    cooper   cont     ar   
ρ1       ✓       ✓       ✓       ✓    
ρ2       ✓       ✓       ✓       ✓    
derivation counts: qr=2, cooper=2, cooper_ill_formed=0, cont=2, ar=2

model-theoretic profile over 564 models (exhaustive where ≤ 4096 per size):
  equivalence classes: {ρ1,ρ2}
  scope sensitivity Δ = 0.000    profile entropy H = 0.997 bits
  disagreement δ(ρi,ρj):
    ρ1  0.000 0.000
    ρ2  0.000 0.000
  m(ρi) = ρ1: 0.468, ρ2: 0.468
  entailment (Hasse): none (logically independent)
  weakest: ρ1    strongest: ρ1
```

## 6. Three quantifiers: where the mechanisms part ways

QR and Cooper storage derive all 3! orders; one-level continuations cannot let the subject take intermediate scope.

```console
$ denote readings examples/extensional.lex examples/scope.trees#triple
sentence: every student showed a professor two books
mechanisms: qr, cooper, cont, ar   distinct readings modulo α/βη: 6

ρ1  ∀x[student(x) → ∃x'[professor(x') ∧ card x''[book(x'') ∧ show(x, x'', x')] ≥ 2]]
ρ2  ∀x[student(x) → card x'[book(x') ∧ ∃x''[professor(x'') ∧ show(x, x', x'')]] ≥ 2]
ρ3  ∃x[professor(x) ∧ ∀x'[student(x') → card x''[book(x'') ∧ show(x', x'', x)] ≥ 2]]
ρ4  ∃x[professor(x) ∧ card x'[book(x') ∧ ∀x''[student(x'') → show(x'', x', x)]] ≥ 2]
ρ5  card x[book(x) ∧ ∀x'[student(x') → ∃x''[professor(x'') ∧ show(x', x, x'')]]] ≥ 2
ρ6  card x[book(x) ∧ ∃x'[professor(x') ∧ ∀x''[student(x'') → show(x'', x, x')]]] ≥ 2

mechanism concordance (✓ = derivable)
         qr    cooper   cont     ar   
ρ1       ✓       ✓       ✓       ·    
ρ2       ✓       ✓       ✓       ·    
ρ3       ✓       ✓       ·       ·    
ρ4       ✓       ✓       ✓       ·    
ρ5       ✓       ✓       ·       ·    
ρ6       ✓       ✓       ✓       ·    
derivation counts: qr=6, cooper=6, cooper_ill_formed=0, cont=4, ar=0

model-theoretic profile over 466 models (exhaustive where ≤ 4096 per size):
  equivalence classes: {ρ1}  {ρ2}  {ρ3}  {ρ4}  {ρ5}  {ρ6}
  scope sensitivity Δ = 0.163    profile entropy H = 1.549 bits
  disagreement δ(ρi,ρj):
    ρ1  0.000 0.028 0.041 0.135 0.135 0.139
    ρ2  0.028 0.000 0.069 0.163 0.112 0.146
    ρ3  0.041 0.069 0.000 0.094 0.137 0.107
    ρ4  0.135 0.163 0.094 0.000 0.052 0.017
    ρ5  0.135 0.112 0.137 0.052 0.000 0.034
    ρ6  0.139 0.146 0.107 0.017 0.034 0.000
  m(ρi) = ρ1: 0.281, ρ2: 0.309, ρ3: 0.240, ρ4: 0.146, ρ5: 0.197, ρ6: 0.163
  entailment (Hasse): ρ1 ⊨ ρ2, ρ3 ⊨ ρ1, ρ4 ⊨ ρ3, ρ4 ⊨ ρ6, ρ5 ⊨ ρ2, ρ6 ⊨ ρ5
  weakest: ρ2    strongest: ρ4
```

## 7. Inverse linking and the free-variable problem of storage

Only argument raising yields the surface (narrow) reading; one Cooper retrieval order is discarded as ill-formed (Keller 1988).

```console
$ denote readings examples/extensional.lex examples/scope.trees#inverse
sentence: a student from every country left
mechanisms: qr, cooper, cont, ar   distinct readings modulo α/βη: 2

ρ1  ∀x[country(x) → ∃x'[student(x') ∧ from(x', x) ∧ leave(x')]]
ρ2  ∃x[student(x) ∧ ∀x'[country(x') → from(x, x')] ∧ leave(x)]

mechanism concordance (✓ = derivable)
         qr    cooper   cont     ar   
ρ1       ✓       ✓       ✓       ·    
ρ2       ·       ·       ·       ✓    
derivation counts: qr=1, cooper=1, cooper_ill_formed=1, cont=1, ar=1

model-theoretic profile over 1340 models (exhaustive where ≤ 4096 per size):
  equivalence classes: {ρ1}  {ρ2}
  scope sensitivity Δ = 0.129    profile entropy H = 1.320 bits
  disagreement δ(ρi,ρj):
    ρ1  0.000 0.129
    ρ2  0.129 0.000
  m(ρi) = ρ1: 0.388, ρ2: 0.259
  entailment (Hasse): ρ2 ⊨ ρ1
  weakest: ρ1    strongest: ρ2
```

## 8. De re / de dicto

Clause-bounded QR yields only the de dicto reading; storage, or unbounded QR, adds de re. Both readings are evaluated in a Kripke model.

```console
$ denote readings examples/intensional.lex examples/intensional.trees#dedicto --model examples/kripke.toml
sentence: John believes that a spy left
mechanisms: qr, cooper, cont, ar   distinct readings modulo α/βη: 2

ρ1  ∀v[dox(john, w, v) → ∃x[spy(v, x) ∧ leave(v, x)]]
ρ2  ∃x[spy(w, x) ∧ ∀v[dox(john, w, v) → leave(v, x)]]

mechanism concordance (✓ = derivable)
         qr    cooper   cont     ar   
ρ1       ✓       ✓       ✓       ✓    
ρ2       ·       ✓       ·       ·    
derivation counts: qr=2, cooper=2, cooper_ill_formed=0, cont=1, ar=1

truth values in examples/kripke.toml: ρ1 = 1, ρ2 = 0

model-theoretic profile over 458 models (exhaustive where ≤ 4096 per size):
  equivalence classes: {ρ1}  {ρ2}
  scope sensitivity Δ = 0.210    profile entropy H = 1.739 bits
  disagreement δ(ρi,ρj):
    ρ1  0.000 0.210
    ρ2  0.210 0.000
  m(ρi) = ρ1: 0.504, ρ2: 0.483
  entailment (Hasse): none (logically independent)
  weakest: ρ1, ρ2    strongest: ρ1, ρ2
```

```console
$ denote readings examples/intensional.lex examples/intensional.trees#dedicto --unbounded --method qr
sentence: John believes that a spy left
mechanisms: qr   (QR unbounded)   distinct readings modulo α/βη: 2

ρ1  ∀v[dox(john, w, v) → ∃x[spy(v, x) ∧ leave(v, x)]]
ρ2  ∃x[spy(w, x) ∧ ∀v[dox(john, w, v) → leave(v, x)]]

mechanism concordance (✓ = derivable)
         qr   
ρ1       ✓    
ρ2       ✓    
derivation counts: qr=2

model-theoretic profile over 458 models (exhaustive where ≤ 4096 per size):
  equivalence classes: {ρ1}  {ρ2}
  scope sensitivity Δ = 0.210    profile entropy H = 1.739 bits
  disagreement δ(ρi,ρj):
    ρ1  0.000 0.210
    ρ2  0.210 0.000
  m(ρi) = ρ1: 0.504, ρ2: 0.483
  entailment (Hasse): none (logically independent)
  weakest: ρ1, ρ2    strongest: ρ1, ρ2
```

## 9. Presupposition projection under three trivalent schemes

The proviso problem (conditional presupposition), universal projection from a quantifier, and factivity under negation.

```console
$ denote presup examples/extensional.lex examples/phenomena.trees#cond
sentence: if a king exists the king is bald
meaning : ∃x[king(x) ∧ exist(x)] → bald(ιx[king(x)])

[ weak ] presupposition π = ∃z[king(z) ∧ ∀y[king(y) → y = z]]
         assertion      α = ∃z[king(z) ∧ ∀y[king(y) → y = z]] ∧ (∀x[¬(king(x) ∧ exist(x))] ∨ ∃z[king(z) ∧ ∀y[king(y) → y = z] ∧ bald(z)])
[strong] presupposition π = ∀x[¬king(x) ∨ ¬exist(x)] ∨ ∃z[king(z) ∧ ∀y[king(y) → y = z]]
         assertion      α = ∀x[¬king(x) ∨ ¬exist(x)] ∨ ∃z[king(z) ∧ ∀y[king(y) → y = z] ∧ bald(z)]
[middle] presupposition π = ∀x[¬king(x) ∨ ¬exist(x)] ∨ ∃z[king(z) ∧ ∀y[king(y) → y = z]]
         assertion      α = ∀x[¬king(x) ∨ ¬exist(x)] ∨ ∃z[king(z) ∧ ∀y[king(y) → y = z] ∧ bald(z)]
```

```console
$ denote presup examples/extensional.lex examples/phenomena.trees#bound
sentence: every boy loves the mother of him
meaning : ∀x[boy(x) → love(x, ιx'[∂[male(x)] mother(x', x)])]

[ weak ] presupposition π = ∀x[∃z[male(x) ∧ mother(z, x) ∧ ∀y[male(x) ∧ mother(y, x) → y = z]]]
         assertion      α = ∀x[∃z[male(x) ∧ mother(z, x) ∧ ∀y[male(x) ∧ mother(y, x) → y = z]] ∧ (¬boy(x) ∨ ∃z[male(x) ∧ mother(z, x) ∧ ∀y[male(x) ∧ mother(y, x) → y = z] ∧ love(x, z)])]
[strong] presupposition π = ∀x[¬boy(x) ∨ ∃z[male(x) ∧ mother(z, x) ∧ ∀y[male(x) ∧ mother(y, x) → y = z] ∧ love(x, z)]] ∨ ∃x[boy(x) ∧ ∃z[male(x) ∧ mother(z, x) ∧ ∀y[male(x) ∧ mother(y, x) → y = z] ∧ ¬love(x, z)]]
         assertion      α = ∀x[¬boy(x) ∨ ∃z[male(x) ∧ mother(z, x) ∧ ∀y[male(x) ∧ mother(y, x) → y = z] ∧ love(x, z)]]
[middle] presupposition π = ∀x[¬boy(x) ∨ ∃z[male(x) ∧ mother(z, x) ∧ ∀y[male(x) ∧ mother(y, x) → y = z] ∧ love(x, z)]] ∨ ∃x[boy(x) ∧ ∃z[male(x) ∧ mother(z, x) ∧ ∀y[male(x) ∧ mother(y, x) → y = z] ∧ ¬love(x, z)]]
         assertion      α = ∀x[¬boy(x) ∨ ∃z[male(x) ∧ mother(z, x) ∧ ∀y[male(x) ∧ mother(y, x) → y = z] ∧ love(x, z)]]
```

```console
$ denote presup examples/intensional.lex examples/intensional.trees#negfactive
sentence: John doesn't know that Mary left
meaning : ¬∂[leave(w, mary)] ∀v[dox(john, w, v) → leave(v, mary)]

[ weak ] presupposition π = leave(w, mary)
         assertion      α = leave(w, mary) ∧ ∃v[dox(john, w, v) ∧ ¬leave(v, mary)]
[strong] presupposition π = leave(w, mary)
         assertion      α = leave(w, mary) ∧ ∃v[dox(john, w, v) ∧ ¬leave(v, mary)]
[middle] presupposition π = leave(w, mary)
         assertion      α = leave(w, mary) ∧ ∃v[dox(john, w, v) ∧ ¬leave(v, mary)]
```

## 10. Focus, alternatives, and question–answer congruence

```console
$ denote focus examples/extensional.lex examples/phenomena.trees#vponly
sentence: Rex only chased Felix
ordinary value  ⟦S⟧° = ∂[chase(rex, felix)] ∀y[chase(rex, y) → y = felix]
focus operator: association with focus: B = λz1.chase(x, z1), F = felix
```

```console
$ denote focus examples/extensional.lex examples/phenomena.trees#answer --question examples/phenomena.trees#question
question abstract  λz.Q = λz1.chase(rex, z1)
answer background  λz.B = λz1.chase(rex, z1)
Q–A congruence (Rooth 1992: ⟦Q⟧ ⊆ ⟦A⟧^f): ✓ congruent
```

```console
$ denote focus examples/extensional.lex examples/phenomena.trees#wrongfocus --question examples/phenomena.trees#question
question abstract  λz.Q = λz1.chase(rex, z1)
answer background  λz.B = λz1.chase(z1, felix)
Q–A congruence (Rooth 1992: ⟦Q⟧ ⊆ ⟦A⟧^f): ✗ incongruent
```

## 11. Generalized-quantifier universals

Exhaustive verification over |D| ≤ 4, with graded monotonicity and van Benthem number triangles.

```console
$ denote universals examples/determiners.lex
generalized-quantifier properties, exhaustive over all A, B ⊆ D with |D| ≤ 4

determiner      CONS   EXT QUANT  MON↑  MON↓  ↑MON  ↓MON   SYM   INT NTRIV   graded MON↑/MON↓
a                  ✓     ✓     ✓     ✓     ✗     ✓     ✗     ✓     ✓     ✓   1.00/0.71
all                ✓     ✓     ✓     ✓     ✗     ✗     ✓     ✗     ✗     ✓   1.00/0.50
at-most-two        ✓     ✓     ✓     ✗     ✓     ✗     ✓     ✓     ✓     ✓   0.94/1.00
both               ✓     ✓     ✓     ✓     ✗     ✗     ✗     ✗     ✗     ✓   1.00/0.30
equi               ✗     ✓     ✓     ✗     ✗     ✗     ✗     ✓     ✗     ✓   0.00/0.00
every              ✓     ✓     ✓     ✓     ✗     ✗     ✓     ✗     ✗     ✓   1.00/0.50
exactly-two        ✓     ✓     ✓     ✗     ✗     ✗     ✗     ✓     ✓     ✓   0.50/0.23
gleeb              ✗     ✓     ✓     ✗     ✓     ✓     ✗     ✗     ✗     ✓   0.50/1.00
most               ✓     ✓     ✓     ✓     ✗     ✗     ✗     ✗     ✗     ✓   1.00/0.43
neither            ✓     ✓     ✓     ✗     ✓     ✗     ✗     ✗     ✗     ✓   0.30/1.00
no                 ✓     ✓     ✓     ✗     ✓     ✗     ✓     ✓     ✓     ✓   0.50/1.00
not-every          ✓     ✓     ✓     ✗     ✓     ✓     ✗     ✗     ✗     ✓   0.71/1.00
some               ✓     ✓     ✓     ✓     ✗     ✓     ✗     ✓     ✓     ✓   1.00/0.71
two                ✓     ✓     ✓     ✓     ✗     ✓     ✗     ✓     ✓     ✓   1.00/0.40

MON↑/MON↓ = scope (right) monotonicity; ↑MON/↓MON = restrictor (left) monotonicity;
graded = 1 − proportion of monotonicity violations among applicable pairs
```

```console
$ denote universals examples/determiners.lex --det most,both --triangle 4
generalized-quantifier properties, exhaustive over all A, B ⊆ D with |D| ≤ 4

determiner      CONS   EXT QUANT  MON↑  MON↓  ↑MON  ↓MON   SYM   INT NTRIV   graded MON↑/MON↓
both               ✓     ✓     ✓     ✓     ✗     ✗     ✗     ✗     ✗     ✓   1.00/0.30
most               ✓     ✓     ✓     ✓     ✗     ✗     ✗     ✗     ✗     ✓   1.00/0.43

MON↑/MON↓ = scope (right) monotonicity; ↑MON/↓MON = restrictor (left) monotonicity;
graded = 1 − proportion of monotonicity violations among applicable pairs

number triangle for 'both' (van Benthem 1986):
|A|=0      #
|A|=1     # #
|A|=2    − − +
|A|=3   # # # #
|A|=4  # # # # #
        (left: |A∩B| = 0 … right: |A∩B| = |A|)

number triangle for 'most' (van Benthem 1986):
|A|=0      −
|A|=1     − +
|A|=2    − − +
|A|=3   − − + +
|A|=4  − − − + +
        (left: |A∩B| = 0 … right: |A∩B| = |A|)
```

## 12. Polarity: classical versus Strawson entailment

Positions are abstracted and tested for monotonicity; *only* is non-monotone classically but Strawson-downward-entailing.

```console
$ denote polarity examples/extensional.lex examples/phenomena.trees#quant --at dog
sentence: every dog barks
position 'dog' abstracted, X : ⟨e,t⟩:  λX.∀x[X(x) → bark(x)]
polarity: ↓ downward entailing   {'tested': 231, '↑-violations': 67, '↓-violations': 0}
NPI prediction (Fauconnier 1975; Ladusaw 1979): 'any'/'ever' licensed in this position
```

```console
$ denote polarity examples/extensional.lex examples/phenomena.trees#onlynpi --at cat
sentence: only Rex chased some cat
position 'cat' abstracted, X : ⟨e,t⟩:  λX : ∃x'[X(x') ∧ chase(rex, x')] . ∀y[∃x'[X(x') ∧ chase(y, x')] → y = rex]
polarity: non-monotone   {'tested': 248, '↑-violations': 22, '↓-violations': 22}
NPI prediction (Fauconnier 1975; Ladusaw 1979): 'any'/'ever' not licensed in this position
```

```console
$ denote polarity examples/extensional.lex examples/phenomena.trees#onlynpi --at cat --strawson
sentence: only Rex chased some cat
position 'cat' abstracted, X : ⟨e,t⟩:  λX : ∃x'[X(x') ∧ chase(rex, x')] . ∀y[∃x'[X(x') ∧ chase(y, x')] → y = rex]
Strawson-polarity: ↓ downward entailing   {'tested': 112, '↑-violations': 22, '↓-violations': 0, 'skipped (undefined)': 136}
NPI prediction (Fauconnier 1975; Ladusaw 1979; von Fintel 1999): 'any'/'ever' licensed in this position
```

## 13. Informativity and the 0–1 law

Bar-Hillel–Carnap measures, and finite-size profiles that drift toward 0 or 1 as domains grow.

```console
$ denote info examples/extensional.lex "[S [DP every dog] [VP barks]]" --profile
tree: every dog barks
   ∀x[dog(x) → bark(x)]
   models = 340   m(φ) = 0.353   inf(φ) bits = 1.503   cont(φ) = 0.647   P(defined) = 1.000
   finite-size profile m_n(φ): n=1:0.76  n=2:0.56  n=3:0.40  n=4:0.34  n=5:0.20  n=6:0.18  n=8:0.10
```

```console
$ denote info examples/extensional.lex "[S [DP some dog] [VP barks]]" --profile
tree: some dog barks
   ∃x[dog(x) ∧ bark(x)]
   models = 340   m(φ) = 0.647   inf(φ) bits = 0.628   cont(φ) = 0.353   P(defined) = 1.000
   finite-size profile m_n(φ): n=1:0.24  n=2:0.47  n=3:0.54  n=4:0.70  n=5:0.74  n=6:0.82  n=8:0.91
```

## 14. Davidson's diamond

An entailment lattice over event-semantic sentences.

```console
$ denote lattice examples/events.lex examples/events.trees --dot examples/output/diamond.dot
d1       Brutus Agent stabbed Caesar
         ∃e[agent(e, brutus) ∧ stab(e) ∧ theme(e, caesar)]
d2       Brutus Agent stabbed Caesar violently
         ∃e[agent(e, brutus) ∧ stab(e) ∧ theme(e, caesar) ∧ violent(e)]
d3       Brutus Agent stabbed Caesar with the knife
         ∃e[agent(e, brutus) ∧ stab(e) ∧ theme(e, caesar) ∧ instr(e, ιx[knife(x)])]
d4       Brutus Agent stabbed Caesar violently with the knife
         ∃e[agent(e, brutus) ∧ stab(e) ∧ theme(e, caesar) ∧ violent(e) ∧ instr(e, ιx[knife(x)])]

entailment matrix over 514 models (row ⊨ column):
           d1      d2      d3      d4   
d1         ⊨       ·       ·       ·    
d2         ⊨       ⊨       ·       ·    
d3         ⊨       ·       ⊨       ·    
d4         ⊨       ⊨       ⊨       ⊨    
Hasse diagram: d2 ⊨ d1, d3 ⊨ d1, d4 ⊨ d2, d4 ⊨ d3
m(φ): d1 = 0.294, d2 = 0.148, d3 = 0.056, d4 = 0.023
DOT written to examples/output/diamond.dot
```

## 15. Bounded entailment with counter-models and prover export

```console
$ denote entail examples/extensional.lex --premise "[S [DP every dog] [VP barks]]" --premise "[S Rex [VP is [DP a dog]]]" --hypothesis "[S Rex [VP barks]]" --tptp --smt
P1: ∀x[dog(x) → bark(x)]
P2: ∃x'[dog(x') ∧ x' = rex]
H : bark(rex)
verdict: yes   (1252 models; exhaustive up to |D| = 4)

% TPTP FOF
fof(p1, axiom, ![X0]: ((dog(X0) => bark(X0)))).
fof(p2, axiom, ?[X0]: ((dog(X0) & (X0 = rex)))).
fof(h, conjecture, bark(rex)).

; SMT-LIB 2
(set-logic ALL)
(declare-sort E 0)
(declare-fun bark (E) Bool)
(declare-fun dog (E) Bool)
(declare-fun rex () E)
(assert (forall ((v0 E)) (=> (dog v0) (bark v0))))
(assert (exists ((v0 E)) (and (dog v0) (= v0 rex))))
(assert (not (bark rex)))   ; unsat ⇔ premises ⊨ hypothesis
(check-sat)
```

```console
$ denote entail examples/extensional.lex --premise "[S [DP some dog] [VP barks]]" --hypothesis "[S [DP every dog] [VP barks]]"
P1: ∃x[dog(x) ∧ bark(x)]
H : ∀x[dog(x) → bark(x)]
verdict: unknown   (18 models; exhaustive up to |D| = 2)
counter-model (premises true, hypothesis not true):
  domains: D_e = {a, b}
    I(bark) = {a}
    I(dog) = {a, b}
```

## 16. Competing analyses scored side by side

Frege–Strawson versus Russellian definites on one suite.

```console
$ denote suite examples/extensional.lex examples/russell.lex --suite examples/suite.toml
denote mini-suite: entailment, ambiguity, truth-value judgements

item              gold     extensional.lex     russell.lex         
nli-every-mp      yes      ✓ yes               ✓ yes               
nli-every-down    yes      ✓ yes               ✓ yes               
nli-some-up       yes      ✓ yes               ✓ yes               
nli-no-contra     no       ✓ no                ✓ no                
nli-some-every    unknown  ✓ unknown           ✓ unknown           
nli-most-some     yes      ✓ yes               ✓ yes               
nli-the-some      yes      ✓ yes               ✓ yes               
amb-every-a       2        ✓ 2                 ✓ 2                 
amb-every-every   1        ✓ 1                 ✓ 1                 
tvj-king          #        ✓ #                 ✗ 0                 
tvj-not-king      1        ✗ #                 ✓ 1                 
tvj-every-dog     1        ✓ 1                 ✓ 1                 

accuracy: extensional.lex: 11/12 = 0.92   russell.lex: 11/12 = 0.92
notes:
  nli-every-down: every is ↓ in its restrictor
  amb-every-every: two LFs, one truth condition: spurious ambiguity
  tvj-king: Strawsonian gap: speakers judge neither true nor false (cf. von Fintel 2004)
  tvj-not-king: 'it is not the case that the king is bald' read with wide-scope negation: true
```

## 17. Corpus coverage and failure taxonomy

```console
$ denote coverage examples/extensional.lex examples/corpus.trees
coverage: 11/18 = 61.1%
  ✓ c01    1 derivation(s)
  ✓ c02    2 derivation(s)
  ✓ c03    1 derivation(s)
  ✓ c04    1 derivation(s)
  ✓ c05    1 derivation(s)
  ✓ c06    1 derivation(s)
  ✓ c07    1 derivation(s)
  ✗ c08    0 derivation(s)   ← no lexical entry for 'loudly'
  ✗ c09    0 derivation(s)   ← 3-ary branching at VP
  ✗ c10    0 derivation(s)   ← root has type ⟨⟨e,t⟩,t⟩, not t
  ✗ c11    0 derivation(s)   ← no lexical entry for 'garden'
  ✓ c12    1 derivation(s)
  ✓ c13    1 derivation(s)
  ✗ c14    0 derivation(s)   ← no lexical entry for 'each'
  ✓ c15    1 derivation(s)
  ✓ c16    1 derivation(s)
  ✗ c17    0 derivation(s)   ← no lexical entry for 'mouse'
  ✗ c18    0 derivation(s)   ← no lexical entry for 'yesterday'
lexical gaps: loudly ×1, garden ×1, each ×1, mouse ×1, yesterday ×1
```

## 18. Grading a student's formula

```console
$ denote check examples/extensional.lex examples/scope.trees#ea --answer "exists y. book(y) & forall x. student(x) -> read(x, y)"
sentence: every student read a book
answer  : ∃y[book(y) ∧ ∀x[student(x) → read(x, y)]]
✓ identical (modulo α/βη) to reading ρ2
```

```console
$ denote check examples/extensional.lex examples/scope.trees#ea --answer "forall y. book(y) -> exists x. student(x) & read(x, y)"
sentence: every student read a book
answer  : ∀y[book(y) → ∃x[student(x) ∧ read(x, y)]]
✗ matches no derivable reading
  ρ1: ∀x[student(x) → ∃x'[book(x') ∧ read(x, x')]]
      answer ⊨ ρ1? unknown
      model separating them:
        domains: D_e = {a}
          I(book) = {}
          I(read) = {}
          I(student) = {a}
  ρ2: ∃x[book(x) ∧ ∀x'[student(x') → read(x', x)]]
      answer ⊨ ρ2? unknown
      model separating them:
        domains: D_e = {a}
          I(book) = {}
          I(read) = {}
          I(student) = {}
```

## 19. Truth in a model and derivational complexity

```console
$ denote eval examples/extensional.lex examples/phenomena.trees --model examples/world.toml
fa           1   bark(rex)
pm           1   bark(ιx[brown(x) ∧ dog(x)])
quant        1   ∀x[dog(x) → bark(x)]
relative     1   ∀x[dog(x) ∧ chase(x, felix) → bark(x)]
objrel       #   sleep(ιx[cat(x) ∧ chase(rex, x)])
vpneg        0   ¬bark(rex)
sneg         #   ¬bald(ιx[king(x)])
copula       1   ∃x'[dog(x') ∧ x' = rex]
adjpred      1   brown(rex)
reflexive    1   chase(rex, rex)
coordvp      0   bark(rex) ∧ sleep(rex)
coordname    0   leave(rex) ∧ leave(felix)
coordmix     0   leave(rex) ∧ ∀x[cat(x) → leave(x)]
coordgq      1   ∀x[dog(x) → leave(x)] ∨ ∃x[cat(x) ∧ leave(x)]
objquant     1   ∀x'[cat(x') → chase(rex, x')]
pronoun      0   ∂[male(x1)] leave(x1)
bound        1   ∀x[boy(x) → love(x, ιx'[∂[male(x)] mother(x', x)])]
both         1   ∂[card x[dog(x)] = 2] ∀x[dog(x) → bark(x)]
cond         1   ∃x[king(x) ∧ exist(x)] → bald(ιx[king(x)])
only         0   ∂[chase(rex, felix)] ∀y[chase(rex, y) → y = felix]
vponly       0   ∂[chase(rex, felix)] ∀y[chase(rex, y) → y = felix]
subjonly     0   ∂[chase(rex, felix)] ∀y[chase(y, felix) → y = rex]
onlynpi      0   ∂[∃x'[cat(x') ∧ chase(rex, x')]] ∀y[∃x'[cat(x') ∧ chase(y, x')] → y = rex]
answer       1   chase(rex, felix)
wrongfocus   1   chase(rex, felix)
question     !  (free variable z1 has no value (add it under [assignment])) chase(rex, z1)
comparative  1   height(ann) > height(bo)
equative     1   height(ann) ≥ max d[height(bo) ≥ d]
positive     1   height(ann) > stnd
mismatch     —   (no derivation)
```

```console
$ denote derive examples/extensional.lex examples/phenomena.trees#bound --metrics
── bound: every boy loves the mother of him
derivation 1/1
S : t   [FA]
│  ∀x[boy(x) → love(x, ιx'[∂[male(x)] mother(x', x)])]
├─ DP : ⟨⟨e,t⟩,t⟩   [FA]
│  │  λQ.∀x[boy(x) → Q(x)]
│  ├─ “every” : ⟨⟨e,t⟩,⟨⟨e,t⟩,t⟩⟩   [TN]
│  │     λP.λQ.∀x[P(x) → Q(x)]
│  └─ “boy” : ⟨e,t⟩   [TN]
│        λx.boy(x)
└─ λ1 : ⟨e,t⟩   [PA]
   │  λx1.love(x1, ιx[∂[male(x1)] mother(x, x1)])
   └─ S : t   [FA]
      │  love(x1, ιx[∂[male(x1)] mother(x, x1)])
      ├─ “t_1” : e   [TN]  — Traces & Pronouns: g(1) = x1
      │     x1
      └─ VP : ⟨e,t⟩   [FA]
         │  λx.love(x, ιx[∂[male(x1)] mother(x, x1)])
         ├─ “loves” : ⟨e,⟨e,t⟩⟩   [TN]
         │     λy.λx.love(x, y)
         └─ DP : e   [FA]
            │  ιx[∂[male(x1)] mother(x, x1)]
            ├─ “the” : ⟨⟨e,t⟩,e⟩   [TN]
            │     λP.ιx[P(x)]
            └─ NP : ⟨e,t⟩   [FA]
               │  λx : male(x1) . mother(x, x1)
               ├─ “mother” : ⟨e,⟨e,t⟩⟩   [TN]
               │     λy.λx.mother(x, y)
               └─ PP : e   [FA]
                  │  ∂[male(x1)] x1
                  ├─ “of” : ⟨e,e⟩   [TN]
                  │     λx.x
                  └─ “him_1” : e   [TN]  — pronoun: φ-features as partial identity
                        ∂[male(x1)] x1
                nodes: 16
              β-steps: 11
              ∂-steps: 1
          type-shifts: 0
       max type order: 2
       max redex size: 25
     normal-form size: 19
     quantifier depth: 2
                rules: {'FA': 7, 'TN': 8, 'PA': 1}
```

## 20. Raw λ-calculus: normal-order reduction with α-conversion

```console
$ denote reduce "(\R.\x.\y. R(y)(x))(\x.\y. love(x, y))"
   (λR.λx.λy.R(y)(x))(λx.λy.love(x, y))   : ⟨e,⟨e,t⟩⟩
⇝β λx.λy.(λx.λy.love(x, y))(y)(x)
⇝β λx.λy.(λy'.love(y, y'))(x)
⇝β λx.λy.love(y, x)
```
