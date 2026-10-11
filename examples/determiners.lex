% ───────────────────────────────────────────────────────────────────────────────
% determiners.lex — logical determiners, Q ∈ D⟨⟨e,t⟩,⟨⟨e,t⟩,t⟩⟩
% (Barwise & Cooper 1981; Keenan & Stavi 1986; Peters & Westerståhl 2006).
% No non-logical constants occur here, so any fragment may @import this file, and
% `denote universals` can test CONS / EXT / QUANT / monotonicity exhaustively.
% ───────────────────────────────────────────────────────────────────────────────
@title Logical determiners

every        = \P.\Q. forall x. P(x) -> Q(x)
all          = \P.\Q. forall x. P(x) -> Q(x)
some         = \P.\Q. exists x. P(x) & Q(x)
a            = \P.\Q. exists x. P(x) & Q(x)
no           = \P.\Q. ~(exists x. P(x) & Q(x))
not-every    = \P.\Q. ~(forall x. P(x) -> Q(x))
most         = \P.\Q. card x[P(x) & Q(x)] > card x[P(x) & ~Q(x)]
two          = \P.\Q. card x[P(x) & Q(x)] >= 2
exactly-two  = \P.\Q. card x[P(x) & Q(x)] = 2
at-most-two  = \P.\Q. card x[P(x) & Q(x)] <= 2

% presuppositional determiners: partial functions (domain condition |P| = 2)
both         = \P : card x[P(x)] = 2 . \Q. forall x. P(x) -> Q(x)
neither      = \P : card x[P(x)] = 2 . \Q. ~(exists x. P(x) & Q(x))

% two unattested ('impossible') determiners, for contrast with the CONS universal
gleeb        = \P.\Q. forall x. Q(x) -> P(x)            % "only" as a determiner
equi         = \P.\Q. card x[P(x)] = card x[Q(x)]       % the Härtig quantifier
