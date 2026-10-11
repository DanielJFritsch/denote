% ───────────────────────────────────────────────────────────────────────────────
% intensional.lex — two-sorted type theory Ty2 (Gallin 1975) with an explicit
% evaluation-world variable w, in the style of von Fintel & Heim. Clausal
% complements combine by Intensional Functional Application.
% ───────────────────────────────────────────────────────────────────────────────
@title Intensional fragment (Ty2)
@free w : s
@import determiners.lex

the :: <<e,t>,e> = \P. iota x. P(x)

% world-relative extensions
student = \x. student(w, x)
spy = \x. spy(w, x)
unicorn = \x. unicorn(w, x)
left = \x. leave(w, x)
leave = \x. leave(w, x)
is      :: <<e,t>,<e,t>> = \P. P
that    :: <t,t> = \q. q
doesn't :: <<e,t>,<e,t>> = \P.\x. ~P(x)

% modals: quantification over accessible worlds (Kripke 1963; Kratzer 1977)
must  :: <<s,t>,t> = \p. forall v:s. acc(w, v) -> p(v)
might :: <<s,t>,t> = \p. exists v:s. acc(w, v) & p(v)

% attitude verbs (Hintikka 1969); 'know' is factive: it presupposes p(w)
believes :: <<s,t>,<e,t>> = \p.\x. forall v:s. dox(x, w, v) -> p(v)
knows = \p : p(w) . \x. forall v:s. dox(x, w, v) -> p(v)
know  = \p : p(w) . \x. forall v:s. dox(x, w, v) -> p(v)

% intensional transitive verb (Montague 1973; Zimmermann 1993): 'seek' ≈ 'try to find'
seeks = \Q.\x. forall v:s. bou(x, w, v) -> Q(v)(\y. find(v, x, y))
