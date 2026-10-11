% russell.lex — the same fragment with a quantificational, total article.
@title Extensional fragment (Russellian definites)
@import vocabulary.lex
@import determiners.lex

the = \P.\Q. exists x. P(x) & (forall y. P(y) -> y = x) & Q(x)    % Russell (1905)
