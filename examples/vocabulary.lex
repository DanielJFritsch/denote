% ───────────────────────────────────────────────────────────────────────────────
% vocabulary.lex — extensional open-class vocabulary and function words, shared by
% extensional.lex (Frege–Strawson 'the') and russell.lex (Russellian 'the').
% Relations are uncurried in application order: chase(x, y) ≡ chase(x)(y) = "x chased y";
% models list tuples in the same order.
% ───────────────────────────────────────────────────────────────────────────────
@title Extensional vocabulary

% common nouns ⟨e,t⟩
dog = \x. dog(x)
dogs = \x. dog(x)
cat = \x. cat(x)
cats = \x. cat(x)
student = \x. student(x)
students = \x. student(x)
professor = \x. professor(x)
professors = \x. professor(x)
book = \x. book(x)
books = \x. book(x)
king = \x. king(x)
boy = \x. boy(x)
country = \x. country(x)

% intersective and gradable adjectives (degrees: Cresswell 1976; Kennedy 1999)
brown = \x. brown(x)
gray = \x. gray(x)
bald = \x. bald(x)
happy = \x. happy(x)
tall = \x. height(x) > stnd                              % positive form, contextual standard
taller = \y.\x. height(x) > height(y)                    % phrasal comparative
as-tall-as = \y.\x. height(x) >= max d[height(y) >= d]   % equative via maximality

% intransitive verbs ⟨e,t⟩
barks = \x. bark(x)
bark = \x. bark(x)
sleeps = \x. sleep(x)
left = \x. leave(x)
exists = \x. exist(x)

% transitive verbs, relational nouns, prepositions ⟨e,⟨e,t⟩⟩
chased = \y.\x. chase(x, y)
read = \y.\x. read(x, y)
loves = \y.\x. love(x, y)
saw = \y.\x. see(x, y)
recommended = \y.\x. recommend(x, y)
mother = \y.\x. mother(x, y)                  % x is a mother of y
from = \y.\x. from(x, y)
in = \y.\x. in(x, y)

% ditransitive ⟨e,⟨e,⟨e,t⟩⟩⟩ for [[showed IO] DO]: x showed z to y
showed = \y.\z.\x. show(x, z, y)

% function words
is      :: <<e,t>,<e,t>> = \P. P                  % copula: semantically vacuous
than    :: <e,e>         = \x. x
of      :: <e,e>         = \x. x
who     :: <<e,t>,<e,t>> = \P. P                  % relative pronoun; its sister's λ-binder does the work
doesn't :: <<e,t>,<e,t>> = \P.\x. ~P(x)
not     :: <t,t>         = \q. ~q
if      :: <t,<t,t>>     = \q.\r. q -> r
himself :: <<e,<e,t>>,<e,t>> = \R.\x. R(x)(x)     % reflexive as arity reducer (Bach & Partee 1980)

% pronouns: φ-features as partial identity functions (Cooper 1983; Heim 2008)
he  :: <e,e> = \x : male(x) . x
him :: <e,e> = \x : male(x) . x
she :: <e,e> = \x : female(x) . x
her :: <e,e> = \x : female(x) . x
it  :: <e,e> = \x : nonhuman(x) . x

% exclusive particle with presupposed prejacent (Horn 1969), cross-categorial ('a)
only :: <<'a,t>,<'a,t>> {focus} = \B.\F : B(F) . forall y. B(y) -> y = F
