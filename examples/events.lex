% events.lex — neo-Davidsonian event semantics with a severed external argument
% (Davidson 1967; Parsons 1990; Kratzer 1996). VoiceP composes by Event Identification;
% the root ⟨v,t⟩ is existentially closed.
@title Event semantics
@import determiners.lex

the :: <<e,t>,e> = \P. iota x. P(x)
knife = \x. knife(x)
toast = \x. toast(x)

Agent :: <e,<v,t>> = \x.\e. agent(e, x)      % Voice head
stabbed  = \y.\e. stab(e) & theme(e, y)
buttered = \y.\e. butter(e) & theme(e, y)
violently = \e. violent(e)
slowly    = \e. slow(e)
with = \y.\e. instr(e, y)
