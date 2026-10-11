"""Lexicon files (.lex): typed λ-term entries, directives, global signature inference.

    % comment
    @free w : s                      a free variable (here: the evaluation world)
    @import core.lex                 include another lexicon (relative path)
    @title  …   @scheme strong       metadata
    every     :: <<e,t>,<<e,t>,t>>  = \\P.\\Q. forall x. P(x) -> Q(x)
    the[frege]                      = \\P. iota x. P(x)       sense-tagged homonym, type inferred
    only      :: <<'a,t>,<'a,t>> {focus} = \\B.\\F. B(F) & forall y. B(y) -> y = F
       (indented lines continue the previous entry)
"""
from __future__ import annotations

import re
from collections import defaultdict
from dataclasses import dataclass
from pathlib import Path

from .typesys import parse_type, resolve, order, type_str, unify, TypeClash, final
from .terms import Var, typeof, show
from .parser import parse_term, ParseError
from .typecheck import infer, retype, apply_defaults, freshen_named, SemTypeError
from .reduce import normalize


@dataclass
class Entry:
    word: str
    sense: str | None
    type: object
    term: object
    source: str
    line: int
    flags: frozenset = frozenset()

    @property
    def name(self):
        return self.word + (f"[{self.sense}]" if self.sense else "")


class LexiconError(Exception):
    pass


_ENTRY = re.compile(r"^(?P<word>[^\s\[\]:={}]+)(?:\[(?P<sense>[^\]]+)\])?\s*"
                    r"(?:::\s*(?P<type>[^={}]+?))?\s*(?:\{(?P<flags>[^}]*)\})?\s*=(?P<term>.*)$")


class Lexicon:
    def __init__(self):
        self.entries = defaultdict(list)
        self.free, self.meta, self.signature = {}, {}, {}
        self.path, self._seen = None, set()

    @classmethod
    def load(cls, path):
        lex, raw = cls(), []
        lex.path = Path(path)
        lex._read(Path(path), raw)
        lex._type(raw)
        return lex

    @classmethod
    def loads(cls, text):
        lex, raw = cls(), []
        lex._parse(text, raw, None)
        lex._type(raw)
        return lex

    def _read(self, path, raw):
        path = path.resolve()
        if path in self._seen:
            return
        self._seen.add(path)
        self._parse(path.read_text(encoding="utf-8"), raw, path)

    def _parse(self, text, raw, path):
        logical = []
        for n, line in enumerate(text.splitlines(), 1):
            body = line.split("%", 1)[0].rstrip()
            if not body.strip():
                continue
            if body[:1].isspace() and logical:
                logical[-1] = (logical[-1][0], logical[-1][1] + " " + body.strip())
            else:
                logical.append((n, body.strip()))
        where = str(path) if path else "<string>"
        for n, line in logical:
            if line.startswith("@"):
                key, _, val = line[1:].partition(" ")
                val = val.strip()
                if key == "import":
                    if path is None:
                        raise LexiconError("@import requires a file context")
                    self._read(path.parent / val, raw)
                elif key == "free":
                    name, _, ty = val.partition(":")
                    self.free[name.strip()] = Var(name.strip(), parse_type(ty.strip()))
                else:
                    self.meta[key] = val
                continue
            m = _ENTRY.match(line)
            if not m:
                raise LexiconError(f"{where}:{n}: cannot parse entry: {line}")
            raw.append((m, n, where))

    def _type(self, raw):
        sub, consts, parsed, errors = {}, {}, [], []
        for k, (m, n, where) in enumerate(raw):
            try:
                term = parse_term(m.group("term").strip(), self.free, consts)
                ty = infer(term, sub)
                if m.group("type"):
                    declared = freshen_named(parse_type(m.group("type").strip()), k)
                    try:
                        unify(ty, declared, sub)
                    except TypeClash:
                        raise SemTypeError(f"declared {type_str(declared)} but the term has type "
                                           f"{type_str(resolve(ty, sub))}")
                parsed.append((m, n, where, term))
            except (ParseError, SemTypeError, ValueError) as ex:
                errors.append(f"{where}:{n}: {m.group('word')}: {ex}")
        if errors:
            raise LexiconError("\n".join(errors))
        apply_defaults([p[3] for p in parsed], sub, list(consts.values()))
        for m, n, where, term in parsed:
            t = retype(term, sub)
            flags = frozenset(f.strip() for f in (m.group("flags") or "").split(",") if f.strip())
            self.entries[m.group("word")].append(
                Entry(m.group("word"), m.group("sense"), typeof(t), t, m.group("term").strip(), n, flags))
        self.signature = {name: resolve(c.type, sub) for name, c in consts.items()}

    def lookup(self, word, senses=None):
        es = self.entries.get(word) or self.entries.get(word.lower()) or []
        if senses and word in senses:
            es = [e for e in es if e.sense == senses[word]]
        return es

    def __len__(self):
        return sum(len(v) for v in self.entries.values())

    def lint(self):
        notes = []
        for w, es in sorted(self.entries.items()):
            for e in es:
                nf = normalize(e.term)
                if nf != e.term:
                    notes.append(("info", f"{e.name}: not β-normal; normal form {show(nf)}"))
                if order(e.type) >= 3:
                    notes.append(("info", f"{e.name}: type {type_str(e.type)} has order {order(e.type)}"))
            if len(es) > 1:
                notes.append(("info", f"{w}: {len(es)} senses ({', '.join(e.sense or '—' for e in es)})"
                                      " ⇒ lexical ambiguity multiplies derivations"))
        for c, ty in sorted(self.signature.items()):
            if order(ty) > 1:
                notes.append(("warn", f"constant {c} : {type_str(ty)} is higher-order; "
                                      "models interpret first-order constants only"))
            elif order(ty) == 1 and final(ty) != parse_type("t"):
                notes.append(("info", f"constant {c} : {type_str(ty)} is a (partial) function"))
        return notes

    def type_inventory(self):
        inv = defaultdict(list)
        for es in self.entries.values():
            for e in es:
                inv[e.type].append(e.name)
        return dict(sorted(inv.items(), key=lambda kv: (-len(kv[1]), str(kv[0]))))
