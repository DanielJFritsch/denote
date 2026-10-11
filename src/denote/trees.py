"""Bracketed constituency trees with indices (traces, pronouns, λ-binders) and F/WH-marking.

    [S [DP every dog] [VP barks]]          labelled bracketing (Penn-style parentheses also ok)
    t_1   he_2   t_3:d                      indexed traces / pronouns (optional type)
    [1 [S ...]]   [2:d [S ...]]             binder index node (Predicate Abstraction)
    John_F   [DP_F the dog]   who_WH        focus / wh-marking
"""
from __future__ import annotations

import itertools
import re
from dataclasses import dataclass, field
from pathlib import Path

from .typesys import parse_type

_uid = itertools.count(1)
TRACES = {"t", "trace", "PRO", "pro"}
COORD = {"and", "or"}
_LEAF = re.compile(r"^(?P<w>[^_:]+?)(?:_(?P<i>\d+))?(?:_(?P<f>F|WH))?(?::(?P<ty>.+))?$")


@dataclass(eq=False)
class Tree:
    label: str
    children: list = field(default_factory=list)
    word: str | None = None
    index: int | None = None
    itype: object = None
    focus: str | None = None
    adjoined: bool = False
    uid: int = field(default_factory=lambda: next(_uid))

    @property
    def is_leaf(self):
        return self.word is not None

    def walk(self, parent=None):
        yield self, parent
        for c in self.children:
            yield from c.walk(self)

    def leaves(self):
        return [n for n, _ in self.walk() if n.is_leaf]

    def find(self, uid):
        return next((n for n, _ in self.walk() if n.uid == uid), None)

    def parent_map(self):
        return {n.uid: p for n, p in self.walk()}

    def copy(self):
        return Tree(self.label, [c.copy() for c in self.children], self.word, self.index,
                    self.itype, self.focus, self.adjoined, self.uid)

    def text(self):
        return " ".join(n.word for n in self.leaves() if not (n.word in TRACES and n.index is not None))

    def __str__(self):
        if self.is_leaf:
            s = self.word
            if self.index is not None:
                s += f"_{self.index}"
            if self.focus:
                s += f"_{self.focus}"
            if self.itype is not None:
                s += f":{self.itype}"
            return s
        lab = self.label + (f"_{self.focus}" if self.focus else "")
        if self.index is not None and self.itype is not None:
            lab += f":{self.itype}"
        return "[" + lab + " " + " ".join(str(c) for c in self.children) + "]"


def _mk_node(label, kids):
    m = re.fullmatch(r"(\d+)(?::(.+))?", label)
    if m:
        return Tree(m.group(1), kids, index=int(m.group(1)),
                    itype=parse_type(m.group(2)) if m.group(2) else None)
    focus = None
    for suf in ("_F", "_WH"):
        if label.endswith(suf) and len(label) > len(suf):
            label, focus = label[: -len(suf)], suf[1:]
    return Tree(label, kids, focus=focus)


def _mk_leaf(tok):
    m = _LEAF.match(tok)
    if not m:
        return Tree(tok, word=tok)
    w, i, f, ty = m.group("w"), m.group("i"), m.group("f"), m.group("ty")
    return Tree(w, word=w, index=int(i) if i else None,
                itype=parse_type(ty) if ty else None, focus=f)


def parse_tree(src: str) -> Tree:
    toks = re.findall(r"[\[\]()]|[^\s\[\]()]+", src)
    pos = 0

    def node():
        nonlocal pos
        tok = toks[pos]
        if tok in ("[", "("):
            close = "]" if tok == "[" else ")"
            pos += 1
            if pos >= len(toks) or toks[pos] in ("[", "]", "(", ")"):
                raise ValueError(f"missing label at token {pos} in {src!r}")
            label = toks[pos]
            pos += 1
            kids = []
            while pos < len(toks) and toks[pos] != close:
                if toks[pos] in ("]", ")"):
                    raise ValueError(f"mismatched bracket in {src!r}")
                kids.append(node())
            if pos >= len(toks):
                raise ValueError(f"unclosed bracket in {src!r}")
            pos += 1
            return _mk_node(label, kids)
        pos += 1
        return _mk_leaf(tok)

    if not toks:
        raise ValueError("empty tree")
    t = node()
    if pos != len(toks):
        raise ValueError(f"trailing material in tree {src!r}")
    return t


def load_trees(spec: str):
    """A bracketed string, a .trees file (`id: [tree]` per line, % comments), or file#id."""
    s = spec.strip()
    if s.startswith(("[", "(")):
        return [("tree", parse_tree(s))]
    path, _, sel = spec.partition("#")
    out = []
    for n, line in enumerate(Path(path).read_text(encoding="utf-8").splitlines(), 1):
        line = line.split("%", 1)[0].strip()
        if not line:
            continue
        if not line.startswith(("[", "(")) and ":" in line:
            ident, tree = line.split(":", 1)
        else:
            ident, tree = f"{Path(path).stem}-{n}", line
        if sel and ident.strip() != sel:
            continue
        out.append((ident.strip(), parse_tree(tree.strip())))
    if sel and not out:
        raise KeyError(f"no tree with id {sel!r} in {path}")
    return out
