"""Renderers: annotated text trees, LaTeX (forest trees + Heim & Kratzer-style equational
derivations), and JSON."""
from __future__ import annotations

import json

from .typesys import type_str
from .terms import show

RULE_NAMES = {
    "TN": "Terminal Nodes", "TN*": "Terminal Nodes (auto)", "NN": "Non-branching Nodes",
    "FA": "Functional Application", "IFA": "Intensional Functional Application",
    "PM": "Predicate Modification", "PA": "Predicate Abstraction", "EI": "Event Identification",
    "GC": "Generalized Coordination", "FOC": "Association with Focus", "EC": "Existential Closure",
    "W": "World Saturation", "STORE": "Cooper Storage", "RETRIEVE": "Cooper Retrieval",
    "LIFT": "LIFT", "IDENT": "IDENT", "IOTA": "IOTA", "A": "A (∃-shift)", "BE": "BE",
    "AR": "Argument Raising", "FC": "Function Composition", "WH": "Wh-variable", "VAR": "Abstracted position",
}


def _label(d):
    n = d.node
    if n.is_leaf:
        return f"“{n}”"
    if n.index is not None and n.label.isdigit():
        return f"λ{n.index}"
    return n.label + (f"_{n.focus}" if n.focus else "")


def text_tree(d, style="unicode", steps=False):
    lines = []

    def rec(x, prefix, last, top):
        conn = "" if top else ("└─ " if last else "├─ ")
        lines.append(f"{prefix}{conn}{_label(x)} : {type_str(x.type, style if style != 'latex' else 'unicode')}"
                     f"   [{x.rule}]" + (f"  — {x.note}" if x.note else ""))
        cont = prefix + ("" if top else ("   " if last else "│  "))
        bar = cont + ("│  " if x.kids else "   ")
        lines.append(f"{bar}{show(x.term, style)}")
        if steps and len(x.steps) > 0:
            lines.append(f"{bar}  = {show(x.raw, style)}")
            for s in x.steps:
                lines.append(f"{bar}  ⇝{s.rule} {show(s.result, style)}")
        for i, k in enumerate(x.kids):
            rec(k, cont, i == len(x.kids) - 1, False)

    rec(d, "", True, True)
    return "\n".join(lines)


def _tex_escape(s):
    return s.replace("_", r"\_").replace("&", r"\&").replace("#", r"\#")


def _tex_rule(r):
    return r.replace("↓", r"$\downarrow$").replace("*", r"$^{*}$")


def _tex_label(n):
    if n.is_leaf:
        w = _tex_escape(n.word)
        if n.index is not None:
            w += r"$_{%d}$" % n.index
        if n.focus:
            w += r"$_{\mathrm{%s}}$" % n.focus
        return r"\textit{%s}" % w
    if n.index is not None and n.label.isdigit():
        return r"$\lambda_{%d}$" % n.index
    return _tex_escape(n.label) + (r"$_{\mathrm{%s}}$" % n.focus if n.focus else "")


def _tex_yield(n):
    """Object-language yield for ⟦·⟧ labels, keeping traces and binder indices (H&K style)."""
    if n.is_leaf:
        return _tex_label(n)
    parts = " ".join(_tex_yield(c) for c in n.children)
    if n.index is not None and n.label.isdigit():
        return r"$\lambda_{%d}$ " % n.index + parts
    return parts


def latex_tree(d):
    def rec(x):
        node = (r"{%s\\$%s$\\$%s$\\\scriptsize\textsc{%s}}"
                % (_tex_label(x.node), type_str(x.type, "latex"), show(x.term, "latex"), _tex_rule(x.rule)))
        return "[" + node + "".join(" " + rec(k) for k in x.kids) + "]"
    return ("\\begin{adjustbox}{max width=\\linewidth, max totalheight=0.82\\textheight, center}\n"
            "\\begin{forest}\n  for tree={align=center, base=bottom, font=\\small, s sep=4mm}\n  "
            + rec(d) + "\n\\end{forest}\n\\end{adjustbox}")


def latex_equations(d):
    """⟦root⟧ = ⟦β⟧(⟦γ⟧) = … step by step, rule-annotated (Heim & Kratzer 1998 style)."""
    out = []
    for x in reversed(list(d.walk())):
        if x.raw is None or not x.kids:
            continue
        name = _tex_yield(x.node)
        lines = [r"\llbracket \text{%s} \rrbracket &= %s && \text{(%s)}" % (name, show(x.raw, "latex"), _tex_rule(x.rule))]
        for s in x.steps:
            lines.append(r"&= %s && (\%s)" % (show(s.result, "latex"), {"β": "beta", "η": "eta"}.get(s.rule, "partial")))
        out.append("\\begin{align*}\n" + " \\\\\n".join(lines) + "\n\\end{align*}")
    return "\n".join(out)


LATEX_PREAMBLE = r"""\documentclass[11pt]{article}
\usepackage[margin=2cm,landscape]{geometry}
\usepackage{amsmath,amssymb,stmaryrd,forest,adjustbox}
\begin{document}
"""


def latex_document(parts):
    """A standalone document; `parts` is a list of (title, derivation)."""
    body = [r"\section*{%s}" % _tex_escape(t) + "\n" + latex_tree(d) + "\n\n\\bigskip\n" + latex_equations(d)
            for t, d in parts]
    return LATEX_PREAMBLE + "\n\\clearpage\n".join(body) + "\n\\end{document}\n"


def to_json(d):
    def rec(x):
        return {"label": x.node.label, "word": x.node.word, "type": str(x.type), "rule": x.rule,
                "term": show(x.term, "ascii"), "unicode": show(x.term),
                "steps": [{"rule": s.rule, "result": show(s.result, "ascii")} for s in x.steps],
                "shifts": list(x.shifts), "note": x.note, "children": [rec(k) for k in x.kids]}
    return json.dumps(rec(d), ensure_ascii=False, indent=2)
