"""Type-driven interpretation (Klein & Sag 1985; Heim & Kratzer 1998).

Rules: TN NN FA IFA PM PA EI GC FOC, closure EC/W; type-shifters LIFT IDENT IOTA A BE
(Partee 1987), FC (Geach), AR (Hendriks 1993). Lenses: hk (default), cooper (Cooper 1983
storage), cont (Barker 2002 continuations with clause-bounded lowering)."""
from __future__ import annotations

import itertools
import re
from dataclasses import dataclass, field, replace

from .typesys import Fun, E, T, S, V, D, ET, GQ, unify, TypeClash, type_str, tvars, conjoinable, arg_types, final
from .terms import Var, Const, Num, App, Bind, Op, lam, exists, conj, eq, typeof, fv, alpha_key, show, fresh
from .typecheck import retype
from .reduce import normalize
from .trees import TRACES, COORD

PREFIX = {E: "x", D: "d", S: "w", V: "e"}
VNAME = {E: "x", ET: "P", S: "w", V: "e", D: "d"}
SHIFTS = ("LIFT", "IDENT", "IOTA", "A", "BE", "AR", "FC")
DEFAULT_SHIFTS = ("LIFT", "IDENT", "IOTA", "A", "BE", "AR")   # FC is opt-in: it overgenerates


def index_var(i, ty):
    return Var(f"{PREFIX.get(ty, 'v')}{i}", ty)


def _unit(m, ty):
    k = fresh("k", Fun(ty, T), m)
    return lam(k, App(k, m))


def _meet(x, y, ty, op):
    if ty == T:
        return Op(op, (x, y))
    v = fresh(VNAME.get(ty.arg, "v"), ty.arg, x, y)
    return lam(v, _meet(App(x, v), App(y, v), ty.res, op))


def _shift_table():
    def LIFT(m):
        P = fresh("P", ET, m)
        return lam(P, App(P, m))

    def IDENT(m):
        x = fresh("x", E, m)
        return lam(x, eq(x, m))

    def IOTA(m):
        x = fresh("x", E, m)
        return Bind("iota", x, App(m, x))

    def A(m):
        Q, x = fresh("Q", ET, m), fresh("x", E, m)
        return lam(Q, exists(x, conj(App(m, x), App(Q, x))))

    def BE(m):
        x = fresh("x", E, m)
        y = fresh("y", E, m, x)
        return lam(x, App(m, lam(y, eq(y, x))))

    return {"LIFT": (E, LIFT), "IDENT": (E, IDENT), "IOTA": (ET, IOTA), "A": (ET, A), "BE": (GQ, BE)}


UNARY = _shift_table()


@dataclass
class Deriv:
    node: object
    term: object
    rule: str
    kids: tuple = ()
    raw: object = None
    steps: tuple = ()
    shifts: tuple = ()
    senses: tuple = ()
    store: tuple = ()
    focus: tuple | None = None          # (focus variables, template, focus values)
    entry: object = None
    note: str = ""

    @property
    def type(self):
        return typeof(self.term)

    def walk(self):
        yield self
        for k in self.kids:
            yield from k.walk()

    def key(self):
        return (alpha_key(self.term), tuple((v.name, alpha_key(q)) for v, q in self.store),
                alpha_key(self.focus[1]) if self.focus else None)


@dataclass
class Failure:
    node: object
    kind: str
    detail: str
    types: tuple = ()
    suggestions: tuple = ()


@dataclass
class Options:
    shifts: str = "last-resort"          # off | last-resort | free
    allowed: tuple = DEFAULT_SHIFTS
    lens: str = "hk"                     # hk | cooper | cont
    senses: dict = field(default_factory=dict)
    override: dict = field(default_factory=dict)   # Tree.uid -> Term (position abstraction)
    max_derivs: int = 200


def _dedupe(ds):
    seen, out = set(), []
    for d in ds:
        k = d.key()
        if k not in seen:
            seen.add(k)
            out.append(d)
    return out


class Interpreter:
    def __init__(self, lexicon, options: Options | None = None):
        self.lex, self.opts = lexicon, options or Options()
        self.world = lexicon.free.get("w")
        self.failures, self.discarded = [], 0
        self._z, self._store_vars = itertools.count(1), set()

    # ------------------------------------------------------------------ entry point
    def interpret(self, tree):
        self.failures, self.discarded = [], 0
        out = []
        for d in self._node(tree, root=True):
            if d.store:
                continue
            d = self._close(d)
            if d.type != T:
                self._fail(d.node, "root type", f"root has type {type_str(d.type)}, not t")
                continue
            if any(v.name in self._store_vars for v in fv(d.term)):
                self.discarded += 1          # retrieval left a store variable unbound
                continue
            out.append(d)
        return _dedupe(out)

    def _close(self, d):
        if d.type == Fun(V, T):
            e = fresh("e", V, d.term)
            return self._mk(d.node, "EC", exists(e, App(d.term, e)), (d,), focus=d.focus,
                            note="existential closure of the event argument")
        if d.type == Fun(S, T) and self.world is not None:
            return self._mk(d.node, "W", App(d.term, self.world), (d,), focus=d.focus,
                            note="evaluation at the world of utterance")
        return d

    # ------------------------------------------------------------------ bookkeeping
    def _mk(self, node, rule, raw, kids, store=None, focus=None, shifts=(), note=""):
        steps = []
        term = normalize(raw, steps)
        sh = tuple(itertools.chain.from_iterable(k.shifts for k in kids)) + tuple(shifts)
        se = tuple(itertools.chain.from_iterable(k.senses for k in kids))
        st = store if store is not None else tuple(itertools.chain.from_iterable(k.store for k in kids))
        return Deriv(node, term, rule, tuple(kids), raw, tuple(steps), sh, se, st, focus, None, note)

    def _fail(self, node, kind, detail, types=(), suggestions=()):
        self.failures.append(Failure(node, kind, detail, tuple(types), tuple(suggestions)))

    @staticmethod
    def _order(n, d1, d2):
        return (d2, d1) if n.children and d2.node is n.children[0] else (d1, d2)

    def _build(self, n, rule, fn, d1, d2, shifts=(), note=""):
        raw, focus = fn(d1.term, d2.term), None
        if d1.focus or d2.focus:
            f1, f2 = d1.focus or ((), None, ()), d2.focus or ((), None, ())
            t1 = f1[1] if d1.focus else d1.term
            t2 = f2[1] if d2.focus else d2.term
            focus = (f1[0] + f2[0], normalize(fn(t1, t2)), f1[2] + f2[2])
        return self._mk(n, rule, raw, self._order(n, d1, d2), focus=focus, shifts=shifts, note=note)

    # ------------------------------------------------------------------ nodes
    def _node(self, n, root=False):
        if n.uid in self.opts.override:
            ds = [Deriv(n, self.opts.override[n.uid], "VAR", note="position abstracted")]
        elif n.is_leaf:
            ds = self._terminal(n)
        elif len(n.children) == 1:
            ds = [self._pa(n, d) if n.index is not None else
                  replace(d, node=n, rule="NN", kids=(d,), raw=None, steps=(), note="")
                  for d in self._node(n.children[0])]
        elif len(n.children) == 2:
            L, R = self._node(n.children[0]), self._node(n.children[1])
            ds = [r for a, b in itertools.product(L, R) for r in self._combine(n, a, b)]
        elif len(n.children) == 3 and n.children[1].is_leaf and n.children[1].word in COORD:
            L, R = self._node(n.children[0]), self._node(n.children[2])
            ds = [r for a, b in itertools.product(L, R)
                  for r in self._coord(n, a, b, n.children[1].word)]
        else:
            self._fail(n, "unsupported", f"{len(n.children)}-ary branching at {n.label}")
            ds = []
        if n.focus == "F" and ds:
            ds = [self._mark(d) for d in ds]
        if self.opts.lens == "cooper" and ds:
            ds = self._cooper(n, ds, root)
        return _dedupe(ds)[: self.opts.max_derivs]

    def _terminal(self, n):
        w = n.word
        entries = self.lex.lookup(w, self.opts.senses)
        if n.focus == "WH":
            z = Var(f"z{next(self._z)}", n.itype or E)
            restr = next((e.term for e in entries if e.type == Fun(z.type, T)), None)
            return [Deriv(n, z, "WH", focus=((z,), z, (restr,)),
                          note=f"wh-variable {z.name} (structured question)")]
        if n.index is not None:
            v = index_var(n.index, n.itype or E)
            pro = [e for e in entries if e.type == Fun(v.type, v.type)]
            if w in TRACES or not pro:
                return [Deriv(n, v, "TN", note=f"Traces & Pronouns: g({n.index}) = {v.name}")]
            return [self._mk(n, "TN", App(e.term, v), (), note="pronoun: φ-features as partial identity")
                    for e in pro]
        if re.fullmatch(r"\d+", w):
            return [Deriv(n, Num(int(w)), "TN")]
        if not entries:
            if w[:1].isupper():
                return [Deriv(n, Const(w.lower(), E), "TN*", note="proper name (automatic entry)")]
            self._fail(n, "lexical gap", f"no lexical entry for '{w}'")
            return []
        return [Deriv(n, e.term, "TN", senses=((w, e.sense),) if e.sense else (), entry=e)
                for e in entries]

    def _pa(self, n, d):
        v = index_var(n.index, n.itype or E)
        focus = (d.focus[0], lam(v, d.focus[1]), d.focus[2]) if d.focus else None
        note = "" if v in fv(d.term) else f"vacuous abstraction over {v.name}"
        return self._mk(n, "PA", lam(v, d.term), (d,), focus=focus, note=note)

    def _mark(self, d):
        z = Var(f"z{next(self._z)}", d.type)
        return replace(d, focus=((z,), z, (d.term,)), note=(d.note + " [F]").strip())

    # ------------------------------------------------------------------ binary nodes
    def _combine(self, n, a, b):
        for op, other in ((a, b), (b, a)):
            if op.entry is not None and "focus" in op.entry.flags:
                return self._foc(n, op, other)
        out = self._base(n, a, b)
        if self.opts.shifts == "free" or (self.opts.shifts == "last-resort" and not out):
            out += self._shifted(n, a, b)
        if self.opts.lens == "cont":
            out += self._cont(n, a, b)
        if not out:
            self._diagnose(n, a, b)
        return out

    def _fa(self, n, f, x):
        tf, tx = f.type, x.type
        if not isinstance(tf, Fun):
            return None
        if tf.arg == tx:
            return self._build(n, "FA", lambda F, X: App(F, X), f, x)
        if tvars(tf) or tvars(tx):
            sub = {}
            try:
                unify(tf.arg, tx, sub)
            except TypeClash:
                return None
            return self._build(n, "FA", lambda F, X: App(F, X), replace(f, term=retype(f.term, sub)),
                               replace(x, term=retype(x.term, sub)), note="polymorphic instantiation")
        return None

    def _base(self, n, a, b):
        out = [r for f, x in ((a, b), (b, a)) if (r := self._fa(n, f, x))]
        if self.world is not None:
            w = self.world
            for f, x in ((a, b), (b, a)):
                if isinstance(f.type, Fun) and f.type.arg == Fun(S, x.type):
                    out.append(self._build(n, "IFA", lambda F, X: App(F, lam(w, X)), f, x,
                                           note="intensional functional application"))
        ta = a.type
        if ta == b.type and isinstance(ta, Fun) and ta.res == T:
            def pm(F, X, _t=ta):
                v = fresh(VNAME.get(_t.arg, "v"), _t.arg, F, X)
                return lam(v, conj(App(F, v), App(X, v)))
            out.append(self._build(n, "PM", pm, a, b))
        evt = Fun(E, Fun(V, T))
        for f, x in ((a, b), (b, a)):
            if f.type == evt and x.type == Fun(V, T):
                def ei(F, X):
                    xv, ev = fresh("x", E, F, X), fresh("e", V, F, X)
                    return lam(xv, lam(ev, conj(App(App(F, xv), ev), App(X, ev))))
                out.append(self._build(n, "EI", ei, f, x, note="Event Identification (Kratzer 1996)"))
        return out

    def _shift(self, d, name, fn):
        focus = (d.focus[0], normalize(fn(d.focus[1])), d.focus[2]) if d.focus else None
        return self._mk(d.node, name, fn(d.term), (d,), focus=focus, shifts=(name,),
                        note=f"type shift {name}")

    def _shifted(self, n, a, b):
        out, allowed = [], self.opts.allowed
        for i, d in enumerate((a, b)):
            other = b if i == 0 else a
            for name, (src, fn) in UNARY.items():
                if name in allowed and d.type == src:
                    sd = self._shift(d, name, fn)
                    out += self._base(n, *((sd, other) if i == 0 else (other, sd)))
        for f, g in ((a, b), (b, a)):
            tf, tg = f.type, g.type
            if "FC" in allowed and isinstance(tf, Fun) and isinstance(tg, Fun) and tg.res == tf.arg:
                def fc(F, G, _ta=tg.arg):
                    z = fresh("z", _ta, F, G)
                    return lam(z, App(F, App(G, z)))
                out.append(self._build(n, "FC", fc, f, g, shifts=("FC",), note="function composition (Geach)"))
            if "AR" in allowed and tf == Fun(E, ET) and tg == GQ:
                def ar_narrow(F, G):
                    x, y = fresh("x", E, F, G), fresh("y", E, F, G)
                    return lam(x, App(G, lam(y, App(App(F, y), x))))

                def ar_wide(F, G):
                    Q, x, y = fresh("Q", GQ, F, G), fresh("x", E, F, G), fresh("y", E, F, G)
                    return lam(Q, App(G, lam(y, App(Q, lam(x, App(App(F, y), x))))))
                out.append(self._build(n, "AR", ar_narrow, f, g, shifts=("AR",),
                                       note="argument raising, object ≺ subject (Hendriks 1993)"))
                out.append(self._build(n, "AR", ar_wide, f, g, shifts=("AR",),
                                       note="argument raising, object ≻ subject (Hendriks 1993)"))
        return out

    def _coord(self, n, a, b, word):
        op = "and" if word == "and" else "or"
        pairs = [(a, b)]
        if "LIFT" in self.opts.allowed and self.opts.shifts != "off" and E in (a.type, b.type):
            lift = UNARY["LIFT"][1]
            pairs.append((self._shift(a, "LIFT", lift) if a.type == E else a,
                          self._shift(b, "LIFT", lift) if b.type == E else b))
        out = []
        for x, y in pairs:
            if x.type == y.type and conjoinable(x.type):
                out.append(self._build(n, "GC", lambda X, Y, _t=x.type: _meet(X, Y, _t, op), x, y,
                                       note="generalized " + ("conjunction" if op == "and" else "disjunction")))
        if not out:
            self._fail(n, "type mismatch", f"cannot coordinate {type_str(a.type)} and {type_str(b.type)}",
                       (a.type, b.type))
        return out

    def _foc(self, n, op, other):
        if not other.focus:
            self._fail(n, "focus", f"'{op.node.word or op.node.label}' is focus-sensitive but its sister "
                                   "contains no F-marked constituent")
            return []
        vs, tpl, vals = other.focus
        if len(vs) != 1:
            self._fail(n, "focus", "exactly one focus per focus-sensitive operator is supported")
            return []
        z = vs[0]
        sub = {}
        try:
            unify(op.type, Fun(Fun(z.type, T), Fun(z.type, T)), sub)
        except TypeClash:
            self._fail(n, "type mismatch", f"focus operator {type_str(op.type)} cannot associate with "
                                           f"a focus of type {type_str(z.type)}")
            return []
        ttpl = typeof(tpl)
        if final(ttpl) != T:
            self._fail(n, "focus", f"focus background of type {type_str(ttpl)} is not conjoinable")
            return []
        xs = []
        for ty in arg_types(ttpl):                      # cross-categorial only (Rooth 1985)
            xs.append(fresh(VNAME.get(ty, "v"), ty, tpl, vals[0], *xs))
        body = tpl
        for x in xs:
            body = App(body, x)
        B = lam(z, body)
        res = App(App(retype(op.term, sub), B), vals[0])
        for x in reversed(xs):
            res = lam(x, res)
        return [self._mk(n, "FOC", res, self._order(n, op, other),
                         note=f"association with focus: B = {show(normalize(B))}, F = {show(vals[0])}")]

    # ------------------------------------------------------------------ Cooper storage
    def _cooper(self, n, ds, root):
        out = list(ds)
        if not root:
            for d in ds:
                if d.type == GQ:
                    u = Var(f"u{next(self._z)}", E)
                    self._store_vars.add(u.name)
                    out.append(replace(d, term=u, rule="STORE", kids=(d,), raw=None, steps=(),
                                       store=d.store + ((u, d.term),),
                                       note=f"Cooper storage ⟨{u.name}, {show(d.term)}⟩"))
        for d in list(out):
            if d.type == T and d.store:
                for k in range(1, len(d.store) + 1):
                    for combo in itertools.permutations(d.store, k):
                        term = d.term
                        for u, q in combo:                       # first retrieved = narrowest
                            term = App(q, lam(u, term))
                        rest = tuple(s for s in d.store if s not in combo)
                        out.append(self._mk(n, "RETRIEVE", term, (d,), store=rest, focus=d.focus,
                                            note="retrieve " + " ≺ ".join(u.name for u, _ in combo)))
        return out

    # ------------------------------------------------------------------ continuations
    def _cont(self, n, a, b):
        """One-level continuation semantics: a daughter of type <<σ,t>,t> may be read as a
        computation of a σ; values combine by FA or PM inside the monad, evaluated left-to-right
        (LR) or right-to-left (RL), with lowering at type t (clause-bounded)."""
        def views(d):
            t, vs = d.type, [("pure", d.type)]
            if isinstance(t, Fun) and t.res == T and isinstance(t.arg, Fun) and t.arg.res == T:
                vs.append(("scope", t.arg.arg))
            return vs

        def combinators(sa, sb):
            out = []
            if isinstance(sa, Fun) and sa.arg == sb:
                out.append(("FA", lambda m, y: App(m, y), sa.res))
            if isinstance(sb, Fun) and sb.arg == sa:
                out.append(("FA", lambda m, y: App(y, m), sb.res))
            if sa == sb and isinstance(sa, Fun) and sa.res == T:
                def pm(m, y, _t=sa):
                    v = fresh(VNAME.get(_t.arg, "v"), _t.arg, m, y)
                    return lam(v, conj(App(m, v), App(y, v)))
                out.append(("PM", pm, sa))
            return out

        out = []
        for (ka, sa), (kb, sb) in itertools.product(views(a), views(b)):
            if ka == kb == "pure":
                continue
            for cname, comb, tau in combinators(sa, sb):
                for order_ in (("LR", "RL") if ka == kb == "scope" else ("LR",)):
                    def build(A, B, ka=ka, kb=kb, sa=sa, sb=sb, tau=tau, comb=comb, order_=order_):
                        Ac = A if ka == "scope" else _unit(A, sa)
                        Bc = B if kb == "scope" else _unit(B, sb)
                        k = fresh("k", Fun(tau, T), A, B)
                        m = fresh("m", sa, A, B, k)
                        y = fresh("y", sb, A, B, k, m)
                        inner = App(k, comb(m, y))
                        body = (App(Ac, lam(m, App(Bc, lam(y, inner)))) if order_ == "LR"
                                else App(Bc, lam(y, App(Ac, lam(m, inner)))))
                        res = lam(k, body)
                        if tau == T:
                            p = fresh("p", T, res)
                            res = App(res, lam(p, p))
                        return res
                    out.append(self._build(n, f"CONT{'↓' if tau == T else ''}({cname},{order_})", build, a, b,
                                           note="continuation-based combination (Barker 2002)"))
        return out

    # ------------------------------------------------------------------ diagnostics
    def _composes(self, t1, t2):
        def fa(f, x):
            return isinstance(f, Fun) and (f.arg == x or (self.world is not None and f.arg == Fun(S, x)))
        return fa(t1, t2) or fa(t2, t1) or (t1 == t2 and isinstance(t1, Fun) and t1.res == T)

    def _diagnose(self, n, a, b):
        ta, tb, sugg = a.type, b.type, []
        for d, other in ((a, b), (b, a)):
            for name, (src, fn) in UNARY.items():
                if d.type == src:
                    st = typeof(fn(d.term))
                    if self._composes(st, other.type):
                        sugg.append(f"{name} on {d.node.label} ({type_str(src)} ⇒ {type_str(st)})")
        if GQ in (ta, tb):
            sugg.append("QR the quantificational DP (readings --method qr) or use --lens cooper|cont")
        if Fun(E, ET) in (ta, tb) and GQ in (ta, tb):
            sugg.append("argument raising (AR) with --shifts last-resort")
        if self.world is None and any(isinstance(t, Fun) and t.arg == Fun(S, T) for t in (ta, tb)):
            sugg.append("declare '@free w : s' in the lexicon to enable IFA")
        self._fail(n, "type mismatch", f"{a.node.label} : {type_str(ta)} and {b.node.label} : "
                                       f"{type_str(tb)} do not compose", (ta, tb), sugg)
