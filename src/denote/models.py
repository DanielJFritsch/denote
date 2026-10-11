"""Model theory: M = ⟨{D_σ}, I, w₀, g⟩, trivalent evaluation under three projection schemes
(weak Kleene/Bochvar, strong Kleene, middle Kleene/Peters), random and exhaustive models."""
from __future__ import annotations

import itertools
import random
import tomllib

from .typesys import Basic, Fun, T, E, S, D, arg_types, final, type_str
from .terms import Var, Const, Num, App, Bind, Op, typeof

SCHEMES = ("weak", "strong", "middle")
_NAMES = {"e": "abcdefghjkmnpqr", "s": None, "v": None, "i": None}


class ModelError(Exception):
    pass


def _pred(n, ext, acc=()):
    def f(x):
        if x is None:
            return None
        a = acc + (x,)
        return a in ext if len(a) == n else _pred(n, ext, a)
    return f


def _func(n, table, acc=()):
    def f(x):
        if x is None:
            return None
        a = acc + (x,)
        return table.get(a) if len(a) == n else _func(n, table, a)
    return f


class Model:
    def __init__(self, domains, interp, world=None, assignment=None, name="model"):
        self.domains = {k: list(v) for k, v in domains.items()}
        self.raw, self.world, self.g, self.name = dict(interp), world, dict(assignment or {}), name
        self._cache = {}

    @classmethod
    def load(cls, path):
        with open(path, "rb") as fh:
            data = tomllib.load(fh)
        dom = data.get("domains", {})
        return cls({k: v for k, v in dom.items() if k != "world"}, data.get("interpretation", {}),
                   dom.get("world"), data.get("assignment", {}), name=str(path))

    def domain(self, ty):
        if ty == T:
            return [True, False]
        if isinstance(ty, Basic):
            if ty.name not in self.domains:
                raise ModelError(f"model has no domain for type {ty}")
            return self.domains[ty.name]
        if isinstance(ty, Fun) and isinstance(ty.arg, Basic) and ty.res == T:
            base = self.domain(ty.arg)
            if len(base) > 12:
                raise ModelError(f"refusing to enumerate 2^{len(base)} sets of type {type_str(ty)}")
            return [_pred(1, {(x,) for x in sub})
                    for r in range(len(base) + 1) for sub in itertools.combinations(base, r)]
        raise ModelError(f"cannot quantify over type {type_str(ty)}")

    def denot(self, c: Const):
        key = (c.name, c.type)
        if key in self._cache:
            return self._cache[key]
        ty = c.type
        if c.name not in self.raw:
            if isinstance(ty, Basic) and ty.name in self.domains and c.name in self.domains[ty.name]:
                return c.name
            raise ModelError(f"constant {c.name} : {type_str(ty)} is not interpreted in {self.name}")
        raw, args = self.raw[c.name], arg_types(ty)
        if not args:
            val = raw
        elif final(ty) == T:
            ext = {tuple(x) if isinstance(x, (list, tuple)) else (x,) for x in raw}
            val = _pred(len(args), ext)
        else:
            if isinstance(raw, dict):
                table = {(k,): v for k, v in raw.items()}
            else:
                table = {tuple(r[:-1]): r[-1] for r in raw}
            val = _func(len(args), table)
        self._cache[key] = val
        return val

    def describe(self):
        lines = [f"domains: " + "; ".join(f"D_{k} = {{{', '.join(map(str, v))}}}" for k, v in self.domains.items())]
        if self.world is not None:
            lines.append(f"actual world: {self.world}")
        for k, v in sorted(self.raw.items()):
            if isinstance(v, (list, set, tuple)):
                items = sorted((str(x[0]) if len(x) == 1 else "⟨" + ", ".join(map(str, x)) + "⟩")
                               if isinstance(x, (tuple, list)) else str(x) for x in v)
                lines.append(f"  I({k}) = {{{', '.join(items)}}}")
            else:
                lines.append(f"  I({k}) = {v}")
        return "\n".join(lines)


def _and(a, b, sch):
    if sch == "weak":
        return None if a is None or b is None else (a and b)
    if sch == "strong":
        return False if a is False or b is False else (None if a is None or b is None else True)
    return None if a is None else (False if a is False else b)


def _or(a, b, sch):
    if sch == "weak":
        return None if a is None or b is None else (a or b)
    if sch == "strong":
        return True if a is True or b is True else (None if a is None or b is None else False)
    return None if a is None else (True if a is True else b)


def _not(a):
    return None if a is None else not a


def _all(vals, sch):
    if sch == "weak":
        return None if None in vals else all(vals)
    return False if False in vals else (None if None in vals else True)


def _any(vals, sch):
    if sch == "weak":
        return None if None in vals else any(vals)
    return True if True in vals else (None if None in vals else False)


class Evaluator:
    """⟦·⟧^{M,g} with None = # (undefined). Quantifiers in the middle scheme use the strong
    Kleene clauses (left-to-right asymmetry is defined for binary connectives only)."""

    def __init__(self, model: Model, scheme: str = "strong"):
        if scheme not in SCHEMES:
            raise ValueError(f"scheme must be one of {SCHEMES}")
        self.M, self.scheme = model, scheme

    def __call__(self, t, env=None):
        return self.ev(t, env or {})

    def _ext_eq(self, a, b, ty):
        if a is None or b is None:
            return None
        if not isinstance(ty, Fun):
            return a == b
        return all(self._ext_eq(a(x), b(x), ty.res) for x in self.M.domain(ty.arg))

    def ev(self, t, env):
        M, sch = self.M, self.scheme
        if isinstance(t, Var):
            if t in env:
                return env[t]
            if t.name == "w" and M.world is not None and t.type == S:
                return M.world
            if t.name in M.g:
                return M.g[t.name]
            raise ModelError(f"free variable {t.name} has no value (add it under [assignment])")
        if isinstance(t, Const):
            return M.denot(t)
        if isinstance(t, Num):
            return t.value
        if isinstance(t, App):
            f, a = self.ev(t.fun, env), self.ev(t.arg, env)
            return None if f is None or a is None else f(a)
        if isinstance(t, Bind):
            v = t.var
            if t.kind == "lam":
                return lambda x, _e=env: None if x is None else self.ev(t.body, {**_e, v: x})
            dom = M.domain(v.type)
            vals = [self.ev(t.body, {**env, v: x}) for x in dom]
            if t.kind == "forall":
                return _all(vals, sch)
            if t.kind == "exists":
                return _any(vals, sch)
            hits = [x for x, b in zip(dom, vals) if b is True]
            if t.kind == "iota":
                return hits[0] if len(hits) == 1 else None
            if t.kind == "max":
                return max(hits) if hits else None
            return len(hits)
        op, args = t.op, t.args
        if op == "top":
            return True
        if op == "bot":
            return False
        if op == "presup":
            c = self.ev(args[0], env)
            return self.ev(args[1], env) if c is True else None
        if op == "not":
            return _not(self.ev(args[0], env))
        a = self.ev(args[0], env)
        if op == "and" and sch == "middle" and a is not True:
            return None if a is None else False
        if op == "or" and sch == "middle" and a is not False:
            return None if a is None else True
        if op == "imp" and sch == "middle" and a is not True:
            return None if a is None else True
        b = self.ev(args[1], env)
        if op == "and":
            return _and(a, b, sch)
        if op == "or":
            return _or(a, b, sch)
        if op == "imp":
            return _or(_not(a), b, sch)
        if op == "iff":
            return None if a is None or b is None else a == b
        if a is None or b is None:
            return None
        if op == "eq":
            return self._ext_eq(a, b, typeof(args[0]))
        if op == "neq":
            return not self._ext_eq(a, b, typeof(args[0]))
        return {"lt": a < b, "le": a <= b, "gt": a > b, "ge": a >= b}[op]


# ---------------------------------------------------------------------------- generation

def _domains(sig, n):
    used = {"e"}
    for ty in sig.values():
        for b in arg_types(ty) + [final(ty)]:
            if isinstance(b, Basic) and b.name != "t":
                used.add(b.name)
    doms = {}
    for k in sorted(used):
        if k == "e":
            doms[k] = list(_NAMES["e"][:n]) if n <= len(_NAMES["e"]) else [f"a{i}" for i in range(n)]
        elif k == "d":
            doms[k] = list(range(n + 1))
        else:
            doms[k] = [f"{k}{i}" for i in range(n)]
    return doms


def _check_first_order(sig):
    for c, ty in sig.items():
        if any(not isinstance(a, Basic) for a in arg_types(ty)):
            raise ModelError(f"constant {c} : {type_str(ty)} is higher-order; define it lexically "
                             "in terms of first-order relations")


def random_model(sig: dict, n: int = 4, theta: float = 0.5, rng=None) -> Model:
    """Bernoulli random model μ_{n,θ}: each tuple enters each predicate with probability θ."""
    _check_first_order(sig)
    rng = rng or random.Random()
    doms = _domains(sig, n)
    interp = {}
    for c, ty in sig.items():
        args = arg_types(ty)
        if not args:
            interp[c] = rng.choice(doms[ty.name]) if ty != T else rng.random() < theta
        elif final(ty) == T:
            interp[c] = [tup for tup in itertools.product(*(doms[a.name] for a in args)) if rng.random() < theta]
        else:
            interp[c] = [list(tup) + [rng.choice(doms[final(ty).name])]
                         for tup in itertools.product(*(doms[a.name] for a in args))]
    return Model(doms, interp, "s0" if "s" in doms else None, name=f"μ(n={n},θ={theta})")


def count_models(sig, n):
    doms, total = _domains(sig, n), 1
    for ty in sig.values():
        args = arg_types(ty)
        cells = 1
        for a in args:
            cells *= len(doms[a.name])
        if not args:
            total *= len(doms.get(ty.name, [True, False])) if ty != T else 2
        elif final(ty) == T:
            total *= 2 ** cells
        else:
            total *= len(doms[final(ty).name]) ** cells
    return total


def all_models(sig: dict, n: int, limit: int = 50_000):
    """Every interpretation of `sig` over a domain of size n (raises if more than `limit`)."""
    _check_first_order(sig)
    if count_models(sig, n) > limit:
        raise ModelError(f"{count_models(sig, n)} models exceed the limit {limit}")
    doms, names, options = _domains(sig, n), list(sig), []
    for c in names:
        ty = sig[c]
        args = arg_types(ty)
        if not args:
            options.append([True, False] if ty == T else doms[ty.name])
        elif final(ty) == T:
            cells = list(itertools.product(*(doms[a.name] for a in args)))
            options.append([[cells[i] for i in range(len(cells)) if mask >> i & 1] for mask in range(2 ** len(cells))])
        else:
            cells = list(itertools.product(*(doms[a.name] for a in args)))
            options.append([[list(c_) + [v] for c_, v in zip(cells, vals)]
                            for vals in itertools.product(doms[final(ty).name], repeat=len(cells))])
    for combo in itertools.product(*options):
        yield Model(doms, dict(zip(names, combo)), "s0" if "s" in doms else None, name=f"exhaustive(n={n})")


def model_sample(sig, sizes=(1, 2, 3, 4), samples=400, theta=0.5, seed=0, exhaustive_limit=4096):
    """Exhaustive models for small sizes where feasible, random models otherwise."""
    rng, out = random.Random(seed), []
    for n in sizes:
        if count_models(sig, n) <= exhaustive_limit:
            out.extend(all_models(sig, n, exhaustive_limit))
        else:
            out.extend(random_model(sig, n, theta, rng) for _ in range(samples // len(sizes)))
    return out
