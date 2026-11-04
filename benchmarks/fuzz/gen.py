#!/usr/bin/env python3
"""Deterministic random CNF generators for fuzzing popso-sat.

Every formula is a pure function of its seed (``generate(seed)``), so a fuzz
failure is reproduced from the seed alone. The default mix produces many
small formulas fast:

  ksat       uniform random k-SAT (k = 2..5) near the satisfiability threshold
  mixed      random CNF with mixed clause lengths, density near the threshold
  layered    cnfuzz-style structured formulas (layers of variables, clauses
             within a layer and reaching back into earlier layers)
  edge-*     edge cases: empty formula, empty clause, unit chains, duplicate
             literals / tautologies / duplicate clauses, unused variables,
             very long clauses, pure 2-SAT with equivalences, many units,
             single-clause formulas
  php        pigeonhole (3..6 holes), mostly UNSAT
  parity     two XOR chains over the same variables, SAT or UNSAT
  circuit    miters of two copies of a random AND/OR/XOR/ITE circuit written in
             different equivalent gate forms (sometimes with one gate changed)

Besides the edge-* families, low-probability mutators sprinkle duplicate
literals, tautologies, duplicate clauses, units and unused variables into the
other families.

CLI:
  gen.py --seed 7                      print one formula (DIMACS) to stdout
  gen.py --seed 0 --count 100 --outdir DIR
  gen.py --list                        list families
  gen.py --stats --count 2000          family mix, sizes, SAT/UNSAT balance and
                                       reference-solver time (needs PySAT)
"""

from __future__ import annotations

import argparse
import math
import random
import sys
import time
from dataclasses import dataclass, field
from pathlib import Path

# Satisfiability thresholds of uniform random k-SAT (clauses / variables).
THRESHOLD = {1: 0.7, 2: 1.0, 3: 4.267, 4: 9.931, 5: 21.117, 6: 43.37, 7: 87.79}

# Largest n per k that the reference solves in milliseconds near the threshold.
KSAT_MAX_VARS = {2: 200, 3: 200, 4: 70, 5: 45}


@dataclass
class Formula:
    nvars: int
    clauses: list[list[int]]
    family: str
    seed: int = 0
    expected: str | None = None  # "SAT" / "UNSAT" when known by construction
    notes: list[str] = field(default_factory=list)

    def max_var(self) -> int:
        return max((abs(l) for c in self.clauses for l in c), default=0)

    def dimacs(self, comments: bool = True) -> str:
        out = []
        if comments:
            out.append(f"c popso-sat fuzz formula family={self.family} seed={self.seed}")
            if self.expected:
                out.append(f"c expected {self.expected}")
            for n in self.notes:
                out.append(f"c {n}")
        out.append(f"p cnf {self.nvars} {len(self.clauses)}")
        out.extend(" ".join(map(str, c + [0])) for c in self.clauses)
        return "\n".join(out) + "\n"


# --------------------------------------------------------------------------- helpers


def _log_uniform_int(rng: random.Random, lo: int, hi: int) -> int:
    """Integer in [lo, hi], skewed towards small values (log-uniform)."""
    return min(hi, max(lo, int(math.exp(rng.uniform(math.log(lo), math.log(hi + 1))))))


def _random_clause(rng: random.Random, n: int, k: int) -> list[int]:
    vs = rng.sample(range(1, n + 1), min(k, n))
    return [v if rng.random() < 0.5 else -v for v in vs]


def _ksat_clauses(rng: random.Random, n: int, m: int, k: int) -> list[list[int]]:
    return [_random_clause(rng, n, k) for _ in range(m)]


# --------------------------------------------------------------------------- families


def gen_ksat(rng: random.Random, max_vars: int) -> Formula:
    k = rng.choices([2, 3, 4, 5], weights=[1, 6, 2, 1])[0]
    n = _log_uniform_int(rng, 5, max(5, min(max_vars, KSAT_MAX_VARS[k])))
    lo, hi = (0.9, 1.6) if k == 2 else (0.85, 1.15)  # 2-SAT: wide window at small n
    m = max(1, round(THRESHOLD[k] * rng.uniform(lo, hi) * n))
    return Formula(n, _ksat_clauses(rng, n, m, k), f"ksat{k}")


def gen_mixed(rng: random.Random, max_vars: int) -> Formula:
    """Mixed clause lengths 1..7; m from the harmonic mixture of thresholds."""
    lengths = [1, 2, 3, 4, 5, 6, 7]
    w = [rng.choice([0, 0, 0.05]), rng.random(), rng.random() * 2, rng.random(), rng.random() * 0.5,
         rng.random() * 0.2, rng.random() * 0.1]
    if sum(w[1:]) == 0:
        w[2] = 1.0
    total = sum(w)
    p = [x / total for x in w]
    # Each clause of length k "uses up" 1/threshold_k of a variable.
    per_clause = sum(pk / THRESHOLD[k] for k, pk in zip(lengths, p))
    longest = max(k for k, pk in zip(lengths, p) if pk > 0)
    cap = 200 if longest <= 3 else 90 if longest == 4 else 50
    n = _log_uniform_int(rng, 8, max(8, min(max_vars, cap)))
    m = max(1, round(n / per_clause * rng.uniform(1.05, 1.45)))  # tuned for a SAT/UNSAT mix
    clauses = [_random_clause(rng, n, rng.choices(lengths, weights=p)[0]) for _ in range(m)]
    return Formula(n, clauses, "mixed")


def gen_layered(rng: random.Random, max_vars: int) -> Formula:
    """cnfuzz-style: variables in layers; a clause of layer i draws each literal
    from layer i, or (geometrically less often) from earlier layers. Clause
    lengths start at 2 or 3 and grow geometrically. Optionally the variable
    numbering is scrambled to hide the layer locality."""
    nlayers = rng.randint(1, 10)
    maxw = rng.randint(5, 40)
    widths = []
    for _ in range(nlayers):
        if sum(widths) >= max_vars:
            break
        widths.append(min(rng.randint(min(5, maxw), maxw), max(1, max_vars - sum(widths))))
    lows, highs = [], []
    for wd in widths:
        lo = highs[-1] + 1 if highs else 1
        lows.append(lo)
        highs.append(lo + wd - 1)
    n = highs[-1]
    min_len = rng.choices([2, 3], weights=[1, 2])[0]
    cont = rng.uniform(0.15, 0.6)  # probability to grow a clause by one more literal
    back = rng.uniform(0.1, 0.4)  # probability to step back one layer per literal
    clauses = []
    for i, wd in enumerate(widths):
        span = wd + (widths[i - 1] if i else 0)
        # Density per layer, tuned for a mix of SAT and UNSAT formulas.
        ratio = rng.uniform(1.4, 2.4) if min_len == 3 else rng.uniform(0.9, 1.8)
        for _ in range(max(1, round(ratio * span))):
            length = min_len
            while length < 10 and rng.random() < cont:
                length += 1
            seen = set()
            clause = []
            for _ in range(length):
                layer = i
                while layer and rng.random() < back:
                    layer -= 1
                v = rng.randint(lows[layer], highs[layer])
                if v in seen:
                    continue
                seen.add(v)
                clause.append(v if rng.random() < 0.5 else -v)
            clauses.append(clause)
    f = Formula(n, clauses, "layered")
    if rng.random() < 0.5:
        perm = list(range(1, n + 1))
        rng.shuffle(perm)
        f.clauses = [[perm[abs(l) - 1] * (1 if l > 0 else -1) for l in c] for c in f.clauses]
        rng.shuffle(f.clauses)
        f.family = "layered-scrambled"
    return f


def gen_php(rng: random.Random, max_vars: int) -> Formula:
    holes = rng.randint(3, 6)
    pigeons = holes + 1 if rng.random() < 0.85 else holes
    var = lambda p, h: p * holes + h + 1  # noqa: E731
    clauses = [[var(p, h) for h in range(holes)] for p in range(pigeons)]
    for h in range(holes):
        for p in range(pigeons):
            for q in range(p + 1, pigeons):
                clauses.append([-var(p, h), -var(q, h)])
    if rng.random() < 0.5:
        rng.shuffle(clauses)
    return Formula(pigeons * holes, clauses, f"php{pigeons}x{holes}",
                   expected="UNSAT" if pigeons > holes else "SAT")


def _xor_chain(rng: random.Random, xs: list[int], parity: int, next_var: int, clauses: list[list[int]]) -> int:
    """Encode XOR(xs) == parity with a chain of fresh variables (3-variable XORs).
    Returns the next free variable."""
    acc = xs[0]
    for x in xs[1:]:
        t = next_var
        next_var += 1
        # t <-> acc xor x
        clauses += [[-t, acc, x], [-t, -acc, -x], [t, -acc, x], [t, acc, -x]]
        acc = t
    clauses.append([acc] if parity else [-acc])
    return next_var


def gen_parity(rng: random.Random, max_vars: int) -> Formula:
    n = rng.randint(4, 24)
    xs = list(range(1, n + 1))
    b1 = rng.randint(0, 1)
    b2 = b1 if rng.random() < 0.3 else 1 - b1
    clauses: list[list[int]] = []
    a, b = xs[:], xs[:]
    rng.shuffle(a)
    rng.shuffle(b)
    nv = _xor_chain(rng, a, b1, n + 1, clauses)
    nv = _xor_chain(rng, b, b2, nv, clauses)
    rng.shuffle(clauses)
    return Formula(nv - 1, clauses, "parity", expected="SAT" if b1 == b2 else "UNSAT")


# ----- edge cases


def _encode_gate(kind: str, out: int, ins: list[int], clauses: list[list[int]], rng: random.Random) -> None:
    """Tseitin clauses of out = kind(ins); `out` may be a negative literal."""
    if kind == "and":
        clauses.extend([-out, a] for a in ins)
        clauses.append([out] + [-a for a in ins])
    elif kind == "or":
        clauses.extend([out, -a] for a in ins)
        clauses.append([-out] + list(ins))
    elif kind == "xor":
        a, b = ins
        clauses += [[-out, a, b], [-out, -a, -b], [out, -a, b], [out, a, -b]]
    else:  # ite: out = c ? t : e
        c, t, e = ins
        clauses += [[-c, -t, out], [-c, t, -out], [c, -e, out], [c, e, -out]]
        if rng.random() < 0.3:  # the redundant blocking clauses, sometimes
            clauses += [[-t, -e, out], [t, e, -out]]


def gen_circuit(rng: random.Random, max_vars: int) -> Formula:
    """Random AND / OR / XOR / ITE circuits (Tseitin encoded), mostly as a miter of two copies of
    the same circuit over shared inputs. The second copy writes gates in varied equivalent forms
    (permuted inputs, ITE(-c, e, t), negated outputs via De Morgan) so that congruence closure,
    gate-based elimination and substitution have work to do. Sometimes one gate of the second
    copy is changed (the miter is then usually SAT), or the outputs get random units instead."""
    n_in = rng.randint(2, 8)
    n_gates = rng.randint(3, max(3, min(max(40, max_vars // 5), (max_vars - n_in - 2) // 2)))
    specs = []
    for g in range(n_gates):
        kind = rng.choice(["and", "or", "xor", "ite"])
        k = {"xor": 2, "ite": 3}.get(kind, rng.randint(2, 3))
        avail = n_in + g
        if avail < k:
            kind, k = "and", 2
        picks = rng.sample(range(avail), k)
        specs.append((kind, [(i, rng.random() < 0.3) for i in picks]))
    mutate = rng.random() < 0.3
    bad = rng.randrange(n_gates) if mutate else -1
    clauses: list[list[int]] = []
    next_var = n_in + 1

    def build(variant: bool) -> list[int]:
        nonlocal next_var
        sig = list(range(1, n_in + 1))
        for g, (kind, ins) in enumerate(specs):
            lits = [-sig[i] if neg else sig[i] for i, neg in ins]
            if variant and g == bad:
                kind = {"and": "or", "or": "and", "xor": "and", "ite": "xor"}[kind]
                lits = lits[:2]
            out = next_var
            next_var += 1
            if variant and rng.random() < 0.5:
                if kind == "ite":
                    c, t, e = lits
                    lits = [-c, e, t]  # ITE(-c, e, t) = ITE(c, t, e)
                else:
                    rng.shuffle(lits)
            r = rng.random() if variant else 1.0
            if kind in ("and", "or") and r < 0.25:
                # De Morgan: out = AND(x) <=> -out = OR(-x) (and dually).
                _encode_gate("or" if kind == "and" else "and", -out, [-a for a in lits], clauses, rng)
                sig.append(out)
            elif kind == "xor" and r < 0.25:
                a, b = lits
                _encode_gate("xor", -out, [a, -b], clauses, rng)  # -out = XOR(a, -b) = -XOR(a, b)
                sig.append(out)
            elif r < 0.45:
                _encode_gate(kind, -out, lits, clauses, rng)  # the variable carries the negated signal
                sig.append(-out)
            else:
                _encode_gate(kind, out, lits, clauses, rng)
                sig.append(out)
        return sig

    s1 = build(False)
    s2 = build(True)
    notes = [f"inputs {n_in}, gates {n_gates}" + (f", gate {bad} changed in copy 2" if mutate else "")]
    if rng.random() < 0.8:
        # Miter on the last gate (and sometimes a few more outputs): some output pair differs.
        outs = [n_gates - 1] + rng.sample(range(n_gates - 1), min(n_gates - 1, rng.randint(0, 2)))
        diff = []
        for g in outs:
            d = next_var
            next_var += 1
            _encode_gate("xor", d, [s1[n_in + g], s2[n_in + g]], clauses, rng)
            diff.append(d)
        clauses.append(diff)
    else:
        for g in rng.sample(range(n_gates), min(n_gates, rng.randint(1, 3))):
            x = s1[n_in + g] if rng.random() < 0.5 else s2[n_in + g]
            clauses.append([x if rng.random() < 0.5 else -x])
    return Formula(next_var - 1, clauses, "circuit", notes=notes)


def edge_empty(rng, max_vars):
    return Formula(rng.choice([0, 0, 1, 5, 17]), [], "edge-empty", expected="SAT")


def edge_single(rng, max_vars):
    n = rng.randint(1, 4)
    shapes = [
        [[1]], [[-1]], [[1, -1]], [[1], [-1]], [[1, 1]], [[1, 2]], [[1], [1]], [[-1, -1, -1]],
    ]
    clauses = [c[:] for c in rng.choice(shapes)]
    f = Formula(max(n, max(abs(l) for c in clauses for l in c)), clauses, "edge-single")
    f.expected = "UNSAT" if clauses == [[1], [-1]] else "SAT"
    return f


def edge_empty_clause(rng, max_vars):
    base = gen_ksat(rng, min(max_vars, 40)) if rng.random() < 0.8 else Formula(rng.randint(0, 3), [], "")
    clauses = base.clauses
    clauses.insert(rng.randint(0, len(clauses)), [])
    return Formula(base.nvars, clauses, "edge-empty-clause", expected="UNSAT")


def edge_unit_chain(rng, max_vars):
    """x1, x1 -> x2 -> ... -> xL (binary implications), optionally closed by -xL
    (UNSAT by unit propagation alone), with optional ternary noise."""
    length = rng.randint(1, min(max_vars, 150))
    order = list(range(1, length + 1))
    if rng.random() < 0.5:
        rng.shuffle(order)
    signs = {v: rng.choice([1, -1]) for v in order}
    lit = lambda v: v * signs[v]  # noqa: E731
    clauses = [[lit(order[0])]]
    for a, b in zip(order, order[1:]):
        clauses.append([-lit(a), lit(b)])
    unsat = rng.random() < 0.5
    if unsat:
        clauses.append([-lit(order[-1])])
    expected = "UNSAT" if unsat else "SAT"
    if rng.random() < 0.4 and length >= 3:
        noise = _ksat_clauses(rng, length, rng.randint(1, 2 * length), 3)
        if not unsat:  # keep SAT: each noise clause gets a literal true under the forced assignment
            for c in noise:
                if not any(l == lit(abs(l)) for l in c):
                    c[0] = lit(abs(c[0]))
        clauses += noise
    rng.shuffle(clauses)
    return Formula(length, clauses, "edge-unit-chain", expected=expected)


def edge_dups(rng, max_vars):
    base = gen_ksat(rng, min(max_vars, 100)) if rng.random() < 0.6 else gen_layered(rng, min(max_vars, 100))
    f = _mutate(rng, base, force=True)
    f.family = "edge-dups"
    return f


def edge_unused(rng, max_vars):
    """Sparse variable numbering and a header larger than the largest used variable."""
    base = gen_ksat(rng, min(max_vars, 100))
    n = base.nvars
    spread = rng.randint(n, 4 * n + 10)
    used = sorted(rng.sample(range(1, spread + 1), n))
    clauses = [[used[abs(l) - 1] * (1 if l > 0 else -1) for l in c] for c in base.clauses]
    return Formula(spread + rng.randint(0, 50), clauses, "edge-unused")


def edge_long(rng, max_vars):
    n = rng.randint(50, 600)
    clauses = []
    for _ in range(rng.randint(1, 8)):
        clauses.append(_random_clause(rng, n, rng.randint(min(50, n), n)))
    if rng.random() < 0.7:
        m = round(THRESHOLD[3] * rng.uniform(0.7, 1.1) * min(n, 120))
        clauses += _ksat_clauses(rng, min(n, 120), m, 3)
    rng.shuffle(clauses)
    return Formula(n, clauses, "edge-long")


def edge_2sat(rng, max_vars):
    """Pure binary formula: equivalence cycles (x1 -> x2 -> ... -> x1, possibly
    through negations), implication chains, random binary clauses."""
    n = _log_uniform_int(rng, 4, min(max_vars, 200))
    clauses = []
    vs = list(range(1, n + 1))
    rng.shuffle(vs)
    i = 0
    while i < n:
        size = rng.randint(2, 12)
        cyc = [v * rng.choice([1, -1]) for v in vs[i:i + size]]
        i += size
        if len(cyc) < 2:
            continue
        for a, b in zip(cyc, cyc[1:] + cyc[:1]):
            clauses.append([-a, b])  # a -> b
    for _ in range(rng.randint(0, round(n * rng.uniform(0.2, 1.1)))):
        clauses.append(_random_clause(rng, n, 2))
    rng.shuffle(clauses)
    return Formula(n, clauses, "edge-2sat")


def edge_units(rng, max_vars):
    base = gen_ksat(rng, min(max_vars, 150)) if rng.random() < 0.7 else gen_layered(rng, min(max_vars, 150))
    n = base.nvars
    k = rng.randint(1, max(1, n // 8))
    model = {v: rng.choice([1, -1]) for v in range(1, n + 1)}
    units = [[v * model[v]] for v in rng.sample(range(1, n + 1), min(k, n))]
    if rng.random() < 0.2:
        v = rng.randint(1, n)
        units += [[v], [-v]]
    clauses = base.clauses + units
    rng.shuffle(clauses)
    return Formula(n, clauses, "edge-units")


EDGE = {
    "edge-empty": edge_empty,
    "edge-single": edge_single,
    "edge-empty-clause": edge_empty_clause,
    "edge-unit-chain": edge_unit_chain,
    "edge-dups": edge_dups,
    "edge-unused": edge_unused,
    "edge-long": edge_long,
    "edge-2sat": edge_2sat,
    "edge-units": edge_units,
}

# Family -> (generator, weight in the default mix)
FAMILIES = {
    "ksat": (gen_ksat, 0.30),
    "circuit": (gen_circuit, 0.08),
    "mixed": (gen_mixed, 0.10),
    "layered": (gen_layered, 0.32),
    "php": (gen_php, 0.03),
    "parity": (gen_parity, 0.04),
    **{name: (fn, 0.13 / len(EDGE)) for name, fn in EDGE.items()},
}


# --------------------------------------------------------------------------- mutators


def _mutate(rng: random.Random, f: Formula, force: bool = False) -> Formula:
    """Low-probability syntactic noise. Keeps satisfiability except for the
    extra units (which may make the formula UNSAT; status is then unknown)."""
    p = 1.0 if force else 0.04
    clauses = [c[:] for c in f.clauses]
    applied = []
    if clauses and rng.random() < p:  # duplicate literals inside clauses
        for c in rng.sample(clauses, max(1, len(clauses) // 10)):
            if c:
                c.insert(rng.randint(0, len(c)), rng.choice(c))
        applied.append("duplicate-literals")
    if f.nvars and rng.random() < p:  # tautological clauses
        for _ in range(rng.randint(1, 5)):
            c = _random_clause(rng, f.nvars, rng.randint(1, 4))
            v = rng.randint(1, f.nvars)
            c += [v, -v]
            rng.shuffle(c)
            clauses.insert(rng.randint(0, len(clauses)), c)
        applied.append("tautologies")
    if clauses and rng.random() < p:  # duplicate clauses
        for c in rng.sample(clauses, max(1, len(clauses) // 8)):
            d = c[:]
            if rng.random() < 0.5:
                rng.shuffle(d)
            clauses.insert(rng.randint(0, len(clauses)), d)
        applied.append("duplicate-clauses")
    nvars = f.nvars
    if rng.random() < p:  # header larger than the largest used variable
        nvars += rng.randint(1, 40)
        applied.append("unused-vars")
    expected = f.expected
    if f.nvars and rng.random() < p / 2:  # a few units (status may change)
        for _ in range(rng.randint(1, 4)):
            clauses.insert(rng.randint(0, len(clauses)), _random_clause(rng, f.nvars, 1))
        applied.append("units")
        if expected == "SAT":
            expected = None
    if not applied:
        return f
    g = Formula(nvars, clauses, f.family, f.seed, expected, f.notes + ["mutators: " + ",".join(applied)])
    return g


# --------------------------------------------------------------------------- entry points


def family_names() -> list[str]:
    return list(FAMILIES)


def _select(families: list[str] | None) -> tuple[list[str], list[float]]:
    names = family_names()
    if families:
        chosen = []
        for f in families:
            if f == "edge":
                chosen += list(EDGE)
            elif f in FAMILIES:
                chosen.append(f)
            else:
                raise ValueError(f"unknown family {f!r}; known: edge, {', '.join(names)}")
        names = chosen
    return names, [FAMILIES[n][1] for n in names]


def generate(seed: int, families: list[str] | None = None, max_vars: int = 200) -> Formula:
    """The formula for `seed` (deterministic). `families` restricts the mix
    ("edge" selects all edge-* families)."""
    rng = random.Random(f"popso-sat-gen-{seed}")
    names, weights = _select(families)
    name = rng.choices(names, weights=weights)[0]
    f = FAMILIES[name][0](rng, max_vars)
    if not name.startswith("edge-"):
        f = _mutate(rng, f)
    f.seed = seed
    return f


def _stats(args) -> None:
    from collections import Counter, defaultdict

    from pysat.solvers import Solver

    fams = args.family.split(",") if args.family else None
    count = Counter()
    status = defaultdict(Counter)
    times = defaultdict(list)
    sizes = defaultdict(list)
    t0 = time.time()
    gen_time = 0.0
    for s in range(args.seed, args.seed + args.count):
        g0 = time.time()
        f = generate(s, fams, args.max_vars)
        gen_time += time.time() - g0
        fam = f.family
        count[fam] += 1
        sizes[fam].append((f.nvars, len(f.clauses)))
        t = time.time()
        if any(len(c) == 0 for c in f.clauses):
            st = "UNSAT"
        else:
            with Solver(name="cadical195", bootstrap_with=f.clauses) as sol:
                st = "SAT" if sol.solve() else "UNSAT"
        times[fam].append(time.time() - t)
        status[fam][st] += 1
        if f.expected and f.expected != st:
            print(f"seed {s}: expected {f.expected}, reference says {st}", file=sys.stderr)
    total = sum(count.values())
    print(f"{total} formulas, generation {gen_time / total * 1000:.2f} ms/formula, wall {time.time() - t0:.1f}s")
    print(f"{'family':22} {'count':>6} {'SAT':>6} {'UNSAT':>6} {'avg n':>7} {'avg m':>7} {'ref ms avg':>10} {'ref ms max':>10}")
    for fam in sorted(count):
        ns = [a for a, _ in sizes[fam]]
        ms = [b for _, b in sizes[fam]]
        print(f"{fam:22} {count[fam]:6} {status[fam]['SAT']:6} {status[fam]['UNSAT']:6} "
              f"{sum(ns) / len(ns):7.1f} {sum(ms) / len(ms):7.1f} "
              f"{sum(times[fam]) / len(times[fam]) * 1000:10.2f} {max(times[fam]) * 1000:10.1f}")
    sat = sum(c["SAT"] for c in status.values())
    print(f"total SAT {sat}  UNSAT {total - sat}")


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--seed", type=int, default=0, help="first seed (default 0)")
    ap.add_argument("--count", type=int, default=1, help="number of formulas (default 1)")
    ap.add_argument("--family", help="comma-separated families to draw from (default: full mix; 'edge' = all edge-*)")
    ap.add_argument("--max-vars", type=int, default=200, help="variable cap for the scalable families (default 200)")
    ap.add_argument("-o", "--output", help="output file (single formula)")
    ap.add_argument("--outdir", help="write <outdir>/fuzz-<seed>.cnf for each seed")
    ap.add_argument("--list", action="store_true", help="list families and their weights")
    ap.add_argument("--stats", action="store_true", help="print family mix / SAT-UNSAT balance / reference time (PySAT)")
    args = ap.parse_args(argv)
    if args.list:
        for name, (_, w) in FAMILIES.items():
            print(f"{name:20} {w:.3f}")
        return 0
    if args.stats:
        _stats(args)
        return 0
    fams = args.family.split(",") if args.family else None
    if args.outdir:
        out = Path(args.outdir)
        out.mkdir(parents=True, exist_ok=True)
        for s in range(args.seed, args.seed + args.count):
            (out / f"fuzz-{s}.cnf").write_text(generate(s, fams, args.max_vars).dimacs())
        return 0
    if args.count != 1:
        ap.error("--count > 1 needs --outdir (or --stats)")
    text = generate(args.seed, fams, args.max_vars).dimacs()
    if args.output:
        Path(args.output).write_text(text)
    else:
        sys.stdout.write(text)
    return 0


if __name__ == "__main__":
    sys.exit(main())
