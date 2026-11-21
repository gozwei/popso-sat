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
  counting   (only with --family) pigeonhole / clique formulas, perfect matching of K_n,
             partition into triples, for --counting: mostly UNSAT, scrambled or not
  circuit    miters of two copies of a random AND/OR/XOR/ITE circuit written in
             different equivalent gate forms (sometimes with one gate changed)
  xorsub     (only with --family) XOR-substituted formulas for --xorsub: random k-CNF,
             pigeonhole, ordering principle, Tseitin or pyramid pebbling with every variable
             (or most) replaced by the XOR of 2 (sometimes 3) new variables, expanded into
             CNF; shuffled numbering, polarities and clause order; sometimes a stray clause
  linmod     (only with --family) linear equations mod 3, 5 or 7 on one-hot domains for
             --linmod (forbidden-tuple clauses), planted or random right-hand sides, sometimes
             scrambled, with extra clauses or a non-linear constraint

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


def _exactly_one_pairs(lits: list[int], clauses: list[list[int]]) -> None:
    for i in range(len(lits)):
        for j in range(i + 1, len(lits)):
            clauses.append([-lits[i], -lits[j]])


AMO_ENCODINGS = ("pairwise", "seq", "commander", "product")


def _at_most_one(lits: list[int], clauses: list[list[int]], enc: str, next_var: int) -> int:
    """At-most-one over lits: pairwise, sequential counter (Sinz), commander (groups of three,
    commanders recursively) or product (row and column variables). Returns the next free
    variable."""
    n = len(lits)
    if n <= 1:
        return next_var
    if enc == "pairwise" or n <= 3:
        _exactly_one_pairs(lits, clauses)
        return next_var
    if enc == "seq":
        s = list(range(next_var, next_var + n - 1))
        clauses.append([-lits[0], s[0]])
        for i in range(1, n - 1):
            clauses += [[-lits[i], s[i]], [-s[i - 1], s[i]], [-lits[i], -s[i - 1]]]
        clauses.append([-lits[-1], -s[-1]])
        return next_var + n - 1
    if enc == "commander":
        commanders = []
        for g in range(0, n, 3):
            group = lits[g:g + 3]
            c = next_var
            next_var += 1
            commanders.append(c)
            _exactly_one_pairs(group, clauses)
            clauses += [[-x, c] for x in group]
            clauses.append([-c] + group)
        return _at_most_one(commanders, clauses, "commander", next_var)
    side = 1
    while side * side < n:
        side += 1
    rows = list(range(next_var, next_var + (n + side - 1) // side))
    next_var += len(rows)
    cols = list(range(next_var, next_var + side))
    next_var += side
    for i, x in enumerate(lits):
        clauses += [[-x, rows[i // side]], [-x, cols[i % side]]]
    _exactly_one_pairs(rows, clauses)
    _exactly_one_pairs(cols, clauses)
    return next_var


def gen_counting(rng: random.Random, max_vars: int) -> Formula:
    """Counting principles for --counting (not in the default mix): pigeonhole (plain, functional,
    clique formulas with k variables per pair), perfect matching of K_n, partition of n points into
    triples, clique-colouring, graph colouring with a planted clique (a pigeonhole inside a larger
    formula), relativized pigeonhole (also with second in-use variables), pigeonhole on a sparse graph. Sometimes satisfiable (pigeons <= holes, even n, 3 | n, clique <= colours), with
    the long clauses cut into clauses of three literals, scrambled
    (renamed variables, flipped polarities), or with one clause added or removed."""
    kind = rng.choice(["php", "fphp", "clique", "matching", "triples", "clqcl", "gcol", "rphp", "sphp"])
    sat = rng.random() < 0.25
    clauses: list[list[int]] = []
    # At-most-one constraints over auxiliary variables (pigeonholes, matchings, triples) half the time.
    enc = rng.choice(AMO_ENCODINGS[1:]) if rng.random() < 0.5 else "pairwise"
    amo_groups: list[list[int]] = []
    if kind in ("php", "fphp", "clique"):
        if kind == "clique":
            parts, size = rng.randint(2, 4), rng.randint(1, 3)
        else:
            parts, size = rng.randint(3, 6), 1
        # (the reference needs seconds from PHP 7 -> 6 on, and 20 s for 8 -> 7)
        pigeons = rng.randint(max(2, parts - 1), parts) if sat else parts + (1 if parts > 4 else rng.choice([1, 2]))
        holes = parts
        verts = parts * size
        x = lambda p, v: p * verts + v + 1  # noqa: E731
        for p in range(pigeons):
            row = [x(p, v) for v in range(verts)]
            clauses.append(row)
            if kind == "fphp":
                amo_groups.append(row)
            elif kind != "php":
                _exactly_one_pairs(row, clauses)
        if kind == "clique":
            for p in range(pigeons):
                for q in range(p + 1, pigeons):
                    for v in range(verts):
                        for w in range(verts):
                            if v // size == w // size:
                                clauses.append([-x(p, v), -x(q, w)])
        else:
            for v in range(verts):
                amo_groups.append([x(p, v) for p in range(pigeons)])
        nvars = pigeons * verts
        name = f"{kind}{pigeons}x{holes}" + (f"x{size}" if kind == "clique" else "")
        unsat = pigeons > holes
    elif kind == "matching":
        n = rng.choice([4, 6, 8]) if sat else rng.choice([5, 7, 9])
        e, nvars = {}, 0
        for a in range(n):
            for b in range(a + 1, n):
                nvars += 1
                e[a, b] = e[b, a] = nvars
        for a in range(n):
            row = [e[a, b] for b in range(n) if b != a]
            clauses.append(row)
            amo_groups.append(row)
        name, unsat = f"matching{n}", n % 2 == 1
    elif kind == "clqcl":
        n, m = rng.randint(4, 5), 3  # (the reference needs 1 s for n = 5, 10 s for n = 6)
        k = rng.randint(2, m) if sat else rng.choice([m + 1, m + 1, m + 2])
        e, nvars = {}, 0
        for u in range(n):
            for v in range(u + 1, n):
                nvars += 1
                e[u, v] = e[v, u] = nvars
        q = [[nvars + i * n + u + 1 for u in range(n)] for i in range(k)]
        nvars += k * n
        r = [[nvars + u * m + c + 1 for c in range(m)] for u in range(n)]
        nvars += n * m
        for row in q:
            clauses.append(row)
            _exactly_one_pairs(row, clauses)
        for u in range(n):
            for i in range(k):
                for j in range(i + 1, k):
                    clauses.append([-q[i][u], -q[j][u]])
        for i in range(k):
            for j in range(i + 1, k):
                for u in range(n):
                    for v in range(n):
                        if u != v:
                            clauses.append([-q[i][u], -q[j][v], e[u, v]])
        for row in r:
            clauses.append(row)
            _exactly_one_pairs(row, clauses)
        for u in range(n):
            for v in range(u + 1, n):
                for c in range(m):
                    clauses.append([-e[u, v], -r[u][c], -r[v][c]])
        name, unsat = f"clqcl{n}x{k}x{m}", k > m
    elif kind == "rphp":
        n = rng.randint(3, 5)
        r = n + (rng.choice([0, 0, 1, 2]) if n < 5 else 0)  # (the reference: 4 to 9 s for 5 pigeons, 7 places)
        h = rng.randint(n, n + 1) if sat else n - 1
        pv = lambda i, u: i * r + u + 1  # noqa: E731
        used = lambda u: n * r + u + 1  # noqa: E731
        qv = lambda u, k: n * r + r + u * h + k + 1  # noqa: E731
        nvars = n * r + r + r * h
        for i in range(n):
            clauses.append([pv(i, u) for u in range(r)])
        for u in range(r):
            for i in range(n):
                for j in range(i + 1, n):
                    clauses.append([-pv(i, u), -pv(j, u)])
                clauses.append([-pv(i, u), used(u)])
            clauses.append([-used(u)] + [qv(u, k) for k in range(h)])
        for u in range(r):
            for v in range(u + 1, r):
                for k in range(h):
                    clauses.append([-used(u), -used(v), -qv(u, k), -qv(v, k)])
        name, unsat = f"rphp{n}x{r}x{h}", n > h
        if rng.random() < 0.3:  # a second in-use variable on some places, excluded against other places (a_rphp)
            for u in rng.sample(range(r), rng.randint(1, r)):
                nvars += 1
                for i in range(n):
                    clauses.append([-pv(i, u), nvars])
                for v in rng.sample([v for v in range(r) if v != u], rng.randint(1, min(3, r - 1))):
                    for k in range(h):
                        clauses.append([-nvars, -used(v), -qv(u, k), -qv(v, k)])
            name += "+2nd"
    elif kind == "gcol":
        n, m = rng.randint(8, 14), rng.randint(3, 5)
        clique = rng.randint(2, m) if sat else m + 1
        p = rng.uniform(0.1, 0.3 if sat else 0.45)
        x = lambda u, c: u * m + c + 1  # noqa: E731
        nvars = n * m
        amo = rng.random() < 0.5
        for u in range(n):
            row = [x(u, c) for c in range(m)]
            clauses.append(row)
            if amo:
                _exactly_one_pairs(row, clauses)
        for u in range(n):
            for v in range(u + 1, n):
                if (u < clique and v < clique) or rng.random() < p:
                    for c in range(m):
                        clauses.append([-x(u, c), -x(v, c)])
        name = f"gcol{n}x{m}c{clique}"
        unsat = clique > m
        if not unsat:
            sat = None  # (the random edges may still make it unsatisfiable)
    elif kind == "sphp":
        # A pigeonhole system on a sparse graph: a pigeon may use only some of the holes (now and
        # then two of them: a binary pigeon clause), sometimes at most one of them.
        holes = rng.randint(3, 7)
        pigeons = holes + (rng.choice([-1, 0]) if sat else rng.choice([0, 1, 1, 2]))
        p = rng.uniform(0.4, 0.8)
        in_hole: list[list[int]] = [[] for _ in range(holes)]
        nvars = 0
        for _ in range(pigeons):
            hs = [h for h in range(holes) if rng.random() < p]
            if len(hs) < 2:
                hs = sorted(rng.sample(range(holes), 3))
            row = []
            for h in hs:
                nvars += 1
                row.append(nvars)
                in_hole[h].append(nvars)
            clauses.append(row)
            if rng.random() < 0.3:
                amo_groups.append(row)
        amo_groups += [m for m in in_hole if len(m) > 1]
        name, unsat = f"sphp{pigeons}x{holes}", pigeons > holes
        if rng.random() < 0.3:  # the holes' at-least-one clauses too: a perfect matching of the graph
            clauses += [list(m) for m in in_hole if len(m) > 1]
            name += "+both"
        if rng.random() < 0.3:  # other exclusions between the pigeons' variables
            for _ in range(rng.randint(1, 4)):
                x, y = rng.sample(range(1, nvars + 1), 2)
                clauses.append([-x, -y])
            name += "+excl"
        if rng.random() < 0.4:  # unit clauses: a pigeon in a hole (the others lose it), or not in it
            for _ in range(rng.randint(1, 2)):
                clauses.append([rng.randint(1, nvars) * rng.choice([1, -1])])
            name += "+units"
            unsat = False
        if rng.random() < 0.3:  # each at-most-one constraint in an encoding of its own
            nv = nvars + 1
            for g in amo_groups:
                nv = _at_most_one(g, clauses, rng.choice(AMO_ENCODINGS), nv)
            nvars = nv - 1
            amo_groups = []
            name += "-mixed"
        if not unsat:
            sat = None  # (a set of pigeons may still have too few holes)
    else:
        n = rng.choice([6]) if sat else rng.choice([4, 5, 7, 8])
        through: list[list[int]] = [[] for _ in range(n)]
        nvars = 0
        for a in range(n):
            for b in range(a + 1, n):
                for c in range(b + 1, n):
                    nvars += 1
                    for p in (a, b, c):
                        through[p].append(nvars)
        for row in through:
            clauses.append(row)
            amo_groups.append(row)
        name, unsat = f"triples{n}", n % 3 != 0
    if amo_groups:
        nv = nvars + 1
        for g in amo_groups:
            nv = _at_most_one(g, clauses, enc, nv)
        nvars = nv - 1
        if enc != "pairwise":
            name += f"-{enc}"
    expected = "UNSAT" if unsat else ("SAT" if sat is not None else None)
    r = rng.random()
    if r < 0.15:  # one more clause: still unsatisfiable if it was
        clauses.append(_random_clause(rng, nvars, rng.randint(2, 3)))
        name += "+1"
        if not unsat:
            expected = None
    elif r < 0.25 and len(clauses) > 1:  # one clause less: may become satisfiable
        del clauses[rng.randrange(len(clauses))]
        name += "-1"
        if unsat:
            expected = None
    if rng.random() < 0.2:  # clauses of four or more literals cut into clauses of three, chained by new variables
        cut: list[list[int]] = []
        for c in clauses:
            if len(c) <= 3:
                cut.append(c)
                continue
            nvars += 1
            cut.append([c[0], c[1], nvars])
            for l in c[2:-2]:
                cut.append([-nvars, l, nvars + 1])
                nvars += 1
            cut.append([-nvars, c[-2], c[-1]])
        clauses = cut
        name += "-split3"
    if rng.random() < 0.5:
        perm = list(range(1, nvars + 1))
        rng.shuffle(perm)
        flip = [rng.choice([1, -1]) for _ in range(nvars)]
        clauses = [[perm[abs(l) - 1] * flip[abs(l) - 1] * (1 if l > 0 else -1) for l in c] for c in clauses]
        for c in clauses:
            rng.shuffle(c)
        rng.shuffle(clauses)
        name += "-scrambled"
    return Formula(nvars, clauses, f"counting-{name}", expected=expected)


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


def gen_ternpairs(rng: random.Random, max_vars: int) -> Formula:
    """4-variable XORs (8 clauses each), binary equivalences between variables of the same XOR
    (substitution turns those XORs into ternary clause pairs (a b c) (a b -c)), explicit ternary
    pairs, AND gates over XOR outputs and random ternary clauses: exercises --congruencetern."""
    n = rng.randint(8, max(8, min(max_vars, 60)))
    clauses: list[list[int]] = []
    for _ in range(rng.randint(2, n // 2)):
        vs = rng.sample(range(1, n + 1), 4)
        par = rng.randint(0, 1)
        for mask in range(16):
            if bin(mask).count("1") % 2 != par:
                clauses.append([v if mask >> i & 1 else -v for i, v in enumerate(vs)])
        if rng.random() < 0.6:
            x, y = rng.sample(vs, 2)
            sy = y if rng.random() < 0.5 else -y
            clauses += [[-x, sy], [x, -sy]]
    for _ in range(rng.randint(0, n // 3)):
        a, b, c = rng.sample(range(1, n + 1), 3)
        a, b = (a if rng.random() < 0.5 else -a), (b if rng.random() < 0.5 else -b)
        clauses += [[a, b, c], [a, b, -c]]
    for _ in range(rng.randint(0, n // 4)):
        o, i, j = rng.sample(range(1, n + 1), 3)
        clauses += [[-o, i], [-o, j], [o, -i, -j]]
    clauses += _ksat_clauses(rng, n, rng.randint(0, 2 * n), 3)
    rng.shuffle(clauses)
    return Formula(n, clauses, "ternpairs")


def gen_truthtable(rng: random.Random, max_vars: int) -> Formula:
    """Random gates encoded by their forbidden assignments, as in the random-circuits family: a
    gate with i inputs and o outputs is every (input, output) assignment but the valid ones, one
    clause of i + o literals each (sometimes a relation: some valid rows allow two outputs, some
    forbidden ones are left out), gates fed by inputs and earlier outputs, then output constraints
    and random clauses. Exercises --mergepairs (pairs of clauses that differ in one sign)."""
    n_in = rng.randint(3, 8)
    nv = n_in
    pool = list(range(1, n_in + 1))
    clauses: list[list[int]] = []
    for _ in range(rng.randint(1, 6)):
        ni = rng.randint(1, min(4, len(pool)))
        no = rng.randint(1, 3)
        ins = rng.sample(pool, ni)
        outs = list(range(nv + 1, nv + no + 1))
        nv += no
        relation = rng.random() < 0.3
        for row in range(1 << ni):
            good = {rng.randrange(1 << no)}
            if relation and rng.random() < 0.3:
                good.add(rng.randrange(1 << no))
            for out in range(1 << no):
                if out in good or (relation and rng.random() < 0.1):
                    continue
                cl = [-v if row >> i & 1 else v for i, v in enumerate(ins)]
                cl += [-v if out >> i & 1 else v for i, v in enumerate(outs)]
                clauses.append(cl)
        pool += outs
    for _ in range(rng.randint(0, 3)):
        v = rng.choice(pool[n_in:] or pool)
        clauses.append([v if rng.random() < 0.5 else -v])
    clauses += _ksat_clauses(rng, nv, rng.randint(0, nv), 3)
    for cl in clauses:
        rng.shuffle(cl)
    rng.shuffle(clauses)
    return Formula(nv, clauses, "truthtable")


# ----- XOR substitution


def xor_substitute(rng: random.Random, nvars: int, clauses: list[list[int]], p3: float = 0.15,
                   p1: float = 0.1) -> tuple[int, list[list[int]]]:
    """Replaces variable x (1..nvars) by the XOR of a tuple of 2 (or 3, or 1) new variables plus a
    random constant, expands every clause completely, and shuffles variable numbers, literal
    order and clause order. Satisfiability is preserved."""
    sizes = [0] + [3 if rng.random() < p3 else (1 if rng.random() < p1 else 2) for _ in range(nvars)]
    total = sum(sizes)
    ids = list(range(1, total + 1))
    rng.shuffle(ids)
    tuples, flips, k = [[]], [0], 0
    for x in range(1, nvars + 1):
        tuples.append(ids[k:k + sizes[x]])
        k += sizes[x]
        flips.append(rng.randint(0, 1))
    out = []
    for c in clauses:
        acc = [[]]
        for lit in c:
            t = tuples[abs(lit)]
            if len(t) == 1 and not flips[abs(lit)]:
                parts = [[t[0] if lit > 0 else -t[0]]]
            else:
                false_value = (0 if lit > 0 else 1) ^ flips[abs(lit)]  # XOR(t) when lit is false
                parts = []
                for m in range(1 << len(t)):
                    if bin(m).count("1") % 2 != false_value:
                        continue
                    parts.append([-v if (m >> i) & 1 else v for i, v in enumerate(t)])
            acc = [a + p for a in acc for p in parts]
        for z in acc:
            rng.shuffle(z)
            out.append(z)
    rng.shuffle(out)
    return total, out


def _ordering_principle(m: int) -> tuple[int, list[list[int]]]:
    x = lambda i, j: i * m + j + 1  # noqa: E731
    cl = []
    for i in range(m):
        pred = []
        for j in range(m):
            if j == i:
                continue
            pred.append(x(j, i))
            if i < j:
                cl += [[-x(i, j), -x(j, i)], [x(i, j), x(j, i)]]
            for k in range(m):
                if k != i and k != j:
                    cl.append([-x(i, j), -x(j, k), x(i, k)])
        cl.append(pred)
    return m * m, cl


def _pyramid_pebbling(h: int) -> tuple[int, list[list[int]]]:
    """Pebbling formula of a pyramid of height h: sources true, each node implied by its two
    predecessors, the sink false (UNSAT)."""
    ids = {}
    for r in range(h):
        for i in range(r + 1):
            ids[r, i] = len(ids) + 1
    cl = [[ids[h - 1, i]] for i in range(h)]  # the bottom row are the sources
    for r in range(h - 1):
        for i in range(r + 1):
            cl.append([-ids[r + 1, i], -ids[r + 1, i + 1], ids[r, i]])
    cl.append([-ids[0, 0]])
    return len(ids), cl


def _tseitin_small(rng: random.Random, n: int, odd: bool) -> tuple[int, list[list[int]]]:
    """Tseitin parity formula on a random connected graph (cycle plus chords), an edge variable
    per edge and a charge per vertex: odd total charge UNSAT, even SAT."""
    edges = [(i, (i + 1) % n) for i in range(n)]
    for _ in range(rng.randint(0, n // 2)):
        a, b = rng.sample(range(n), 2)
        if (a, b) not in edges and (b, a) not in edges:
            edges.append((a, b))
    charge = [rng.randint(0, 1) for _ in range(n)]
    if (sum(charge) % 2 == 1) != odd:
        charge[0] ^= 1
    inc = [[] for _ in range(n)]
    for e, (a, b) in enumerate(edges):
        inc[a].append(e + 1)
        inc[b].append(e + 1)
    cl = []
    for v in range(n):
        xs = inc[v]
        for m in range(1 << len(xs)):
            if bin(m).count("1") % 2 != charge[v]:
                cl.append([-x if (m >> i) & 1 else x for i, x in enumerate(xs)])
    return len(edges), cl


def gen_xorsub(rng: random.Random, max_vars: int) -> Formula:
    kind = rng.choice(["ksat", "php", "op", "tseitin", "pebbling"])
    expected = None
    if kind == "ksat":
        n = rng.randint(4, 14)
        k = rng.choice([2, 3])
        m = int(n * THRESHOLD[k] * rng.uniform(0.7, 1.3))
        nvars, base = n, _ksat_clauses(rng, n, max(1, m), k)
    elif kind == "php":
        holes = rng.randint(2, 4)
        pigeons = holes + 1 if rng.random() < 0.8 else holes
        var = lambda p, h: p * holes + h + 1  # noqa: E731
        base = [[var(p, h) for h in range(holes)] for p in range(pigeons)]
        for h in range(holes):
            for p in range(pigeons):
                for q in range(p + 1, pigeons):
                    base.append([-var(p, h), -var(q, h)])
        nvars, expected = pigeons * holes, "UNSAT" if pigeons > holes else "SAT"
    elif kind == "op":
        m = rng.randint(3, 4)
        nvars, base = _ordering_principle(m)
        expected = "UNSAT"
        if rng.random() < 0.4:
            base.pop()  # the last element needs no predecessor: SAT
            expected = "SAT"
    elif kind == "tseitin":
        odd = rng.random() < 0.6
        nvars, base = _tseitin_small(rng, rng.randint(4, 7), odd)
        expected = "UNSAT" if odd else "SAT"
    else:
        nvars, base = _pyramid_pebbling(rng.randint(2, 4))
        expected = "UNSAT"
        if rng.random() < 0.3:
            base.pop()  # no sink clause: SAT
            expected = "SAT"
    p3 = rng.choice([0.0, 0.0, 0.15, 0.4])
    p1 = rng.choice([0.0, 0.0, 0.1, 0.3])
    total, clauses = xor_substitute(rng, nvars, base, p3, p1)
    notes = [f"base {kind}, {nvars} variables, {len(base)} clauses; p3 {p3}, p1 {p1}"]
    if clauses and rng.random() < 0.1:  # a stray clause: some groups incomplete or extra
        clauses.append(_random_clause(rng, total, rng.randint(2, 4)))
        notes.append("stray clause")
        if expected == "SAT":
            expected = None
    return Formula(total, clauses, f"xorsub-{kind}", expected=expected, notes=notes)


def gen_linmod(rng: random.Random, max_vars: int) -> Formula:
    """Linear equations mod p (3, 5 or 7) on one-hot domains for --linmod (not in the default
    mix): each domain is an exactly-one group (positive clause + pairwise at-most-one), each
    equation over k domains forbids the p^k - p^(k-1) tuples that violate it with one clause each
    (as the sc2026 linear-equations family). Planted solution (SAT) or random right-hand sides;
    sometimes flipped domain polarities, scrambled numbering, extra random clauses, an incomplete
    equation (a forbidden tuple missing) or a non-linear constraint."""
    p = rng.choice([3, 3, 3, 5, 7])
    kmax = {3: 4, 5: 3, 7: 2}[p]
    nd = rng.randint(2, max(2, min(30, max_vars // p)))
    neq = rng.randint(1, nd + 2)
    planted = rng.random() < 0.6
    sol = [rng.randrange(p) for _ in range(nd)]
    var = lambda d, v: d * p + v + 1  # noqa: E731
    clauses: list[list[int]] = []
    for d in range(nd):
        lits = [var(d, v) for v in range(p)]
        clauses.append(lits[:])
        _exactly_one_pairs(lits, clauses)
    notes = [f"p {p}, {nd} domains, {neq} equations, planted {planted}"]
    expected = "SAT" if planted else None
    for e in range(neq):
        k = rng.randint(2, min(kmax, nd))
        ds = rng.sample(range(nd), k)
        coef = [rng.randrange(1, p) for _ in range(k)]
        rhs = sum(c * sol[d] for c, d in zip(coef, ds)) % p if planted else rng.randrange(p)
        tuples = []
        for idx in range(p ** k):
            t, x = [], idx
            for _ in range(k):
                t.append(x % p)
                x //= p
            if sum(c * v for c, v in zip(coef, t)) % p != rhs:
                tuples.append(t)
        if rng.random() < 0.05 and tuples:  # incomplete: one forbidden tuple missing (not linear)
            tuples.pop(rng.randrange(len(tuples)))
            notes.append(f"equation {e} incomplete")
        elif rng.random() < 0.05:  # one extra forbidden tuple (not linear, may be UNSAT)
            t = [rng.randrange(p) for _ in range(k)]
            if t not in tuples:
                tuples.append(t)
                expected = None
                notes.append(f"equation {e} extra tuple")
        for t in tuples:
            clauses.append([-var(d, v) for d, v in zip(ds, t)])
    nvars = nd * p
    if rng.random() < 0.2:  # extra random clauses over the domain variables and new ones
        extra = rng.randint(1, 6)
        nvars += extra
        for _ in range(rng.randint(1, 3 * extra)):
            clauses.append(_random_clause(rng, nvars, rng.randint(2, 4)))
        expected = None
        notes.append("extra clauses")
    if rng.random() < 0.4:  # scramble numbering and polarities, shuffle clauses and literals
        perm = list(range(1, nvars + 1))
        rng.shuffle(perm)
        flip = [rng.random() < 0.3 for _ in range(nvars + 1)]
        clauses = [[(perm[abs(l) - 1] if l > 0 else -perm[abs(l) - 1]) * (-1 if flip[abs(l)] else 1) for l in c]
                   for c in clauses]
        for c in clauses:
            rng.shuffle(c)
        rng.shuffle(clauses)
        notes.append("scrambled")
    return Formula(nvars, clauses, f"linmod-p{p}", expected=expected, notes=notes)


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
    "counting": (gen_counting, 0.0),  # not in the default mix (its seeds stay as they were)
    "xorsub": (gen_xorsub, 0.0),  # not in the default mix
    "linmod": (gen_linmod, 0.0),  # not in the default mix
    "ternpairs": (gen_ternpairs, 0.0),  # not in the default mix
    "truthtable": (gen_truthtable, 0.0),  # not in the default mix
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
        # Families outside the default mix get a weight when they are asked for.
        return names, [FAMILIES[n][1] or 0.05 for n in names]
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
