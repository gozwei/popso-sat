"""Instance families with known status (by construction where possible).

Every generator takes a deterministic Rng and parameters and returns a Formula.  `status` is
'sat' / 'unsat' when it is known by construction (or by exact GF(2) elimination), or None when a
reference solve has to decide it (random k-SAT, random-graph coloring).

Families (the family name is the file-name prefix, without '_'):
  rand3sat, rand5sat  uniform random k-SAT at the given clause/variable ratio
  php                 pigeonhole PHP(n+1, n), at-most-one pairwise (or enc: seq / commander /
                      product, over auxiliary variables)                            UNSAT
  xorsat              random 3-XORSAT (direct CNF of each equation); status by GF(2) elimination
  xorchain            two XOR chains over the same inputs in different orders, outputs forced
                      different (Tseitin)                                           UNSAT
  tseitin             Tseitin parity formula on a random d-regular graph: odd total charge
                      UNSAT, even total charge SAT
  coloring            k-coloring: planted k-partite graph (SAT) or random G(n, m) (reference)
  queens              n-queens (pairwise at-most-one on rows, columns, diagonals)    SAT
  sudoku              fixed 9x9 puzzles, or a planted N^2 x N^2 grid with holes      SAT
  addereq             miter of two differently built n-bit adders; buggy variant SAT, else UNSAT
  multeq              miter of a*b and b*a array multipliers; buggy variant SAT, else UNSAT
  counter             BMC of an n-step counter with enable inputs: reach value v after T steps
                      (SAT iff v <= T)
  xorsub*             XOR-substituted formulas (every variable replaced by the XOR of d new
                      variables, each clause expanded, numbering / polarities / order shuffled):
                      xorsubop ordering principle (UNSAT, or SAT without one predecessor
                      clause), xorsubphp pigeonhole (UNSAT), xorsubtseitin (by charge),
                      xorsubpebbling pyramid pebbling (UNSAT), xorsubrand3sat (reference)
"""

from __future__ import annotations

import hashlib
import random
from dataclasses import dataclass, field
from itertools import combinations


# ------------------------------------------------------------------ rng / formula

class Rng:
    """Deterministic RNG independent of Python's random-module helper implementations: only
    Random.getrandbits (stable for integer seeds) is used."""

    def __init__(self, *key):
        seed = int.from_bytes(hashlib.sha256("/".join(map(str, key)).encode()).digest()[:8], "big")
        self._r = random.Random(seed)

    def below(self, n: int) -> int:
        if n <= 1:
            return 0
        k = n.bit_length()
        while True:
            x = self._r.getrandbits(k)
            if x < n:
                return x

    def randint(self, a: int, b: int) -> int:
        return a + self.below(b - a + 1)

    def coin(self) -> bool:
        return bool(self._r.getrandbits(1))

    def shuffle(self, xs: list):
        for i in range(len(xs) - 1, 0, -1):
            j = self.below(i + 1)
            xs[i], xs[j] = xs[j], xs[i]
        return xs

    def sample(self, n: int, k: int) -> list[int]:
        """k distinct values from range(n)."""
        if k * 4 < n:
            out, seen = [], set()
            while len(out) < k:
                x = self.below(n)
                if x not in seen:
                    seen.add(x)
                    out.append(x)
            return out
        xs = list(range(n))
        for i in range(k):
            j = i + self.below(n - i)
            xs[i], xs[j] = xs[j], xs[i]
        return xs[:k]


@dataclass
class Formula:
    nvars: int
    clauses: list
    status: str | None              # 'sat' / 'unsat' / None (reference solve needed)
    source: str = "construction"    # how the status is known
    comments: list = field(default_factory=list)


class Cnf:
    def __init__(self):
        self.n = 0
        self.clauses: list[list[int]] = []

    def var(self) -> int:
        self.n += 1
        return self.n

    def vars(self, k: int) -> list[int]:
        return [self.var() for _ in range(k)]

    def add(self, *lits):
        self.clauses.append(list(lits))

    def amo_pairwise(self, xs):
        for a, b in combinations(xs, 2):
            self.add(-a, -b)

    def amo(self, xs, enc: str = "pairwise"):
        """At-most-one over xs: pairwise, sequential counter (Sinz), commander (groups of three,
        commanders recursively) or product (row and column variables)."""
        n = len(xs)
        if enc == "pairwise" or n <= 3:
            self.amo_pairwise(xs)
        elif enc == "seq":
            s = self.vars(n - 1)
            self.add(-xs[0], s[0])
            for i in range(1, n - 1):
                self.add(-xs[i], s[i])
                self.add(-s[i - 1], s[i])
                self.add(-xs[i], -s[i - 1])
            self.add(-xs[-1], -s[-1])
        elif enc == "commander":
            commanders = []
            for g in range(0, n, 3):
                group = xs[g:g + 3]
                c = self.var()
                commanders.append(c)
                self.amo_pairwise(group)
                for x in group:
                    self.add(-x, c)
                self.add(-c, *group)
            self.amo(commanders, "commander")
        elif enc == "product":
            side = 1
            while side * side < n:
                side += 1
            rows = self.vars((n + side - 1) // side)
            cols = self.vars(side)
            for i, x in enumerate(xs):
                self.add(-x, rows[i // side])
                self.add(-x, cols[i % side])
            self.amo_pairwise(rows)
            self.amo_pairwise(cols)
        else:
            raise ValueError(f"unknown at-most-one encoding {enc!r}")

    def xor_eq(self, xs, rhs: int):
        """Direct CNF of XOR(xs) == rhs (2^(k-1) clauses)."""
        k = len(xs)
        for mask in range(1 << k):
            # forbidden assignment: bit i of mask = value of xs[i]; parity != rhs
            if bin(mask).count("1") % 2 != rhs:
                self.add(*[-x if (mask >> i) & 1 else x for i, x in enumerate(xs)])


class Circuit(Cnf):
    """Tseitin-encoded gates."""

    def AND(self, a, b):
        o = self.var()
        self.add(-o, a)
        self.add(-o, b)
        self.add(o, -a, -b)
        return o

    def OR(self, a, b):
        o = self.var()
        self.add(o, -a)
        self.add(o, -b)
        self.add(-o, a, b)
        return o

    def XOR(self, a, b):
        o = self.var()
        self.add(-o, a, b)
        self.add(-o, -a, -b)
        self.add(o, -a, b)
        self.add(o, a, -b)
        return o

    def MAJ(self, a, b, c):
        o = self.var()
        for x, y in ((a, b), (a, c), (b, c)):
            self.add(o, -x, -y)
            self.add(-o, x, y)
        return o

    def const(self, value: bool):
        v = self.var()
        self.add(v if value else -v)
        return v

    def miter(self, outs_a, outs_b):
        diffs = [self.XOR(x, y) for x, y in zip(outs_a, outs_b)]
        self.add(*diffs)  # at least one output differs


# ------------------------------------------------------------------ random k-SAT

def rand_ksat(rng: Rng, n: int, k: int, ratio: float) -> Formula:
    m = round(ratio * n)
    cls = []
    for _ in range(m):
        vs = rng.sample(n, k)
        cls.append([(v + 1) if rng.coin() else -(v + 1) for v in vs])
    return Formula(n, cls, None, "reference",
                   [f"uniform random {k}-SAT, n={n}, m={m} (ratio {ratio:g})"])


# ------------------------------------------------------------------ pigeonhole

def php(rng: Rng, n: int, enc: str = "pairwise") -> Formula:
    """n+1 pigeons, n holes; the holes' at-most-one constraints in the encoding enc."""
    c = Cnf()
    p = [[c.var() for _ in range(n)] for _ in range(n + 1)]
    for i in range(n + 1):
        c.add(*p[i])
    for j in range(n):
        c.amo([p[i][j] for i in range(n + 1)], enc)
    note = f"pigeonhole PHP({n + 1},{n})" + ("" if enc == "pairwise" else f", at-most-one {enc}")
    return Formula(c.n, c.clauses, "unsat", "construction", [note])


# ------------------------------------------------------------------ parity

def gf2_consistent(rows, n):
    """rows: list of (bitmask over n vars, rhs). Exact consistency by Gaussian elimination."""
    pivots = {}  # pivot bit -> (mask, rhs)
    for mask, rhs in rows:
        while mask:
            hb = mask.bit_length() - 1
            if hb not in pivots:
                pivots[hb] = (mask, rhs)
                break
            pm, pr = pivots[hb]
            mask ^= pm
            rhs ^= pr
        else:
            if rhs:
                return False
    return True


def xorsat(rng: Rng, n: int, m: int, k: int = 3) -> Formula:
    c = Cnf()
    xs = c.vars(n)
    rows = []
    for _ in range(m):
        vs = rng.sample(n, k)
        rhs = int(rng.coin())
        c.xor_eq([xs[v] for v in vs], rhs)
        mask = 0
        for v in vs:
            mask |= 1 << v
        rows.append((mask, rhs))
    st = "sat" if gf2_consistent(rows, n) else "unsat"
    return Formula(c.n, c.clauses, st, "gf2-elimination",
                   [f"random {k}-XORSAT, n={n}, m={m}; status by GF(2) elimination: {st}"])


def xorchain(rng: Rng, n: int) -> Formula:
    c = Circuit()
    xs = c.vars(n)

    def chain(order):
        acc = xs[order[0]]
        for i in order[1:]:
            acc = c.XOR(acc, xs[i])
        return acc

    a = chain(list(range(n)))
    b = chain(rng.shuffle(list(range(n))))
    c.add(a, b)
    c.add(-a, -b)  # a != b
    return Formula(c.n, c.clauses, "unsat", "construction",
                   [f"two XOR chains over {n} inputs in different orders, outputs forced different"])


# ------------------------------------------------------------------ graphs

def random_regular(rng: Rng, n: int, d: int, tries: int = 10000):
    """Simple connected d-regular graph by the pairing model with rejection."""
    assert n * d % 2 == 0
    for _ in range(tries):
        pts = rng.shuffle([v for v in range(n) for _ in range(d)])
        edges = set()
        ok = True
        for i in range(0, len(pts), 2):
            u, v = pts[i], pts[i + 1]
            if u == v or (min(u, v), max(u, v)) in edges:
                ok = False
                break
            edges.add((min(u, v), max(u, v)))
        if ok and _connected(n, edges):
            return sorted(edges)
    raise RuntimeError(f"no simple connected {d}-regular graph on {n} vertices found")


def _connected(n, edges):
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    seen, stack = {0}, [0]
    while stack:
        u = stack.pop()
        for w in adj[u]:
            if w not in seen:
                seen.add(w)
                stack.append(w)
    return len(seen) == n


def tseitin(rng: Rng, n: int, d: int, odd: bool) -> Formula:
    edges = random_regular(rng, n, d)
    c = Cnf()
    ev = {e: c.var() for e in edges}
    inc = [[] for _ in range(n)]
    for (u, v), x in ev.items():
        inc[u].append(x)
        inc[v].append(x)
    charges = [int(rng.coin()) for _ in range(n)]
    if (sum(charges) % 2 == 1) != odd:
        charges[rng.below(n)] ^= 1
    for v in range(n):
        c.xor_eq(inc[v], charges[v])
    return Formula(c.n, c.clauses, "unsat" if odd else "sat", "construction",
                   [f"Tseitin formula on a random {d}-regular graph, {n} vertices, "
                    f"{'odd' if odd else 'even'} total charge"])


# ------------------------------------------------------------------ XOR substitution

def xor_substitute(rng: Rng, nvars: int, clauses: list, d: int) -> tuple[int, list]:
    """Variable x becomes the XOR of d new variables plus a random constant; each clause is
    expanded completely (2^(d-1) choices per literal); variable numbers, literal order and clause
    order are shuffled. Satisfiability is preserved."""
    total = nvars * d
    ids = rng.shuffle(list(range(1, total + 1)))
    tuples = [None] + [ids[(x - 1) * d:x * d] for x in range(1, nvars + 1)]
    flips = [0] + [int(rng.coin()) for _ in range(nvars)]
    out = []
    for c in clauses:
        acc = [[]]
        for lit in c:
            t = tuples[abs(lit)]
            false_value = (0 if lit > 0 else 1) ^ flips[abs(lit)]
            parts = [[-v if (m >> i) & 1 else v for i, v in enumerate(t)]
                     for m in range(1 << d) if bin(m).count("1") % 2 == false_value]
            acc = [a + p for a in acc for p in parts]
        for z in acc:
            out.append(rng.shuffle(z))
    return total, rng.shuffle(out)


def _ordering(m: int, sat: bool) -> Cnf:
    c = Cnf()
    x = {(i, j): c.var() for i in range(m) for j in range(m) if i != j}
    for i in range(m):
        for j in range(m):
            if i < j:
                c.add(-x[i, j], -x[j, i])
                c.add(x[i, j], x[j, i])
            for k in range(m):
                if len({i, j, k}) == 3:
                    c.add(-x[i, j], -x[j, k], x[i, k])
    for i in range(m - 1 if sat else m):  # element i has a predecessor
        c.add(*[x[j, i] for j in range(m) if j != i])
    return c


def xorsub_op(rng: Rng, m: int, d: int, sat: bool) -> Formula:
    base = _ordering(m, sat)
    n, cl = xor_substitute(rng, base.n, base.clauses, d)
    return Formula(n, cl, "sat" if sat else "unsat", "construction",
                   [f"ordering principle on {m} elements{' without one predecessor clause' if sat else ''}, "
                    f"every variable replaced by the XOR of {d}"])


def xorsub_php(rng: Rng, n: int, d: int) -> Formula:
    base = php(rng, n)
    m, cl = xor_substitute(rng, base.nvars, base.clauses, d)
    return Formula(m, cl, "unsat", "construction", [f"PHP({n + 1}, {n}), every variable replaced by the XOR of {d}"])


def xorsub_tseitin(rng: Rng, n: int, deg: int, odd: bool, d: int) -> Formula:
    base = tseitin(rng, n, deg, odd)
    m, cl = xor_substitute(rng, base.nvars, base.clauses, d)
    return Formula(m, cl, base.status, "construction",
                   base.comments + [f"every variable replaced by the XOR of {d}"])


def xorsub_pebbling(rng: Rng, h: int, d: int) -> Formula:
    """Pyramid of height h: the sources (bottom row) true, every node implied by its two
    predecessors, the top false."""
    c = Cnf()
    node = {(r, i): c.var() for r in range(h) for i in range(r + 1)}
    for i in range(h):
        c.add(node[h - 1, i])
    for r in range(h - 1):
        for i in range(r + 1):
            c.add(-node[r + 1, i], -node[r + 1, i + 1], node[r, i])
    c.add(-node[0, 0])
    m, cl = xor_substitute(rng, c.n, c.clauses, d)
    return Formula(m, cl, "unsat", "construction",
                   [f"pyramid pebbling of height {h}, every variable replaced by the XOR of {d}"])


def xorsub_ksat(rng: Rng, n: int, k: int, ratio: float, d: int) -> Formula:
    base = rand_ksat(rng, n, k, ratio)
    m, cl = xor_substitute(rng, base.nvars, base.clauses, d)
    return Formula(m, cl, None, "reference", [f"random {k}-SAT n={n} ratio {ratio}, every variable replaced by the XOR of {d}"])


def coloring_planted(rng: Rng, n: int, k: int, deg: float) -> Formula:
    col = [i % k for i in range(n)]
    rng.shuffle(col)
    m = round(deg * n / 2)
    edges = set()
    while len(edges) < m:
        u, v = rng.below(n), rng.below(n)
        if u != v and col[u] != col[v]:
            edges.add((min(u, v), max(u, v)))
    f = _coloring_cnf(n, k, sorted(edges))
    f.status, f.source = "sat", "construction"
    f.comments = [f"{k}-coloring of a planted {k}-partite graph, n={n}, m={m}"]
    return f


def coloring_random(rng: Rng, n: int, k: int, deg: float) -> Formula:
    m = round(deg * n / 2)
    edges = set()
    while len(edges) < m:
        u, v = rng.below(n), rng.below(n)
        if u != v:
            edges.add((min(u, v), max(u, v)))
    f = _coloring_cnf(n, k, sorted(edges))
    f.comments = [f"{k}-coloring of a random graph G(n={n}, m={m})"]
    return f


def _coloring_cnf(n, k, edges) -> Formula:
    c = Cnf()
    x = [[c.var() for _ in range(k)] for _ in range(n)]
    for v in range(n):
        c.add(*x[v])
        c.amo_pairwise(x[v])
    for u, v in edges:
        for j in range(k):
            c.add(-x[u][j], -x[v][j])
    return Formula(c.n, c.clauses, None, "reference")


# ------------------------------------------------------------------ puzzles

def queens(rng: Rng, n: int) -> Formula:
    c = Cnf()
    q = [[c.var() for _ in range(n)] for _ in range(n)]
    for i in range(n):
        c.add(*q[i])
        c.amo_pairwise(q[i])
        c.amo_pairwise([q[r][i] for r in range(n)])
    for s in range(2 * n - 1):
        c.amo_pairwise([q[r][s - r] for r in range(n) if 0 <= s - r < n])
        c.amo_pairwise([q[r][r - (s - n + 1)] for r in range(n) if 0 <= r - (s - n + 1) < n])
    return Formula(c.n, c.clauses, "sat" if n >= 4 or n == 1 else "unsat", "construction", [f"{n}-queens"])


# well-known published 9x9 puzzles (each has a solution)
SUDOKU9 = {
    "inkala2012": "800000000003600000070090200050007000000045700000100030001000068008500010090000400",
    "escargot": "100007090030020008009600500005300900010080002600004000300000010040000007007000300",
    "euler01": "003020600900305001001806400008102900700000008006708200002609500800203009005010300",
    "norvighard1": "400000805030000000000700000020000060000080400000010000000603070500200000104000000",
    "goldennugget": "000000039000001005003050800008090006070002000100400000009080050020000600400700000",
}


def sudoku_cnf(N: int, givens) -> Cnf:
    """N^2 x N^2 grid; givens: dict (r, c) -> value in 1..N^2."""
    S = N * N
    c = Cnf()
    x = [[[c.var() for _ in range(S)] for _ in range(S)] for _ in range(S)]
    for r in range(S):
        for col in range(S):
            c.add(*x[r][col])
            c.amo_pairwise(x[r][col])
    for v in range(S):
        for r in range(S):
            cells = [x[r][col][v] for col in range(S)]
            c.add(*cells)
            c.amo_pairwise(cells)
        for col in range(S):
            cells = [x[r][col][v] for r in range(S)]
            c.add(*cells)
            c.amo_pairwise(cells)
        for br in range(N):
            for bc in range(N):
                cells = [x[br * N + i][bc * N + j][v] for i in range(N) for j in range(N)]
                c.add(*cells)
                c.amo_pairwise(cells)
    for (r, col), v in sorted(givens.items()):
        c.add(x[r][col][v - 1])
    return c


def sudoku_fixed(rng: Rng, puzzle: str) -> Formula:
    s = SUDOKU9[puzzle]
    givens = {(i // 9, i % 9): int(ch) for i, ch in enumerate(s) if ch not in "0."}
    c = sudoku_cnf(3, givens)
    return Formula(c.n, c.clauses, "sat", "published puzzle",
                   [f"9x9 sudoku '{puzzle}': {s}"])


def sudoku_planted(rng: Rng, N: int, holes: float) -> Formula:
    S = N * N
    grid = [[(N * (r % N) + r // N + col) % S for col in range(S)] for r in range(S)]
    digits = rng.shuffle(list(range(S)))
    bands = rng.shuffle(list(range(N)))
    rows = [b * N + i for b in bands for i in rng.shuffle(list(range(N)))]
    stacks = rng.shuffle(list(range(N)))
    cols = [s * N + j for s in stacks for j in rng.shuffle(list(range(N)))]
    sol = [[digits[grid[rows[r]][cols[col]]] + 1 for col in range(S)] for r in range(S)]
    cells = [(r, col) for r in range(S) for col in range(S)]
    keep = rng.sample(len(cells), round(len(cells) * (1 - holes)))
    givens = {cells[i]: sol[cells[i][0]][cells[i][1]] for i in keep}
    c = sudoku_cnf(N, givens)
    return Formula(c.n, c.clauses, "sat", "construction",
                   [f"{S}x{S} sudoku with a planted solution, {len(givens)} givens ({holes:.0%} holes)"])


# ------------------------------------------------------------------ circuits / BMC

def _ripple_adder(c: Circuit, a, b, maj_style: bool):
    """n-bit adder, returns n+1 output bits (LSB first)."""
    carry = None
    out = []
    for i in range(len(a)):
        if carry is None:
            out.append(c.XOR(a[i], b[i]))
            carry = c.AND(a[i], b[i])
        elif maj_style:
            out.append(c.XOR(a[i], c.XOR(b[i], carry)))
            carry = c.MAJ(a[i], b[i], carry)
        else:
            t = c.XOR(a[i], b[i])
            out.append(c.XOR(t, carry))
            carry = c.OR(c.AND(a[i], b[i]), c.AND(t, carry))
    return out + [carry]


def addereq(rng: Rng, n: int, buggy: bool) -> Formula:
    c = Circuit()
    a, b = c.vars(n), c.vars(n)
    s1 = _ripple_adder(c, a, b, maj_style=False)
    if not buggy:
        s2 = _ripple_adder(c, b, a, maj_style=True)
    else:
        k = rng.below(n - 1) + 1  # carry out of bit k-1 computed as OR: differs for a=2^(k-1), b=0
        carry, s2 = None, []
        for i in range(n):
            if carry is None:
                s2.append(c.XOR(b[i], a[i]))
                carry = c.OR(b[i], a[i]) if k == 1 else c.AND(b[i], a[i])
            else:
                s2.append(c.XOR(b[i], c.XOR(a[i], carry)))
                carry = c.MAJ(b[i], a[i], carry) if i != k - 1 else c.OR(c.OR(b[i], a[i]), carry)
        s2.append(carry)
    c.miter(s1, s2)
    return Formula(c.n, c.clauses, "sat" if buggy else "unsat", "construction",
                   [f"miter of two {n}-bit ripple-carry adders (a+b vs b+a, different gates)"
                    + (", one carry gate replaced by OR" if buggy else "")])


def _array_multiplier(c: Circuit, a, b, bug_at=None):
    n = len(a)
    acc = None
    for j in range(n):
        row = []
        for i in range(n):
            g = c.OR if bug_at == (i, j) else c.AND
            row.append(g(a[i], b[j]))
        if acc is None:
            acc = row + [None] * n
            continue
        # add row << j into acc
        carry = None
        for i in range(n):
            pos = i + j
            x, y = acc[pos], row[i]
            if x is None:
                if carry is None:
                    acc[pos] = y
                else:
                    acc[pos] = c.XOR(y, carry)
                    carry = c.AND(y, carry)
            elif carry is None:
                acc[pos] = c.XOR(x, y)
                carry = c.AND(x, y)
            else:
                t = c.XOR(x, y)
                acc[pos] = c.XOR(t, carry)
                carry = c.OR(c.AND(x, y), c.AND(t, carry))
        pos = n + j
        if carry is not None:
            if acc[pos] is None:
                acc[pos] = carry
            else:
                s = c.XOR(acc[pos], carry)
                acc[pos] = s
    zero = None
    out = []
    for v in acc:
        if v is None:
            if zero is None:
                zero = c.const(False)
            v = zero
        out.append(v)
    return out


def multeq(rng: Rng, n: int, buggy: bool) -> Formula:
    c = Circuit()
    a, b = c.vars(n), c.vars(n)
    p1 = _array_multiplier(c, a, b)
    bug = (rng.below(n), rng.below(n)) if buggy else None
    p2 = _array_multiplier(c, b, a, bug_at=bug)
    c.miter(p1, p2)
    return Formula(c.n, c.clauses, "sat" if buggy else "unsat", "construction",
                   [f"miter of {n}x{n}-bit array multipliers a*b vs b*a"
                    + (f", partial product {bug} computed with OR" if buggy else "")])


def counter(rng: Rng, steps: int, target: int) -> Formula:
    """Counter with an enable input per step, starting at 0: can it equal `target` after
    `steps` steps?  SAT iff target <= steps (bits sized so that nothing overflows)."""
    width = max(steps, target).bit_length() + 1
    c = Circuit()
    s = c.vars(width)
    for x in s:
        c.add(-x)
    for _ in range(steps):
        en = c.var()
        carry = en
        nxt = []
        for i in range(width):
            nxt.append(c.XOR(s[i], carry))
            if i + 1 < width:
                carry = c.AND(s[i], carry)
        s = nxt
    for i in range(width):
        c.add(s[i] if (target >> i) & 1 else -s[i])
    return Formula(c.n, c.clauses, "sat" if target <= steps else "unsat", "construction",
                   [f"BMC: {width}-bit counter with enable, {steps} steps, reach {target}"])
