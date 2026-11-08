#!/usr/bin/env python3
"""PR (DPR) symmetry breaking for interchangeable rows of a matrix (sym0 feasibility study).

Research tool, not used by the solver. Question: which symmetry-breaking clauses can be justified
in the PR proof system, whose witnesses are partial assignments (so that dpr-trim, our registered
checker, accepts them), and which need substitution redundancy (SR: the witness is the symmetry
itself; dsr-trim or VeriPB)?

usage:
  symmetry_pr.py gen tph|php|sgp|col <params...> [--pigeon-amo] <out.cnf> <out.matrix>
  symmetry_pr.py break <in.cnf> <in.matrix> <out.cnf> <out.dpr>
  symmetry_pr.py sr2pr <in.cnf> <in.dsr> <out.dpr> [--all]

sr2pr reads an SR proof in the DSR text format (dsr-trim's, as satsuma writes it with --sr) and
rewrites every SR line whose substitution moves only variables that unit propagation of the
clause's negation fixes (with the formula's units) into a PR line: the witness is the
substitution applied to that assignment, restricted to the variables that change. RUP, RAT and
PR lines and deletions are copied. It reports the lines that do not convert (and stops at the
first unless --all); a fully converted proof is a DPR proof for dpr-trim.

`break` writes the formula with the symmetry-breaking clauses (to solve) and the PR lines (DPR
text: the clause, then the witness starting with the clause's first literal). The full proof of
the original formula is the PR lines followed by a solver's DRAT proof of the extended formula;
dpr-trim checks it against the original formula.

The matrix file: "mode rows K" or "mode fix1", then one row of literals per line ("r" and the
literals). Every transposition of two rows (applied to all their literals at once) must be a
symmetry of the formula; `break` checks the adjacent ones before anything else.
- mode rows K: the first K columns are a row's values. Rows i < r get the clauses
  (-x[i][v] v -x[r][u]) for u < v < K: row i takes the smallest value among rows i..n (the
  stabilizer chain: row 1 is the minimum of all rows, then row 2 of the rest, ...), added row by
  row and u ascending. Each is a PR clause with the 4-literal witness that swaps the two rows'
  values, {-x[i][v], x[i][u], -x[r][u], x[r][v]}. The negation of the clause sets x[i][v] and
  x[r][u]; where each row is an at-most-one group, propagation fixes both rows, so the witness is
  the transposition applied to that assignment (restricted to the literals that change), and the
  clauses added earlier stay implied under it. Pigeonhole and tph pass without the pigeons'
  at-most-one too: their other constraints are per hole (column-local), so moving two entries
  is enough.
- mode fix1: orbitopal fixing of the first column: units -x[c][0] for c >= 1 ("column 0 takes
  row 0"), witness {-x[c][0], x[0][0]}.
Where the rows are not fixed by the clause (a golfer's schedule over several weeks, colour classes
in graph colouring), the witness repairs the swapped entries only, and the PR check fails: such a
clause needs the substitution witness (SR: dsr-trim, or VeriPB), a case split over the unfixed
part of the moved rows, or extension variables. `gen sgp` and `gen col` produce such cases; `break`
writes them anyway, and dpr-trim rejects them.

Families (gen):
  tph N        2N+1 pigeons, N holes, each hole at most 2 pigeons (UNSAT); rows = pigeons
               (at-least-one over holes; --pigeon-amo adds at-most-one), values = holes.
  php N        N+1 pigeons, N holes (UNSAT); rows = pigeons.
  sgp G S W    social golfer: G groups of S golfers, W weeks, every pair meets at most once (no
               auxiliary variables); rows = golfers, all weeks' (week, group) literals; values =
               the week-1 groups (K = G). Sound by symmetry, not PR with this witness.
  col N K D    random graph, N vertices, average degree D, K colours; rows = colours over the
               vertices (a colour row is not an at-most-one group); mode fix1.
"""
import itertools
import random
import sys


def read_cnf(path):
    n, clauses = 0, []
    with open(path) as f:
        for line in f:
            if line.startswith("c") or not line.strip():
                continue
            if line.startswith("p"):
                n = int(line.split()[2])
                continue
            lits = [int(x) for x in line.split()]
            assert lits[-1] == 0
            clauses.append(lits[:-1])
    return n, clauses


def write_cnf(path, n, clauses, comment=""):
    with open(path, "w") as f:
        if comment:
            f.write(f"c {comment}\n")
        f.write(f"p cnf {n} {len(clauses)}\n")
        for c in clauses:
            f.write(" ".join(map(str, c)) + " 0\n")


def write_matrix(path, rows, mode):
    with open(path, "w") as f:
        f.write(f"mode {mode}\n")
        for r in rows:
            f.write("r " + " ".join(map(str, r)) + "\n")


def read_matrix(path):
    """rows, mode: 'rows K' (the first K columns are the row's values) or 'fix1'."""
    rows, mode = [], None
    with open(path) as f:
        for line in f:
            if line.startswith("r"):
                rows.append([int(x) for x in line.split()[1:]])
            elif line.startswith("mode"):
                mode = line.split()[1:]
    return rows, mode


# ------------------------------------------------------------------ generators

def gen_tph(n, pigeon_amo):
    p = [[i * n + j + 1 for j in range(n)] for i in range(2 * n + 1)]
    cls = [list(row) for row in p]
    if pigeon_amo:
        for row in p:
            cls += [[-a, -b] for a, b in itertools.combinations(row, 2)]
    for j in range(n):
        col = [p[i][j] for i in range(2 * n + 1)]
        cls += [[-a, -b, -c] for a, b, c in itertools.combinations(col, 3)]
    return (2 * n + 1) * n, cls, p, f"rows {n}"


def gen_php(n):
    p = [[i * n + j + 1 for j in range(n)] for i in range(n + 1)]
    cls = [list(row) for row in p]
    for j in range(n):
        col = [p[i][j] for i in range(n + 1)]
        cls += [[-a, -b] for a, b in itertools.combinations(col, 2)]
    return (n + 1) * n, cls, p, f"rows {n}"


def gen_sgp(g, s, w):
    golfers = g * s
    x = [[[golfer * w * g + week * g + grp + 1 for grp in range(g)] for week in range(w)]
         for golfer in range(golfers)]
    nv = golfers * w * g
    cls = []
    for golfer in range(golfers):
        for week in range(w):
            blk = x[golfer][week]
            cls.append(list(blk))
            cls += [[-a, -b] for a, b in itertools.combinations(blk, 2)]
    # group sizes: at most s golfers per group (sum over golfers is then exactly s), naive
    for week in range(w):
        for grp in range(g):
            col = [x[golfer][week][grp] for golfer in range(golfers)]
            cls += [[-v for v in sub] for sub in itertools.combinations(col, s + 1)]
    # every pair meets at most once (no auxiliary variables, so that a golfer transposition is a
    # pure row transposition)
    for a, b in itertools.combinations(range(golfers), 2):
        for w1, w2 in itertools.combinations(range(w), 2):
            for g1 in range(g):
                for g2 in range(g):
                    cls.append([-x[a][w1][g1], -x[b][w1][g1], -x[a][w2][g2], -x[b][w2][g2]])
    rows = [[lit for week in range(w) for lit in x[golfer][week]] for golfer in range(golfers)]
    return nv, cls, rows, f"rows {g}"


def gen_col(n, k, d, seed=1):
    rng = random.Random(seed)
    edges = set()
    while len(edges) < n * d // 2:
        u, v = rng.sample(range(n), 2)
        edges.add((min(u, v), max(u, v)))
    x = [[v * k + c + 1 for c in range(k)] for v in range(n)]
    cls = []
    for v in range(n):
        cls.append(list(x[v]))
        cls += [[-a, -b] for a, b in itertools.combinations(x[v], 2)]
    for u, v in sorted(edges):
        cls += [[-x[u][c], -x[v][c]] for c in range(k)]
    rows = [[x[v][c] for v in range(n)] for c in range(k)]
    return n * k, cls, rows, "fix1"


# ------------------------------------------------------------------ symmetry check

def is_row_symmetry(clauses, rows, i, r):
    """Is the transposition of rows i and r (all their literals at once) a symmetry?"""
    m = {}
    for a, b in zip(rows[i], rows[r]):
        m[a], m[b], m[-a], m[-b] = b, a, -b, -a
    s = {tuple(sorted(c)) for c in clauses}
    return all(tuple(sorted(m.get(l, l) for l in c)) in s for c in clauses)


def at_most_one_rows(clauses, rows):
    bins = {tuple(sorted(c)) for c in clauses if len(c) == 2}
    return all(tuple(sorted((-a, -b))) in bins for row in rows for a, b in itertools.combinations(row, 2))


# ------------------------------------------------------------------ breaking

def sb_clauses(rows, mode):
    """(clause, witness) pairs.
    rows K: row i takes the smallest value among rows i..n (values: the first K columns), u
            ascending, 4-literal witness swapping the two rows' values;
    fix1:   orbitopal fixing of the first column: units -x[c][0] for c >= 1 ("column 0 takes
            row 0"), 2-literal witness {-x[c][0], x[0][0]} (the transposition of rows 0 and c
            restricted to column 0)."""
    out = []
    if mode[0] == "fix1":
        for c in range(1, len(rows)):
            out.append(([-rows[c][0]], [-rows[c][0], rows[0][0]]))
        return out
    k = int(mode[1])
    for i in range(len(rows) - 1):
        for u in range(k):
            for r in range(i + 1, len(rows)):
                for v in range(u + 1, k):
                    xiv, xru = rows[i][v], rows[r][u]
                    clause = [-xiv, -xru]
                    witness = [-xiv, rows[i][u], -xru, rows[r][v]]
                    out.append((clause, witness))
    return out


def cmd_break(argv):
    cnf, mat, out_cnf, out_dpr = argv[:4]
    n, clauses = read_cnf(cnf)
    rows, mode = read_matrix(mat)
    sym = all(is_row_symmetry(clauses, rows, i, i + 1) for i in range(len(rows) - 1))
    amo = at_most_one_rows(clauses, rows)
    print(f"rows {len(rows)} x {len(rows[0])}; adjacent row transpositions are symmetries: {sym}; "
          f"rows at-most-one: {amo}", file=sys.stderr)
    if not sym:
        sys.exit("not a row symmetry")
    sb = sb_clauses(rows, mode)
    with open(out_dpr, "w") as f:
        for clause, witness in sb:
            f.write(" ".join(map(str, clause + witness)) + " 0\n")
    write_cnf(out_cnf, n, clauses + [c for c, _ in sb], f"{cnf} + {len(sb)} PR symmetry-breaking clauses")
    print(f"{len(sb)} PR clauses written", file=sys.stderr)


# ------------------------------------------------------------------ SR -> PR where the support is fixed

class Formula:
    """Clause database with deletions and a from-scratch unit propagation (two watches)."""

    def __init__(self, n, clauses):
        self.n = n
        self.cls = []
        self.alive = []
        self.index = {}
        self.watch = {}
        for c in clauses:
            self.add(c)

    def add(self, c):
        c = list(dict.fromkeys(c))
        cid = len(self.cls)
        self.cls.append(c)
        self.alive.append(True)
        self.index.setdefault(tuple(sorted(c)), []).append(cid)
        for lit in c[:2]:
            self.watch.setdefault(lit, []).append(cid)
        for lit in c:
            self.n = max(self.n, abs(lit))

    def delete(self, c):
        ids = self.index.get(tuple(sorted(dict.fromkeys(c))))
        while ids:
            cid = ids.pop()
            if self.alive[cid]:
                self.alive[cid] = False
                return True
        return False

    def propagate(self, assumptions):
        """Assignment {var: bool} from the formula's units and the assumptions, None on a conflict.
        Two watched literals (positions 0 and 1 of each clause, moved as usual); the watches stay
        valid between calls because every call starts from the empty assignment."""
        val = {}
        trail = []

        def value(lit):
            v = val.get(abs(lit))
            return None if v is None else v == (lit > 0)

        def assign(lit):
            x = value(lit)
            if x is not None:
                return x
            val[abs(lit)] = lit > 0
            trail.append(lit)
            return True

        for lit in assumptions:
            if not assign(lit):
                return None
        for cid, c in enumerate(self.cls):
            if self.alive[cid] and len(c) == 1 and not assign(c[0]):
                return None
        i = 0
        while i < len(trail):
            false_lit = -trail[i]
            i += 1
            ws = self.watch.get(false_lit)
            if not ws:
                continue
            keep = []
            conflict = False
            for k, cid in enumerate(ws):
                if conflict:
                    keep.append(cid)
                    continue
                if not self.alive[cid]:
                    continue
                c = self.cls[cid]
                if len(c) == 1:
                    keep.append(cid)
                    continue
                if c[0] == false_lit:
                    c[0], c[1] = c[1], c[0]
                if value(c[0]) is True:
                    keep.append(cid)
                    continue
                moved = False
                for j in range(2, len(c)):
                    if value(c[j]) is not False:
                        c[1], c[j] = c[j], c[1]
                        self.watch.setdefault(c[1], []).append(cid)
                        moved = True
                        break
                if moved:
                    continue
                keep.append(cid)
                if not assign(c[0]):
                    conflict = True
            self.watch[false_lit] = keep
            if conflict:
                return None
        return val


def parse_sr_line(tokens):
    """DSR addition line -> (clause, true literals, {var: literal}); the clause ends at the second
    occurrence of its first literal (the pivot), the true part at the third."""
    if not tokens:
        return [], [], {}
    p = tokens[0]
    occ = [i for i, t in enumerate(tokens) if t == p]
    if len(occ) < 2:
        return tokens, [], {}
    clause = tokens[:occ[1]]
    if len(occ) < 3:
        return clause, tokens[occ[1]:], {}
    trues = tokens[occ[1]:occ[2]]
    rest = tokens[occ[2] + 1:]
    sub = {}
    for k in range(0, len(rest) - 1, 2):
        sub[abs(rest[k])] = rest[k + 1] if rest[k] > 0 else -rest[k + 1]
    return clause, trues, sub


def cmd_sr2pr(argv):
    """sr2pr <in.cnf> <in.dsr> <out.dpr>: every SR line whose substitution moves only variables that
    unit propagation of the clause's negation (and the formula's units) fixes becomes a PR line
    with the witness "substitution applied to that assignment"; RAT / PR / RUP lines and deletions
    are copied. Reports how many SR lines convert; stops at the first that does not."""
    cnf, dsr, out = argv[:3]
    keep_going = "--all" in argv
    n, clauses = read_cnf(cnf)
    F = Formula(n, clauses)
    stats = {"sr": 0, "pinned": 0, "unpinned": 0, "plain": 0, "deletions": 0, "support": 0}
    with open(dsr) as fin, open(out, "w") as fout:
        for line in fin:
            t = line.split()
            if not t:
                continue
            if t[0] == "d":
                lits = [int(x) for x in t[1:-1]]
                F.delete(lits)
                stats["deletions"] += 1
                fout.write(line)
                continue
            tokens = [int(x) for x in t[:-1]]
            clause, trues, sub = parse_sr_line(tokens)
            sub = {v: l for v, l in sub.items() if l != v and v not in {abs(x) for x in trues}}
            if not sub:
                stats["plain"] += 1
                fout.write(line)
                F.add(clause)
                continue
            stats["sr"] += 1
            val = F.propagate([-x for x in clause])
            if val is None:  # the clause is RUP: no witness needed
                stats["pinned"] += 1
                fout.write(" ".join(map(str, clause)) + " 0\n")
                F.add(clause)
                continue
            support = set(sub) | {abs(l) for l in sub.values()}
            stats["support"] += len(support)
            if all(v in val for v in support):
                omega = list(trues)
                seen = {abs(x) for x in omega}
                for v, l in sub.items():
                    b = val[abs(l)] == (l > 0)
                    if v not in seen and val.get(v) != b:  # only the variables that change
                        omega.append(v if b else -v)
                fout.write(" ".join(map(str, clause + omega)) + " 0\n")
                stats["pinned"] += 1
            else:
                stats["unpinned"] += 1
                free = sum(1 for v in support if v not in val)
                print(f"SR line {stats['sr']}: clause {clause}, support {len(support)}, "
                      f"{free} not fixed by propagation", file=sys.stderr)
                if not keep_going:
                    break
                fout.write(line)
            F.add(clause)
    print(stats, file=sys.stderr)


def main():
    if len(sys.argv) < 2:
        sys.exit(__doc__)
    cmd = sys.argv[1]
    if cmd == "sr2pr":
        cmd_sr2pr(sys.argv[2:])
        return
    if cmd == "gen":
        fam, args = sys.argv[2], sys.argv[3:]
        flags = [a for a in args if a.startswith("--")]
        args = [a for a in args if not a.startswith("--")]
        out_cnf, out_mat = args[-2:]
        p = [int(a) for a in args[:-2]]
        if fam == "tph":
            nv, cls, rows, mode = gen_tph(p[0], "--pigeon-amo" in flags)
        elif fam == "php":
            nv, cls, rows, mode = gen_php(p[0])
        elif fam == "sgp":
            nv, cls, rows, mode = gen_sgp(*p)
        elif fam == "col":
            nv, cls, rows, mode = gen_col(*p)
        else:
            sys.exit(f"unknown family {fam}")
        write_cnf(out_cnf, nv, cls, f"{fam} {' '.join(map(str, p))} {' '.join(flags)}")
        write_matrix(out_mat, rows, mode)
    elif cmd == "break":
        cmd_break(sys.argv[2:])
    else:
        sys.exit(__doc__)


if __name__ == "__main__":
    main()
