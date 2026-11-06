#!/usr/bin/env python3
"""End-to-end check of --counting: generated counting formulas, solver proofs, dpr-trim.

For each family and size (plain and scrambled: renamed variables, flipped polarities, shuffled
clauses and literals), the solver runs with --counting=1 and a proof (binary; text with
--text); every UNSAT proof is checked with dpr-trim (and dpr-trim's LPR output with lpr-check,
dpr-trim's C LPR checker, when it is built in benchmarks/tools/build/bin or next to the dpr-trim
sources in benchmarks/tools/build/src/dpr-trim; not for LPR files with a line longer than its
buffer of 10 ints per variable). Satisfiable variants must give SAT
(the solver checks its model against the formula) without a structure found.

    .venv/bin/python benchmarks/tools/counting_check.py            # all families, -j 2
    .venv/bin/python benchmarks/tools/counting_check.py --text --quick

Families (as in tests/test_solver.cpp and benchmarks/fuzz/gen.py --family counting):
  php     PHP: pigeons at least one hole, holes at most one pigeon
  fphp    functional PHP (pigeons exactly one hole), php_sudoku
  clique  a clique of k+1 vertices in the complete k-partite graph (clique_n<size>_k<k+1>)
  match   perfect matching of K_n (parity; count_p2_M<n>)
  triples partition of n points into triples (Count^3; count_p3_M<n>)
  clqcl   clique-colouring: a graph with a k-clique that is m-colourable (clqcl_<n>_<k>_<m>)
  gcol    m-colouring of a random graph with an (m+1)-clique (a pigeonhole inside the formula)
  rphp    relativized pigeonhole: n pigeons, r places, n-1 holes (rphp_p<n>_r<r>)
Exit code 1 if any run fails.
"""

from __future__ import annotations

import argparse
import itertools
import random
import re
import subprocess
import sys
import tempfile
import time
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

BENCH = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(BENCH))
from lib import paths  # noqa: E402


def exactly_one(lits, clauses, pairwise=True):
    clauses.append(list(lits))
    if pairwise:
        clauses.extend([-a, -b] for a, b in itertools.combinations(lits, 2))


def php(pigeons, holes, functional):
    x = lambda p, h: p * holes + h + 1  # noqa: E731
    cl = []
    for p in range(pigeons):
        exactly_one([x(p, h) for h in range(holes)], cl, functional)
    for h in range(holes):
        cl.extend([-x(p, h), -x(q, h)] for p, q in itertools.combinations(range(pigeons), 2))
    return pigeons * holes, cl


def clique(slots, parts, size):
    verts = parts * size
    x = lambda s, v: s * verts + v + 1  # noqa: E731
    cl = []
    for s in range(slots):
        exactly_one([x(s, v) for v in range(verts)], cl)
    for s, t in itertools.combinations(range(slots), 2):
        cl.extend([-x(s, v), -x(t, w)] for v in range(verts) for w in range(verts) if v // size == w // size)
    return slots * verts, cl


def matching(n):
    e = {}
    for a, b in itertools.combinations(range(n), 2):
        e[a, b] = e[b, a] = len(e) // 2 + 1
    cl = []
    for a in range(n):
        exactly_one([e[a, b] for b in range(n) if b != a], cl)
    return n * (n - 1) // 2, cl


def triples(n):
    through = [[] for _ in range(n)]
    for i, t in enumerate(itertools.combinations(range(n), 3)):
        for p in t:
            through[p].append(i + 1)
    cl = []
    for row in through:
        exactly_one(row, cl)
    return len(list(itertools.combinations(range(n), 3))), cl


def clique_colouring(n, k, m):
    e = {}
    for u, v in itertools.combinations(range(n), 2):
        e[u, v] = e[v, u] = len(e) // 2 + 1
    base = n * (n - 1) // 2
    q = [[base + i * n + u + 1 for u in range(n)] for i in range(k)]
    r = [[base + k * n + u * m + c + 1 for c in range(m)] for u in range(n)]
    cl = []
    for row in q:
        exactly_one(row, cl)
    for u in range(n):
        cl.extend([-q[i][u], -q[j][u]] for i, j in itertools.combinations(range(k), 2))
    for i, j in itertools.combinations(range(k), 2):
        cl.extend([-q[i][u], -q[j][v], e[u, v]] for u in range(n) for v in range(n) if u != v)
    for row in r:
        exactly_one(row, cl)
    for u, v in itertools.combinations(range(n), 2):
        cl.extend([-e[u, v], -r[u][c], -r[v][c]] for c in range(m))
    return base + k * n + n * m, cl


def relativized(n, r, h):
    """n pigeons rest at r places, the places in use map injectively into h holes."""
    pv = lambda i, u: i * r + u + 1  # noqa: E731
    used = lambda u: n * r + u + 1  # noqa: E731
    qv = lambda u, k: n * r + r + u * h + k + 1  # noqa: E731
    cl = [[pv(i, u) for u in range(r)] for i in range(n)]
    for u in range(r):
        cl.extend([-pv(i, u), -pv(j, u)] for i, j in itertools.combinations(range(n), 2))
        cl.extend([-pv(i, u), used(u)] for i in range(n))
        cl.append([-used(u)] + [qv(u, k) for k in range(h)])
    for u, v in itertools.combinations(range(r), 2):
        cl.extend([-used(u), -used(v), -qv(u, k), -qv(v, k)] for k in range(h))
    return n * r + r + r * h, cl


def colouring(n, m, clique, p, amo, rng):
    """m colours for a random graph (edge probability p) with a clique on the first vertices."""
    x = lambda u, c: u * m + c + 1  # noqa: E731
    cl = []
    for u in range(n):
        exactly_one([x(u, c) for c in range(m)], cl, amo)
    for u, v in itertools.combinations(range(n), 2):
        if (u < clique and v < clique) or rng.random() < p:
            cl.extend([-x(u, c), -x(v, c)] for c in range(m))
    return n * m, cl


def scramble(nvars, cl, rng):
    perm = list(range(1, nvars + 1))
    rng.shuffle(perm)
    flip = [rng.choice([1, -1]) for _ in range(nvars)]
    out = [[perm[abs(l) - 1] * flip[abs(l) - 1] * (1 if l > 0 else -1) for l in c] for c in cl]
    for c in out:
        rng.shuffle(c)
    rng.shuffle(out)
    return out


def cases(quick):
    """(name, nvars, clauses, unsat)"""
    holes = range(3, 7) if quick else range(3, 11)
    for h in holes:
        yield f"php{h + 1}_{h}", *php(h + 1, h, False), True
        yield f"fphp{h + 1}_{h}", *php(h + 1, h, True), True
        yield f"fphp{h + 2}_{h}", *php(h + 2, h, True), True
        yield f"fphp{h}_{h}", *php(h, h, True), False
    for parts, size in [(3, 2), (4, 2), (3, 3)] + ([] if quick else [(5, 3), (6, 4), (9, 2)]):
        yield f"clique{parts + 1}_{parts}x{size}", *clique(parts + 1, parts, size), True
        yield f"clique{parts}_{parts}x{size}", *clique(parts, parts, size), False
    for n in range(4, 12 if quick else 22):
        yield f"match{n}", *matching(n), n % 2 == 1
    for n in range(4, 9 if quick else 12):
        yield f"triples{n}", *triples(n), n % 3 != 0
    for n, k, m in [(5, 4, 3), (6, 4, 3), (6, 5, 3)] + ([] if quick else [(7, 5, 4), (8, 6, 5), (10, 7, 6)]):
        yield f"clqcl{n}_{k}_{m}", *clique_colouring(n, k, m), True
    yield "clqcl5_3_3", *clique_colouring(5, 3, 3), False
    for n, r in [(5, 5), (8, 8), (4, 6)] + ([] if quick else [(15, 15), (25, 25), (5, 12)]):
        yield f"rphp{n}_{r}", *relativized(n, r, n - 1), True
    yield "rphp4_5_sat", *relativized(4, 5, 4), False
    rng = random.Random(7)
    for n, m in [(12, 4), (20, 5)] + ([] if quick else [(40, 8), (60, 12)]):
        for amo in (False, True):
            yield f"gcol{n}_{m}{'_amo' if amo else ''}", *colouring(n, m, m + 1, 0.3, amo, rng), True


def write_cnf(path, nvars, cl):
    with open(path, "w") as f:
        f.write(f"p cnf {nvars} {len(cl)}\n")
        for c in cl:
            f.write(" ".join(map(str, c)) + " 0\n")


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--solver", default=str(paths.default_solver()))
    ap.add_argument("--extra", default="", help="more solver options")
    ap.add_argument("--text", action="store_true", help="text proofs (--proof-text)")
    ap.add_argument("--quick", action="store_true", help="small sizes only")
    ap.add_argument("--seed", type=int, default=1)
    ap.add_argument("-j", "--jobs", type=int, default=2)
    args = ap.parse_args()
    dpr = paths.tools_bin() / "dpr-trim"
    lpr_check = paths.tools_bin() / "lpr-check"
    if not lpr_check.exists():  # (built next to dpr-trim's sources, not installed)
        lpr_check = paths.tools_bin().parent / "src" / "dpr-trim" / "lpr-check"
    if not dpr.exists():
        raise SystemExit(f"dpr-trim not found in {paths.strip_local(str(paths.tools_bin()))}/")
    rng = random.Random(args.seed)
    jobs = []
    for name, nvars, cl, unsat in cases(args.quick):
        jobs.append((name, nvars, cl, unsat))
        jobs.append((name + "-scrambled", nvars, scramble(nvars, cl, rng), unsat))
    tmp = Path(tempfile.mkdtemp(prefix="counting-check-"))

    def run(job):
        name, nvars, cl, unsat = job
        cnf, proof, lpr = tmp / f"{name}.cnf", tmp / f"{name}.proof", tmp / f"{name}.lpr"
        write_cnf(cnf, nvars, cl)
        cmd = [args.solver, "-v", "-n", "--counting=1"] + args.extra.split() + (["--proof-text"] if args.text else [])
        t0 = time.time()
        out = subprocess.run(cmd + [str(cnf), str(proof)], capture_output=True, text=True).stdout
        secs = time.time() - t0
        status = (re.findall(r"^s (\S+)", out, re.M) or ["?"])[-1]
        m = re.search(r"^c counting +(\d+) +structures .*PR clauses (\d+) +units (\d+) .*abandoned (\d+)", out, re.M)
        found, pr, units, abandoned = (int(g) for g in m.groups()) if m else (-1, -1, -1, -1)
        verdict, ok = "-", True
        if unsat:
            ok = status == "UNSATISFIABLE" and found == 1 and pr >= 0 and abandoned == 0
            d = subprocess.run([str(dpr), str(cnf), str(proof), "-L", str(lpr)], capture_output=True, text=True).stdout
            verdict = (re.findall(r"^s (.*)$", d, re.M) or ["?"])[-1]
            ok = ok and verdict == "VERIFIED"
            # (lpr-check reads a line into a buffer of 10 ints per variable: dpr-trim's first
            # deletion line can be longer, which overflows it; such proofs are not given to it.)
            longest = max((len(line.split()) for line in open(lpr)), default=0) if lpr.exists() else 0
            if ok and lpr_check.exists() and longest < 10 * nvars:
                c = subprocess.run([str(lpr_check), str(cnf), str(lpr)], capture_output=True, text=True).stdout
                lv = (re.findall(r"^s (.*)$", c, re.M) or ["?"])[-1]
                verdict += f", lpr-check {lv}"
                ok = lv == "VERIFIED"
        else:
            ok = status == "SATISFIABLE" and found == 0
        for f in (cnf, proof, lpr):
            f.unlink(missing_ok=True)
        line = (f"{'ok  ' if ok else 'FAIL'} {name:28s} {status:14s} {secs:6.2f} s  found {found}  PR {pr:6d}  "
                f"units {units:4d}  dpr-trim {verdict}")
        print(line, flush=True)
        return ok

    with ThreadPoolExecutor(max(1, min(args.jobs, 2))) as ex:
        results = list(ex.map(run, jobs))
    tmp.rmdir()
    failed = results.count(False)
    print(f"{len(results)} runs, {failed} failed")
    sys.exit(1 if failed else 0)


if __name__ == "__main__":
    main()
