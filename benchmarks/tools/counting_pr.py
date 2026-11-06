#!/usr/bin/env python3
"""PR (DPR) refutations of counting formulas from their exactly-one structure (cardinality study).

Research tool for the v0.5 go/no-go: shows that refutations built from the detected structure
check with dpr-trim (the competition's DPR checker chain dpr-trim + cake_lpr), without new
variables. Not used by the solver.

usage: counting_pr.py php|parity|count3 <input.cnf> <proof.dpr>

Structure (as --cardinality detects it): the long clauses are the at-least-one halves of
exactly-one constraints with positive literals; the binary clauses are pairwise at-most-one.
- php:    pigeons = the long clauses, holes = classes of variables joined by binary clauses
          across pigeons; each (pigeon, hole) pair owns k interchangeable variables (k = 1 for
          functional pigeonhole such as php_sudoku, k = part size for clique formulas on a
          complete multipartite graph). More pigeons than holes.
- parity: vertices = the long clauses, every variable in exactly two = an edge of K_n, n odd
          (perfect matching, count_p2).
- count3: every variable in exactly three = a triple, n = 1 mod 3 (Count^3, count_p3).

All three proofs are symmetry arguments: a PR clause (-x v -y) with a witness that swaps two
pigeons / vertices, then RUP units fix one more pigeon / pair / triple. DPR text format: the
clause, then the witness starting with the clause's first literal.
"""
import itertools
import sys
from collections import defaultdict


def read_cnf(path):
    clauses = []
    with open(path) as f:
        for line in f:
            if line.startswith(("c", "p")) or not line.strip():
                continue
            clauses.append([int(x) for x in line.split()][:-1])
    return clauses


def owners(longs, arity):
    """variable -> the long clauses containing it (asserting positive literals and the arity)."""
    ends = defaultdict(list)
    for i, c in enumerate(longs):
        for lit in c:
            assert lit > 0, "positive at-least-one clauses expected"
            ends[lit].append(i)
    assert all(len(v) == arity for v in ends.values()), f"every variable in exactly {arity} constraint(s)"
    return ends


def php(clauses, out):
    longs = [c for c in clauses if len(c) > 2]
    pigeon_of = {v: i[0] for v, i in owners(longs, 1).items()}
    parent = {v: v for v in pigeon_of}

    def find(v):
        while parent[v] != v:
            parent[v] = parent[parent[v]]
            v = parent[v]
        return v

    for c in clauses:
        if len(c) == 2 and c[0] < 0 and c[1] < 0 and pigeon_of[-c[0]] != pigeon_of[-c[1]]:
            parent[find(-c[0])] = find(-c[1])
    roots = sorted({find(v) for v in pigeon_of})
    hole_of = {r: h for h, r in enumerate(roots)}
    npig, nhole = len(longs), len(roots)
    p = [[[] for _ in range(nhole)] for _ in range(npig)]
    for v, i in sorted(pigeon_of.items()):
        p[i][hole_of[find(v)]].append(v)
    k = len(p[0][0])
    assert all(len(p[i][h]) == k for i in range(npig) for h in range(nhole)) and npig > nhole
    for m in range(nhole, 0, -1):  # hole m-1 is reserved for pigeon m
        hole, s = m - 1, m
        for i in range(m):
            for x in range(hole):
                for ia, va in enumerate(p[i][hole]):
                    for ib, vb in enumerate(p[s][x]):
                        out.write(f"{-va} {-vb} {-va} {p[i][x][ib]} {p[s][hole][ia]} {-vb} 0\n")
        for i in range(m):
            for va in p[i][hole]:
                out.write(f"{-va} 0\n")
    return f"pigeons {npig} holes {nhole} variables per pair {k}"


def parity(clauses, out):
    longs = [c for c in clauses if len(c) > 2]
    n = len(longs)
    e = [[None] * n for _ in range(n)]
    for var, (a, b) in owners(longs, 2).items():
        e[a][b] = e[b][a] = var
    assert n % 2 == 1 and all(e[a][b] for a in range(n) for b in range(n) if a != b)
    verts = list(range(n))
    while len(verts) >= 3:  # WLOG the last vertex m is matched to q
        m, q = verts[-1], verts[-2]
        rest = verts[:-2]
        for u in rest:
            for w in rest:
                if u != w:
                    out.write(f"{-e[m][u]} {-e[q][w]} {-e[m][u]} {e[m][q]} {e[u][w]} {-e[q][w]} 0\n")
        for u in rest:
            out.write(f"{-e[m][u]} 0\n")
        out.write(f"{e[m][q]} 0\n")
        verts = rest
    return f"vertices {n}"


def count3(clauses, out):
    longs = [c for c in clauses if len(c) > 2]
    n = len(longs)
    t = {frozenset(v): var for var, v in owners(longs, 3).items()}
    assert n % 3 == 1

    def tr(*xs):
        return t[frozenset(xs)]

    verts = list(range(n))
    while len(verts) >= 4:  # WLOG {m, q, r} is a triple: first q joins m, then r
        m, q, r = verts[-1], verts[-2], verts[-3]
        no_q = [v for v in verts if v not in (m, q)]
        for a, b in itertools.combinations(no_q, 2):
            for c, d in itertools.combinations([v for v in verts if v not in (m, a, b, q)], 2):
                out.write(f"{-tr(m, a, b)} {-tr(q, c, d)} {-tr(m, a, b)} {tr(m, q, b)} {tr(a, c, d)} {-tr(q, c, d)} 0\n")
        for a, b in itertools.combinations(no_q, 2):
            out.write(f"{-tr(m, a, b)} 0\n")
        others = [v for v in verts if v not in (m, q, r)]
        for b in others:
            for c, d in itertools.combinations([v for v in verts if v not in (m, q, b, r)], 2):
                out.write(f"{-tr(m, q, b)} {-tr(r, c, d)} {-tr(m, q, b)} {tr(m, q, r)} {tr(b, c, d)} {-tr(r, c, d)} 0\n")
        for b in others:
            out.write(f"{-tr(m, q, b)} 0\n")
        out.write(f"{tr(m, q, r)} 0\n")
        verts = others
    return f"points {n}"


def main():
    kind, cnf, proof = sys.argv[1:4]
    clauses = read_cnf(cnf)
    with open(proof, "w") as out:
        info = {"php": php, "parity": parity, "count3": count3}[kind](clauses, out)
        out.write("0\n")
    print(info, file=sys.stderr)


if __name__ == "__main__":
    main()
