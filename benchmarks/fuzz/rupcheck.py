#!/usr/bin/env python3
"""Minimal forward RUP checker for DRAT/DRUP proofs (text or binary), a
fallback for when drat-trim is not built. Test tooling only.

  rupcheck.py <formula.cnf> <proof>     prints 's VERIFIED' (exit 0) or 's NOT VERIFIED' (exit 1)

Every added lemma must be RUP (reverse unit propagation) with respect to the
formula plus all earlier lemmas; unit propagation runs inside a PySAT solver
(minisat22 `propagate`). Deletions are ignored, which is sound for RUP: every
lemma is implied by the formula, so checking against a superset of the live
clauses never accepts a wrong proof. RAT lemmas (needed only for
extension/elimination steps such as BCE) are NOT supported and are reported as
not verified; use drat-trim for those.
"""

from __future__ import annotations

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from fuzzlib import parse_dimacs  # noqa: E402


def read_proof(data: bytes):
    """Yields (is_delete, literals) for text or binary DRAT."""
    printable = set(b"0123456789-cd \t\r\n")
    if data and any(b not in printable for b in data[:256]):
        i, n = 0, len(data)
        while i < n:
            tag = data[i]
            i += 1
            if tag not in (0x61, 0x64):  # 'a' / 'd'
                raise ValueError(f"bad binary proof tag {tag:#x} at byte {i - 1}")
            lits = []
            while True:
                u, shift = 0, 0
                while True:
                    if i >= n:
                        raise ValueError("truncated binary proof")
                    b = data[i]
                    i += 1
                    u |= (b & 127) << shift
                    shift += 7
                    if not b & 128:
                        break
                if u == 0:
                    break
                lits.append((u >> 1) * (-1 if u & 1 else 1))
            yield tag == 0x64, lits
        return
    cur: list[int] = []
    delete = False
    for line in data.decode().splitlines():
        s = line.strip()
        if not s or s[0] == "c":
            continue
        toks = s.split()
        for t in toks:
            if t == "d":
                delete = True
                continue
            v = int(t)
            if v == 0:
                yield delete, cur
                cur, delete = [], False
            else:
                cur.append(v)
    if cur:
        raise ValueError("last proof line not terminated by 0")


def main(argv: list[str]) -> int:
    if len(argv) != 2:
        print("usage: rupcheck.py <formula.cnf> <proof>", file=sys.stderr)
        return 2
    from pysat.solvers import Solver

    _, clauses, _ = parse_dimacs(Path(argv[0]).read_text())
    data = Path(argv[1]).read_bytes()
    with Solver(name="minisat22", bootstrap_with=clauses) as s:
        if any(len(c) == 0 for c in clauses) or not s.propagate(assumptions=[])[0]:
            print("c formula is refuted by unit propagation")
            print("s VERIFIED")
            return 0
        n = 0
        try:
            for delete, lits in read_proof(data):
                if delete:
                    continue
                n += 1
                if s.propagate(assumptions=[-l for l in lits])[0]:
                    print(f"c lemma {n} ({' '.join(map(str, lits))} 0) is not RUP")
                    print("s NOT VERIFIED")
                    return 1
                if not lits:
                    print(f"c empty clause derived after {n} lemmas")
                    print("s VERIFIED")
                    return 0
                s.add_clause(lits)
        except ValueError as e:
            print(f"c malformed proof: {e}")
            print("s NOT VERIFIED")
            return 1
        if not s.propagate(assumptions=[])[0]:
            print(f"c {n} lemmas, conflict by unit propagation at the end")
            print("s VERIFIED")
            return 0
        print(f"c {n} lemmas, no empty clause derived")
        print("s NOT VERIFIED")
        return 1


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
