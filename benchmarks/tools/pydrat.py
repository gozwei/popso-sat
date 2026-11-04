#!/usr/bin/env python3
"""pydrat: a small forward DRAT proof checker in pure Python (fallback for drat-trim).

    pydrat.py <formula.cnf[.gz|.xz]> <proof> [-t <seconds>] [-q]

Prints 's VERIFIED' if the proof refutes the formula, otherwise 's NOT VERIFIED' (exit 1), like
drat-trim; 'c TIMEOUT' + exit 2 when the time limit is hit.  Text and binary DRAT are detected
automatically (drat-trim's convention).  Checking is forward: every added lemma must be RUP
(reverse unit propagation) or RAT on its first literal w.r.t. the current clause set; deletions
of clauses that are unit/reason under the top-level assignment are ignored (as drat-trim does),
deletions of unknown clauses are ignored with a warning.  Verified as soon as the clause set
becomes inconsistent under unit propagation (empty clause, or a conflict at the top level).

Stricter than drat-trim in one way: drat-trim checks backwards and only verifies lemmas used in
the refutation; pydrat rejects any invalid lemma.  It is far slower, so run.py uses it only for
proofs up to --pydrat-max-mb when no drat-trim binary is available.
"""

from __future__ import annotations

import sys
import time
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from lib.dimacs import CnfStream, DimacsError  # noqa: E402

TEXT_BYTES = set(b"0123456789-d \n\r\tc")


class Timeout(Exception):
    pass


def _enc(lit: int) -> int:
    return 2 * lit if lit > 0 else -2 * lit + 1


def proof_steps(path):
    """Yield (is_deletion, [literal codes]) from a text or binary DRAT file."""
    with open(path, "rb") as fh:
        data = fh.read()
    head = data[:512]
    binary = any(b not in TEXT_BYTES for b in head)
    if binary:
        i, n = 0, len(data)
        while i < n:
            tag = data[i]
            i += 1
            if tag not in (0x61, 0x64):
                raise ValueError(f"binary proof: bad tag byte {tag:#x} at offset {i - 1}")
            lits = []
            while True:
                x, shift = 0, 0
                while True:
                    if i >= n:
                        raise ValueError("binary proof: truncated literal")
                    b = data[i]
                    i += 1
                    x |= (b & 0x7F) << shift
                    shift += 7
                    if not b & 0x80:
                        break
                if x == 0:
                    break
                lits.append(x)  # already 2v + sign, the internal code
            yield tag == 0x64, lits
        return
    dele, cur = False, []
    for line in data.splitlines():
        s = line.strip()
        if not s or s[:1] == b"c":
            continue
        for tok in s.split():
            if tok == b"d":
                dele = True
                continue
            v = int(tok)
            if v == 0:
                yield dele, cur
                dele, cur = False, []
            else:
                cur.append(_enc(v))
    if cur:
        yield dele, cur


class Checker:
    def __init__(self, nvars: int):
        self.n = nvars
        size = 2 * (nvars + 2)
        self.asg = bytearray(size)       # asg[x] = 1 <=> literal code x is true
        self.watches = [[] for _ in range(size)]
        self.clauses: list = []
        self.index: dict = {}
        self.trail: list = []
        self.qhead = 0
        self.inconsistent = False
        self.warnings = 0

    def _grow(self, code):
        if code + 2 > len(self.asg):
            need = max(code + 2, 2 * len(self.asg))
            self.asg.extend(bytes(need - len(self.asg)))
            self.watches.extend([] for _ in range(need - len(self.watches)))

    def _propagate(self) -> bool:
        """Returns True on conflict."""
        asg, watches, clauses, trail = self.asg, self.watches, self.clauses, self.trail
        qhead = self.qhead
        while qhead < len(trail):
            f = trail[qhead] ^ 1  # this literal became false
            qhead += 1
            self.qhead = qhead
            ws = watches[f]
            i = j = 0
            nws = len(ws)
            while i < nws:
                cid = ws[i]
                i += 1
                c = clauses[cid]
                if c is None:
                    continue
                if c[0] == f:
                    c[0], c[1] = c[1], f
                first = c[0]
                if asg[first]:
                    ws[j] = cid
                    j += 1
                    continue
                for k in range(2, len(c)):
                    lk = c[k]
                    if not asg[lk ^ 1]:
                        c[1], c[k] = lk, f
                        watches[lk].append(cid)
                        break
                else:
                    ws[j] = cid
                    j += 1
                    if asg[first ^ 1]:
                        while i < nws:
                            ws[j] = ws[i]
                            j += 1
                            i += 1
                        del ws[j:]
                        return True
                    asg[first] = 1
                    trail.append(first)
            del ws[j:]
        return False

    def _assign(self, x):
        self.asg[x] = 1
        self.trail.append(x)

    def _undo(self, mark):
        asg = self.asg
        for x in self.trail[mark:]:
            asg[x] = 0
        del self.trail[mark:]
        self.qhead = mark

    def rup(self, lits) -> bool:
        asg = self.asg
        mark = len(self.trail)
        conflict = False
        for x in lits:
            if asg[x]:
                conflict = True
                break
            if not asg[x ^ 1]:
                self._assign(x ^ 1)
        if not conflict:
            conflict = self._propagate()
        self._undo(mark)
        return conflict

    def rat(self, lits) -> bool:
        if not lits:
            return False
        pivot = lits[0]
        neg = pivot ^ 1
        base = set(lits)
        for c in self.clauses:
            if c is None or neg not in c:
                continue
            res = base | {y for y in c if y != neg}
            if any((y ^ 1) in res for y in res):
                continue  # tautological resolvent
            if not self.rup(list(res)):
                return False
        return True

    def add(self, lits):
        """Add a clause (no check).  Updates the top-level assignment."""
        lits = list(dict.fromkeys(lits))
        for x in lits:
            self._grow(x)
        key = tuple(sorted(lits))
        asg = self.asg
        # non-false literals first (true before unassigned)
        lits.sort(key=lambda x: 0 if asg[x] else (2 if asg[x ^ 1] else 1))
        cid = len(self.clauses)
        self.clauses.append(lits)
        self.index.setdefault(key, []).append(cid)
        if not lits:
            self.inconsistent = True
            return
        if len(lits) == 1:
            x = lits[0]
            if asg[x ^ 1]:
                self.inconsistent = True
            elif not asg[x]:
                self._assign(x)
                if self._propagate():
                    self.inconsistent = True
            return
        self.watches[lits[0]].append(cid)
        self.watches[lits[1]].append(cid)
        if asg[lits[0] ^ 1]:
            self.inconsistent = True  # all literals false
        elif asg[lits[1] ^ 1] and not asg[lits[0]]:
            self._assign(lits[0])  # unit under the top-level assignment
            if self._propagate():
                self.inconsistent = True

    def delete(self, lits):
        key = tuple(sorted(set(lits)))
        ids = self.index.get(key)
        if not ids:
            self.warnings += 1
            return
        cid = ids[-1]
        c = self.clauses[cid]
        asg = self.asg
        true = [x for x in c if asg[x]]
        if len(true) == 1 and all(asg[x ^ 1] for x in c if x != true[0]):
            return  # possibly the reason of a top-level assignment: ignore (drat-trim does too)
        ids.pop()
        self.clauses[cid] = None


def check(cnf, proof, time_limit=None, quiet=False):
    t0 = time.perf_counter()
    stream = CnfStream(cnf)
    clauses = list(stream)
    nv = max(stream.nvars or 0, stream.max_var)
    ck = Checker(nv)
    for cl in clauses:
        ck.add([_enc(x) for x in cl])
        if ck.inconsistent:
            break
    del clauses
    if ck.inconsistent:
        return True, "formula refuted by unit propagation", 0
    nadd = ndel = 0
    for dele, lits in proof_steps(proof):
        if dele:
            ndel += 1
            ck.delete(lits)
            continue
        nadd += 1
        if time_limit and nadd % 256 == 0 and time.perf_counter() - t0 > time_limit:
            raise Timeout()
        lits = list(dict.fromkeys(lits))
        for x in lits:
            ck._grow(x)
        if not ck.rup(lits) and not ck.rat(lits):
            shown = [(x >> 1) * (-1 if x & 1 else 1) for x in lits[:12]]
            return False, f"lemma #{nadd} {shown}{'...' if len(lits) > 12 else ''} is neither RUP nor RAT", nadd
        ck.add(lits)
        if ck.inconsistent:
            return True, f"{nadd} lemmas, {ndel} deletions checked", nadd
    return False, f"no refutation: {nadd} lemmas, {ndel} deletions, clause set still consistent", nadd


def main(argv=None):
    argv = sys.argv[1:] if argv is None else argv
    pos, tl, quiet = [], None, False
    i = 0
    while i < len(argv):
        a = argv[i]
        if a == "-t":
            tl = float(argv[i + 1])
            i += 2
            continue
        if a == "-q":
            quiet = True
        elif a.startswith("-"):
            pass  # drat-trim options are accepted and ignored
        else:
            pos.append(a)
        i += 1
    if len(pos) != 2:
        print(__doc__)
        return 2
    t0 = time.perf_counter()
    try:
        ok, msg, _ = check(pos[0], pos[1], tl, quiet)
    except Timeout:
        print(f"c TIMEOUT after {time.perf_counter() - t0:.1f} s")
        return 2
    except (DimacsError, ValueError, OSError) as e:
        print(f"c ERROR: {e}")
        print("s NOT VERIFIED")
        return 1
    print(f"c pydrat: {msg} ({time.perf_counter() - t0:.2f} s)")
    print("s VERIFIED" if ok else "s NOT VERIFIED")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
