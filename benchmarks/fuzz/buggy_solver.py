#!/usr/bin/env python3
"""Stand-in for popso-sat with injectable bugs, used to validate fuzz.py and ddmin.py.

Implements the popso-sat CLI contract on top of a PySAT solver (glucose4 by
default, so that it differs from the cadical195 reference):

  buggy_solver.py [options] <input.cnf | .cnf.gz | .cnf.xz | -> [<proof-file>]
    --proof=<file> --proof-text --time-limit=<sec> | -t <sec> --seed=<n>
    --conflicts=<n> -n/--no-model -q -v --mem-limit=<MB>
    --<option>=<value>      accepted and ignored (so option fuzzing works)
    --engine=<pysat name>   PySAT solver (default glucose4; proofs need glucose3/4, cadical*, ...)
    --bug=<name>[:<p>]      inject a bug with probability p (default 1), repeatable

Output: 's SATISFIABLE' + 'v ... 0' | 's UNSATISFIABLE' | 's UNKNOWN'; exit 10/20/0, 1 on error.
Proofs are DRUP from the engine, binary DRAT by default, text with --proof-text.

Bugs. Whether a bug fires is a deterministic function of the bug name and the
--seed value (of the input bytes when no --seed is given), so every failure
reproduces exactly, and ddmin (which keeps the seed) sees the bug on every
candidate and shrinks to the smallest formula that shows the symptom:
  flip-answer    report UNSAT for SAT formulas and SAT (all-false model) for UNSAT ones
  bad-model      flip one variable of the model
  partial-model  leave the largest variable out of the model
  crash          abort() (SIGABRT) before printing the answer
  drop-clause    ignore the last clause of the input (parser off-by-one)
  truncate-long  drop the last literal of every clause longer than 3 (storage
                 off-by-one): wrong UNSAT answers and proofs, a structured bug
                 whose shrunk core is a long clause plus the clauses refuting it
  hang           ignore the time limit and sleep for an hour
  unknown        wait for the time limit, then answer 's UNKNOWN'
  garbage        print a malformed line
  bad-exit       exit 0 instead of 10/20
  error          print 'c ERROR' and exit 1
  bad-proof      truncate the proof to its first half (UNSAT only)
"""

from __future__ import annotations

import gzip
import hashlib
import lzma
import os
import random
import sys
import threading
import time

BUGS = ["flip-answer", "bad-model", "partial-model", "crash", "drop-clause", "truncate-long", "hang", "unknown",
        "garbage", "bad-exit", "error", "bad-proof"]


def die(msg: str) -> None:
    print(f"c ERROR: {msg}", file=sys.stderr)
    sys.exit(1)


def read_input(name: str) -> bytes:
    if name == "-":
        return sys.stdin.buffer.read()
    with open(name, "rb") as f:
        data = f.read()
    if data[:2] == b"\x1f\x8b":
        return gzip.decompress(data)
    if data[:6] == b"\xfd7zXZ\x00":
        return lzma.decompress(data)
    return data


def parse(data: bytes) -> tuple[int, list[list[int]]]:
    nvars, nclauses = None, None
    clauses: list[list[int]] = []
    cur: list[int] = []
    for line in data.decode().splitlines():
        s = line.strip()
        if not s or s[0] == "c":
            continue
        if s[0] == "p":
            parts = s.split()
            if len(parts) != 4 or parts[1] != "cnf":
                die(f"bad header {s!r}")
            nvars, nclauses = int(parts[2]), int(parts[3])
            continue
        if s[0] == "%":
            break
        if nvars is None:
            die("clause before header")
        for tok in s.split():
            try:
                v = int(tok)
            except ValueError:
                die(f"bad token {tok!r}")
            if abs(v) > nvars:
                die(f"literal {v} exceeds header variable count {nvars}")
            if v:
                cur.append(v)
            else:
                clauses.append(cur)
                cur = []
    if cur:
        die("last clause not terminated by 0")
    if nvars is None:
        die("no header")
    if nclauses != len(clauses):
        die(f"header says {nclauses} clauses, found {len(clauses)}")
    return nvars, clauses


def varint(u: int) -> bytes:
    out = bytearray()
    while u > 127:
        out.append((u & 127) | 128)
        u >>= 7
    out.append(u)
    return bytes(out)


def write_proof(path: str, lines: list[str], text: bool) -> None:
    with open(path, "wb") as f:
        for line in lines:
            line = line.strip()
            if not line:
                continue
            delete = line.startswith("d")
            lits = [int(t) for t in line.lstrip("d").split()]
            if text:
                f.write((("d " if delete else "") + " ".join(map(str, lits)) + "\n").encode())
            else:
                f.write(b"d" if delete else b"a")
                for l in lits:
                    if l:
                        f.write(varint(2 * abs(l) + (l < 0)))
                f.write(b"\x00")


def main(argv: list[str]) -> int:
    opts: dict[str, str] = {}
    bugs: dict[str, float] = {}
    files: list[str] = []
    it = iter(argv)
    for a in it:
        if a in ("-t", "--time-limit") or a in ("--bug", "--engine", "--seed", "--proof"):
            try:
                val = next(it)
            except StopIteration:
                die(f"missing value for {a}")
            a = f"{a}={val}"
            if a.startswith("-t="):
                a = "--time-limit=" + val
        if a.startswith("--bug="):
            spec = a[len("--bug="):]
            name, _, p = spec.partition(":")
            if name not in BUGS:
                die(f"unknown bug {name!r} (known: {', '.join(BUGS)})")
            bugs[name] = float(p) if p else 1.0
        elif a.startswith("--") and "=" in a:
            k, v = a[2:].split("=", 1)
            opts[k] = v
        elif a in ("-n", "--no-model", "-q", "--quiet", "-v", "--verbose", "--proof-text"):
            opts[a.lstrip("-")] = "1"
        elif a.startswith("-") and a != "-":
            die(f"unknown option {a}")
        else:
            files.append(a)
    if not 1 <= len(files) <= 2:
        die("usage: buggy_solver.py [options] <input> [<proof>]")
    proof_path = opts.get("proof") or (files[1] if len(files) == 2 else None)
    data = read_input(files[0])
    digest = hashlib.sha256(data).hexdigest()
    seed = opts.get("seed", "input-" + digest)

    def fires(bug: str) -> bool:
        if bug not in bugs:
            return False
        return random.Random(f"{bug}|{seed}").random() < bugs[bug]

    nvars, clauses = parse(data)
    if fires("error"):
        print("c ERROR: injected error", file=sys.stderr)
        return 1
    if fires("drop-clause") and clauses:
        clauses = clauses[:-1]
    if fires("truncate-long"):
        clauses = [c[:-1] if len(c) > 3 else c for c in clauses]
    if fires("hang"):
        time.sleep(3600)
    time_limit = float(opts.get("time-limit", "0") or 0)
    if fires("unknown"):
        time.sleep(time_limit)
        print("s UNKNOWN")
        return 0

    from pysat.solvers import Solver

    engine = opts.get("engine", "glucose4")
    status, model, proof = None, None, []
    if any(len(c) == 0 for c in clauses):
        status = False
    else:
        with Solver(name=engine, bootstrap_with=clauses, with_proof=proof_path is not None) as s:
            timer = None
            if time_limit > 0:
                timer = threading.Timer(time_limit, s.interrupt)
                timer.start()
            if "conflicts" in opts:
                s.conf_budget(int(opts["conflicts"]))
            try:
                status = s.solve_limited(expect_interrupt=True) if (timer or "conflicts" in opts) else s.solve()
            except NotImplementedError:  # engine without interrupt support: no time limit
                if timer:
                    timer.cancel()
                    timer = None
                status = s.solve_limited() if "conflicts" in opts else s.solve()
            if timer:
                timer.cancel()
            if status:
                model = s.get_model() or []
            elif status is False and proof_path:
                proof = s.get_proof() or []

    print(f"c buggy_solver (PySAT {engine}), {nvars} variables, {len(clauses)} clauses")
    if fires("crash"):
        sys.stdout.flush()
        os.abort()
    if status is not None and fires("flip-answer"):
        status, model, proof = (not status), ([] if not status else None), []
    if status and model is not None:
        value = {abs(l): l > 0 for l in model}
        model = [v if value.get(v, False) else -v for v in range(1, nvars + 1)]
        if fires("bad-model") and model:
            used = sorted({abs(l) for c in clauses for l in c}) or [1]
            v = random.Random(digest).choice(used)
            model[v - 1] = -model[v - 1]
        if fires("partial-model") and model:
            model = model[:-1]

    if status is None:
        print("s UNKNOWN")
        code = 0
    elif status:
        print("s SATISFIABLE")
        if "n" not in opts and "no-model" not in opts:
            for i in range(0, len(model), 15):
                print("v " + " ".join(map(str, model[i:i + 15])))
            print("v 0")
        code = 10
    else:
        print("s UNSATISFIABLE")
        if proof_path:
            if fires("bad-proof"):
                proof = proof[: len(proof) // 2]
            write_proof(proof_path, proof, "proof-text" in opts)
        code = 20
    if fires("garbage"):
        print("this is not DIMACS output")
    if fires("bad-exit"):
        code = 0
    return code


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
