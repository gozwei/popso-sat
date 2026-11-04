#!/usr/bin/env python3
"""Self-test of the benchmark tooling (no popso-sat needed; ~30 s).

    .venv/bin/python benchmarks/selftest.py

Checks the DIMACS reader (comments, clauses across lines, '%' terminator, errors), the solver-
output parser, the model verifier, pydrat on valid / truncated / sign-flipped / binary proofs,
and run.py's classification of every FAKE_BUG defect of the PySAT stand-in (needs python-sat).
Exit code 0 if everything behaves as expected.
"""

from __future__ import annotations

import io
import json
import os
import subprocess
import sys
import tempfile
from pathlib import Path

BENCH = Path(__file__).resolve().parent
sys.path.insert(0, str(BENCH))
sys.path.insert(0, str(BENCH / "tools"))

from lib.dimacs import CnfStream, DimacsError, read_cnf, write_cnf  # noqa: E402
from lib.output import parse_output  # noqa: E402
from lib.verify import verify_model  # noqa: E402

FAILS = []


def check(cond, what):
    print(("ok    " if cond else "FAIL  ") + what)
    if not cond:
        FAILS.append(what)


def t_dimacs(tmp: Path):
    f = tmp / "a.cnf"
    f.write_text("c hello\np cnf 4 3\n1 -2\n 0 2 3 0\nc mid\n-4 0\n%\n0\n")
    nv, cl = read_cnf(f)
    check(nv == 4 and cl == [[1, -2], [2, 3], [-4]], "dimacs: comments, split clause, '%' end")
    g = tmp / "b.cnf.gz"
    write_cnf(g, 4, cl, ["x"])
    check(read_cnf(g) == (4, cl), "dimacs: gzip round trip")
    g2 = tmp / "b2.cnf.gz"
    write_cnf(g2, 4, cl, ["x"])
    check(g.read_bytes() == g2.read_bytes(), "dimacs: deterministic gzip")
    for bad, what in (("p cnf 2 1\n1 x 0\n", "bad token"), ("1 2 0\n", "no header"),
                      ("p cnf 2\n1 0\n", "bad header")):
        h = tmp / "bad.cnf"
        h.write_text(bad)
        try:
            list(CnfStream(h))
            check(False, f"dimacs: rejects {what}")
        except DimacsError:
            check(True, f"dimacs: rejects {what}")
    e = tmp / "e.cnf"
    e.write_text("p cnf 2 2\n1 2 0\n0\n")
    check(read_cnf(e)[1] == [[1, 2], []], "dimacs: a lone 0 is an empty clause")


def t_output_verify(tmp: Path):
    o = parse_output(io.BytesIO(b"c x\ns SATISFIABLE\nv 1 -2\nv 3 0\n"))
    check(o.status == "SAT" and o.model == [1, -2, 3] and o.model_terminated, "output: SAT + multi-line v")
    o = parse_output(io.BytesIO(b"s UNSATISFIABLE\ns SATISFIABLE\n"))
    check(bool(o.errors), "output: second s line is an error")
    o = parse_output(io.BytesIO(b"s SATISFIABLE\nv 1 2\n"))
    check(not o.model_terminated, "output: model without 0 is not terminated")
    f = tmp / "a.cnf"
    check(verify_model(f, [1, 2, -4]).ok, "verify: valid model")
    check(not verify_model(f, [-1, 2, -4]).ok, "verify: falsified clause")
    check(not verify_model(f, [1, -1, 2, -4]).ok, "verify: contradiction")
    v = verify_model(f, [1, 3, -4])
    check(v.ok and v.missing == 1, "verify: partial model satisfying all clauses is ok (missing=1)")
    e = tmp / "e.cnf"
    check(not verify_model(e, [1, 2]).ok, "verify: empty clause is never satisfied")


def t_pydrat(tmp: Path):
    try:
        from pysat.examples.genhard import PHP
        from pysat.solvers import Solver
    except ImportError:
        print("skip  pydrat tests (python-sat not installed)")
        return
    import pydrat
    f = PHP(6)
    cnf = tmp / "php.cnf"
    write_cnf(cnf, f.nv, f.clauses)
    s = Solver(name="cadical195", bootstrap_with=f.clauses, with_proof=True)
    s.solve()
    proof = s.get_proof()
    s.delete()
    p = tmp / "p.drat"
    p.write_text("\n".join(proof) + "\n")
    check(pydrat.check(cnf, p)[0], "pydrat: valid CaDiCaL proof verifies")
    p.write_text("\n".join(proof[: len(proof) // 2]) + "\n")
    check(not pydrat.check(cnf, p)[0], "pydrat: truncated proof is rejected")
    p.write_text("1 0\n")
    check(not pydrat.check(cnf, p)[0], "pydrat: non-RUP/RAT lemma is rejected")
    p.write_text("")
    check(not pydrat.check(cnf, p)[0], "pydrat: empty proof of a non-trivial formula is rejected")
    out = bytearray()
    for ln in proof:
        toks = ln.split()
        out.append(0x64 if toks[0] == "d" else 0x61)
        for t in toks[1:] if toks[0] == "d" else toks:
            v = int(t)
            if v == 0:
                break
            x = 2 * v if v > 0 else -2 * v + 1
            while x > 127:
                out.append((x & 127) | 128)
                x >>= 7
            out.append(x)
        out.append(0)
    p.write_bytes(bytes(out))
    check(pydrat.check(cnf, p)[0], "pydrat: binary DRAT verifies")


def t_runner(tmp: Path):
    try:
        import pysat  # noqa: F401
    except ImportError:
        print("skip  run.py tests (python-sat not installed)")
        return
    setf = tmp / "set.txt"
    setf.write_text("benchmarks/instances/tiny/php_tiny_n5.cnf unsat\n"
                    "benchmarks/instances/tiny/queens_tiny_n8.cnf sat\n")
    expect = {  # FAKE_BUG -> (php class, queens class)
        "": ("ok", "ok"), "flip": ("ok", "WRONG"), "unsat": ("WRONG", "WRONG"), "sat": ("WRONG", "WRONG"),
        "nomodel": ("ok", "error"), "badproof": ("WRONG", "ok"), "exitcode": ("error", "error"),
        "crash": ("error", "error"), "hang": ("error", "error"), "mem": ("memlimit", "memlimit"),
    }
    for bug, (c_php, c_q) in expect.items():
        extra = {"hang": ["-t", "1", "--grace", "1"], "mem": ["--mem-limit", "200"]}.get(bug, [])
        env = dict(os.environ, FAKE_BUG=bug)
        r = subprocess.run([sys.executable, str(BENCH / "run.py"), "--solver", "pysat:cadical195", "--set",
                            str(setf), "--checker", "pydrat", "--out-dir", str(tmp / "res"), "--tag", f"st{bug}"]
                           + extra, capture_output=True, text=True, env=env, cwd=str(BENCH.parent))
        res = sorted((tmp / "res").glob(f"*_st{bug}.json"))
        if not res:
            check(False, f"run.py FAKE_BUG={bug!r}: no result file ({r.stderr[-200:]})")
            continue
        d = json.loads(res[-1].read_text())
        got = {x["name"]: x["class"] for x in d["results"]}
        ok = got.get("php_tiny_n5") == c_php and got.get("queens_tiny_n8") == c_q
        wrong = c_php == "WRONG" or c_q == "WRONG"
        check(ok and (r.returncode == 1) == wrong,
              f"run.py FAKE_BUG={bug or 'none':<9} -> php {got.get('php_tiny_n5')}, queens "
              f"{got.get('queens_tiny_n8')}, exit {r.returncode}")


def main():
    with tempfile.TemporaryDirectory(prefix="psat-selftest-") as td:
        tmp = Path(td)
        t_dimacs(tmp)
        t_output_verify(tmp)
        t_pydrat(tmp)
        t_runner(tmp)
    print(f"\n{len(FAILS)} failure(s)")
    return 1 if FAILS else 0


if __name__ == "__main__":
    sys.exit(main())
