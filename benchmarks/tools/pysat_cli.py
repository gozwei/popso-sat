#!/usr/bin/env python3
"""Stand-in solver implementing popso-sat's CLI contract on top of PySAT.

    pysat_cli.py [--solver NAME] [options] <input.cnf|.cnf.gz|.cnf.xz> [<proof-file>]
      --solver=NAME        PySAT solver: cadical195 (default), kissat404, glucose4, glucose42,
                           minisat22, lingeling, maplechrono, cadical153, ... (pysat.solvers)
      --proof=<file>       text DRAT proof (only solvers with PySAT proof support: cadical*,
                           glucose*, lingeling, maple*; others write no proof)
      --time-limit=<sec>   -t <sec>     --mem-limit=<MB>     --seed=<n> (ignored)
      -n / --no-model      -q / --quiet  -v / --verbose      --version
      --<option>=<value>   any other option is accepted and ignored (e.g. --deterministic)
    stdout: 'c ...', 's SATISFIABLE' + 'v ... 0' | 's UNSATISFIABLE' | 's UNKNOWN'
    exit:   10 SAT, 20 UNSAT, 0 unknown, 1 error

Used to test benchmarks/run.py and the gates before popso-sat solves anything, and by
benchmarks/reference.py.  The solve runs in a worker subprocess; the time limit is enforced by
the parent (some PySAT back ends, e.g. CaDiCaL and Kissat, cannot be interrupted from Python),
which then prints 's UNKNOWN'.

FAKE_BUG=<kind> injects a defect to check that run.py catches it (FAKE_BUG_MATCH=<substring>
restricts it to matching input paths):
  flip      SAT model with one clause falsified          -> WRONG (model check)
  unsat     claim UNSAT for every input (empty proof)    -> WRONG on SAT instances
  sat       claim SAT with an all-false model            -> WRONG on UNSAT instances
  nomodel   's SATISFIABLE' without 'v' lines            -> error
  badproof  proof truncated to its first half            -> rejected by drat-trim (WRONG)
  exitcode  exit code 0 with a definite answer           -> error
  hang      ignore the time limit                        -> killed by the runner
  mem       allocate memory until killed                 -> memlimit
  crash     abort()                                      -> error
"""

from __future__ import annotations

import os
import subprocess
import sys
import time
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from lib.dimacs import CnfStream, DimacsError  # noqa: E402

UNDERLYING = {
    "cadical103": "CaDiCaL 1.0.3", "cadical153": "CaDiCaL 1.5.3", "cadical195": "CaDiCaL 1.9.5",
    "cadical300": "CaDiCaL 3.0.0", "kissat404": "Kissat 4.0.4", "glucose3": "Glucose 3.0",
    "glucose4": "Glucose 4.1", "glucose42": "Glucose 4.2.1", "minisat22": "MiniSat 2.2.0",
    "minisatgh": "MiniSat (GitHub version)", "lingeling": "Lingeling bbc-9230380-160707",
    "maplechrono": "MapleLCMDistChronoBT", "maplecm": "MapleCM", "maplesat": "MapleCOMSPS",
    "mergesat3": "MergeSat 3.0", "cryptosat": "CryptoMiniSat", "gluecard3": "Gluecard 3.0",
    "gluecard4": "Gluecard 4.1", "minicard": "Minicard 1.2",
}
PROOF_SOLVERS = ("cadical103", "cadical153", "cadical195", "cadical300", "glucose3", "glucose4",
                 "glucose42", "lingeling", "maplechrono", "maplecm", "maplesat")


def version_string(name: str) -> str:
    try:
        import pysat
        pv = pysat.__version__
    except ImportError:
        pv = "?"
    return f"PySAT {pv} {name} ({UNDERLYING.get(name, '?')})"


def parse_args(argv):
    o = {"solver": "cadical195", "proof": None, "time_limit": None, "mem_limit": None,
         "model": True, "quiet": False, "verbose": False, "input": None, "ignored": [],
         "worker": False}
    pos = []
    i = 0
    while i < len(argv):
        a = argv[i]
        val = None
        if a.startswith("--") and "=" in a:
            a, val = a.split("=", 1)

        def need():
            nonlocal i, val
            if val is not None:
                return val
            i += 1
            if i >= len(argv):
                raise SystemExit(f"error: option {a} needs a value")
            return argv[i]

        if a == "--solver":
            o["solver"] = need()
        elif a == "--proof":
            o["proof"] = need()
        elif a in ("--time-limit", "-t", "--time"):
            o["time_limit"] = float(need())
        elif a == "--mem-limit":
            o["mem_limit"] = float(need())
        elif a == "--seed":
            need()
        elif a in ("-n", "--no-model"):
            o["model"] = False
        elif a in ("-q", "--quiet"):
            o["quiet"] = True
        elif a in ("-v", "--verbose"):
            o["verbose"] = True
        elif a == "--_worker":
            o["worker"] = True
        elif a == "--version":
            print(version_string(o["solver"]))
            raise SystemExit(0)
        elif a in ("-h", "--help"):
            print(__doc__)
            raise SystemExit(0)
        elif a.startswith("-") and a != "-":
            o["ignored"].append(a if val is None else f"{a}={val}")
        else:
            pos.append(a)
        i += 1
    if not pos:
        raise SystemExit("error: no input file")
    o["input"] = pos[0]
    if len(pos) > 1 and o["proof"] is None:
        o["proof"] = pos[1]
    return o


def bug_kind(path):
    b = os.environ.get("FAKE_BUG", "")
    if b and os.environ.get("FAKE_BUG_MATCH", "") in str(path):
        return b
    return ""


def worker(o):
    """Solve in this process; print the result lines; exit code as per the contract."""
    from pysat.solvers import Solver

    if o["mem_limit"]:
        sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
        from lib.proc import limit_self
        limit_self(o["mem_limit"])
    bug = bug_kind(o["input"])
    want_proof = o["proof"] is not None and o["solver"] in PROOF_SOLVERS
    s = Solver(name=o["solver"], with_proof=want_proof)
    stream = CnfStream(o["input"])
    empty = False
    clauses_for_bug = []
    try:
        for cl in stream:
            if not cl:
                empty = True
                continue
            s.add_clause(cl)
            if bug == "flip" and len(clauses_for_bug) < 1000:
                clauses_for_bug.append(cl)
    except DimacsError as e:
        print(f"c ERROR: {e}", flush=True)
        return 1
    nvars = max(stream.nvars or 0, stream.max_var)
    if not o["quiet"]:
        print(f"c {version_string(o['solver'])}")
        print(f"c {nvars} variables, {stream.count} clauses")
    t0 = time.perf_counter()
    res = False if empty else s.solve()
    if not o["quiet"]:
        print(f"c solve time {time.perf_counter() - t0:.3f} s")
    if bug == "unsat":
        res = False
    if bug == "sat":
        res = True
    if res is True:
        model = s.get_model() if bug != "sat" else [-v for v in range(1, nvars + 1)]
        model = list(model or [])
        if len(model) < nvars:  # variables the solver never saw (not in any clause)
            model += [-v for v in range(len(model) + 1, nvars + 1)]
        if bug == "flip":
            pos = {abs(x): i for i, x in enumerate(model)}
            for cl in clauses_for_bug:
                if len({abs(x) for x in cl}) == len(cl) and all(abs(x) in pos for x in cl):
                    for x in cl:
                        model[pos[abs(x)]] = -x
                    break
        print("s SATISFIABLE")
        if o["model"] and bug != "nomodel":
            line = ["v"]
            for x in model:
                line.append(str(x))
                if len(line) > 20:
                    print(" ".join(line))
                    line = ["v"]
            line.append("0")
            print(" ".join(line))
        rc = 10
    elif res is False:
        if o["proof"] is not None and (want_proof or empty or bug == "unsat"):
            lines = (s.get_proof() or []) if want_proof and not empty and bug != "unsat" else []
            if bug == "badproof":
                lines = lines[: len(lines) // 2]
            with open(o["proof"], "w") as fh:
                for ln in lines:
                    fh.write(ln if ln.endswith("\n") else ln + "\n")
        elif o["proof"] is not None and not o["quiet"]:
            print(f"c {o['solver']} has no proof support in PySAT: no proof written")
        print("s UNSATISFIABLE")
        rc = 20
    else:
        print("s UNKNOWN")
        rc = 0
    sys.stdout.flush()
    s.delete()
    if bug == "exitcode":
        return 0
    return rc


def main(argv=None):
    o = parse_args(sys.argv[1:] if argv is None else argv)
    if o["worker"]:
        return worker(o)
    if not os.path.exists(o["input"]):
        print(f"c ERROR: cannot open {o['input']}", flush=True)
        return 1
    bug = bug_kind(o["input"])
    if bug == "crash":
        sys.stdout.flush()
        os.abort()
    if bug == "mem":
        hog = []
        while True:
            hog.append(bytearray(64 << 20))
            time.sleep(0.05)
    if bug == "hang":
        while True:
            time.sleep(3600)
    cmd = [sys.executable, os.path.abspath(__file__), "--_worker"] + sys.argv[1:]
    p = subprocess.Popen(cmd, stdout=subprocess.PIPE, stdin=subprocess.DEVNULL)
    try:
        out, _ = p.communicate(timeout=o["time_limit"])
    except subprocess.TimeoutExpired:
        p.kill()
        p.communicate()
        print(f"c time limit {o['time_limit']:g} s reached")
        print("s UNKNOWN", flush=True)
        return 0
    except KeyboardInterrupt:
        p.kill()
        print("s UNKNOWN", flush=True)
        return 0
    sys.stdout.buffer.write(out)
    sys.stdout.flush()
    if p.returncode < 0:
        print(f"c worker killed by signal {-p.returncode}", flush=True)
        if o["mem_limit"]:
            print("c possibly out of memory", flush=True)
        print("s UNKNOWN", flush=True)
        return 0
    return p.returncode


if __name__ == "__main__":
    sys.exit(main())
