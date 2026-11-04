#!/usr/bin/env python3
"""Reference statuses: run reference solvers over a set, write benchmarks/reference/status.json.

    .venv/bin/python benchmarks/reference.py --set tiny --set small            # cadical195
    .venv/bin/python benchmarks/reference.py --set satlib_structured --only-unknown -t 120
    .venv/bin/python benchmarks/reference.py --set gate --solver cadical195 --solver kissat404
    .venv/bin/python benchmarks/reference.py --set dev --solver kissat -t 600   # a binary in
                                                     # <main>/benchmarks/tools/build/bin (if built)

Solvers: PySAT names (cadical195, kissat404, glucose4, minisat22, ...) run through
benchmarks/tools/pysat_cli.py; anything else is resolved like run.py --solver (binary path or
a name in <main>/benchmarks/tools/build/bin) and gets --time-arg (default '--time={}', Kissat/
CaDiCaL style).  Every SAT answer is verified against the formula (an invalid model is an error
and gets no vote).  UNSAT answers are not proof-checked here.

status.json: instances[key] = {status (consensus), solvers: {name: {status, time, version,
time_limit, machine, date}}}.  The consensus is 'sat' if any solver returned a verified model,
'unsat' if a solver said UNSAT and none found a model, 'conflict' (loud) if both, else
'unknown'.  A conflict with the set file's expected status is reported loudly too.  The file is
rewritten atomically after every instance; (instance, solver) pairs already recorded are skipped
unless --redo.  Keep -j <= 2 on the shared machine.
"""

from __future__ import annotations

import argparse
import datetime as dt
import json
import os
import platform
import subprocess
import sys
import tempfile
import threading
from concurrent.futures import ThreadPoolExecutor, as_completed
from pathlib import Path

BENCH = Path(__file__).resolve().parent
sys.path.insert(0, str(BENCH))
sys.path.insert(0, str(BENCH / "tools"))

from lib import paths  # noqa: E402
from lib.output import SAT, UNSAT, parse_output  # noqa: E402
from lib.proc import kill_all, run_capped  # noqa: E402
from lib.sets import read_set  # noqa: E402
from lib.verify import verify_model  # noqa: E402
from pysat_cli import UNDERLYING, version_string  # noqa: E402

DEFAULT_OUT = paths.REFERENCE / "status.json"


def machine_name() -> str:
    cpu = ""
    try:
        if sys.platform == "darwin":
            cpu = subprocess.run(["sysctl", "-n", "machdep.cpu.brand_string"], capture_output=True,
                                 text=True, timeout=5).stdout.strip()
        elif sys.platform.startswith("linux"):
            for ln in Path("/proc/cpuinfo").read_text().splitlines():
                if ln.startswith("model name"):
                    cpu = ln.split(":", 1)[1].strip()
                    break
    except (OSError, subprocess.SubprocessError):
        pass
    return f"{cpu or platform.processor() or '?'} ({platform.system()} {platform.machine()})"


def solver_command(name: str, time_arg: str):
    """(label, argv prefix, time-arg template, version string).  The label is what status.json
    records: the PySAT name, or the binary's file name (never a local path)."""
    if name in UNDERLYING:
        return (name, [sys.executable, str(BENCH / "tools" / "pysat_cli.py"), f"--solver={name}"],
                "--time-limit={}", version_string(name))
    from run import resolve_solver
    cmd = resolve_solver(name)
    label = Path(cmd[0]).name
    ver = "?"
    try:
        out = subprocess.run(cmd + ["--version"], capture_output=True, text=True, timeout=10)
        ver = (out.stdout.strip().splitlines() or ["?"])[0]
    except (OSError, subprocess.SubprocessError):
        pass
    return label, cmd, time_arg, ver if ver.startswith(label) else f"{label} {ver}"


def solve(entry, name, cmd, time_tmpl, version, args):
    t = args.time_limit
    with tempfile.TemporaryDirectory(prefix="psat-ref-") as td:
        out_path = Path(td) / "out"
        argv = cmd + ([time_tmpl.replace("{}", f"{t:g}")] if time_tmpl else []) + [str(entry.path)]
        with open(out_path, "wb") as fh:
            r = run_capped(argv, t + max(10.0, 0.1 * t), args.mem_limit or None, stdout=fh,
                           stderr=subprocess.DEVNULL)
        with open(out_path, "rb") as fh:
            o = parse_output(fh)
    rec = {"status": "unknown", "time": round(r.wall, 3), "version": version, "time_limit": t,
           "machine": MACHINE, "date": dt.date.today().isoformat()}
    if r.reason:
        rec["note"] = r.reason
    elif o.status == SAT:
        v = verify_model(entry.path, o.model) if o.model_terminated else None
        if v is not None and v.ok:
            rec["status"] = "sat"
        else:
            rec["status"] = "error"
            rec["note"] = "invalid model: " + (v.message if v else "no complete model")
    elif o.status == UNSAT:
        rec["status"] = "unsat"
    elif o.status is None:
        rec["status"] = "error"
        rec["note"] = f"no 's' line, exit {r.returncode}"
    return rec


def consensus(solvers: dict) -> str:
    sts = {r["status"] for r in solvers.values()}
    if "sat" in sts and "unsat" in sts:
        return "conflict"
    if "sat" in sts:
        return "sat"
    if "unsat" in sts:
        return "unsat"
    return "unknown"


MACHINE = machine_name()


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--set", action="append", default=[], required=True)
    ap.add_argument("--solver", action="append", default=[],
                    help="reference solver (repeatable; default cadical195)")
    ap.add_argument("-t", "--time-limit", type=float, default=300.0)
    ap.add_argument("-j", "--jobs", type=int, default=1)
    ap.add_argument("--mem-limit", type=int, default=2048, help="MB per solver process (RSS watchdog)")
    ap.add_argument("--time-arg", default="--time={}",
                    help="time-limit argument template for binaries (write --time-arg='--x={}')")
    ap.add_argument("--only-unknown", action="store_true",
                    help="only instances without a status in the set file or status.json")
    ap.add_argument("--redo", action="store_true", help="re-run pairs already recorded")
    ap.add_argument("--filter", help="regex on the instance key")
    ap.add_argument("--out", default=str(DEFAULT_OUT))
    args = ap.parse_args(argv)
    solvers = args.solver or ["cadical195"]

    out = Path(args.out)
    data = json.loads(out.read_text()) if out.exists() else {}
    insts = data.setdefault("instances", {})
    entries = []
    for s in args.set:
        entries += read_set(s)
    if args.filter:
        import re
        entries = [e for e in entries if re.search(args.filter, e.key)]
    missing = [e.key for e in entries if not e.path.exists()]
    if missing:
        print(f"{len(missing)} file(s) missing (skipped), e.g. {missing[:3]}", file=sys.stderr)
    entries = [e for e in entries if e.path.exists()]
    if args.only_unknown:
        entries = [e for e in entries if not e.expected
                   and insts.get(e.key, {}).get("status") not in ("sat", "unsat")]
    cmds = {}
    for s in solvers:
        label, *rest = solver_command(s, args.time_arg)
        cmds[label] = rest
    solvers = list(cmds)
    tasks = [(e, s) for e in entries for s in solvers
             if args.redo or s not in insts.get(e.key, {}).get("solvers", {})]
    print(f"{len(tasks)} solves ({len(entries)} instances x {len(solvers)} solver(s)), time limit "
          f"{args.time_limit:g} s, jobs {args.jobs}, machine {MACHINE}")
    lock = threading.Lock()
    loud = []

    def save():
        data["note"] = ("reference statuses (benchmarks/reference.py); SAT verified by model check, "
                        "UNSAT not proof-checked")
        data["instances"] = dict(sorted(insts.items()))
        tmp = out.with_suffix(".json.tmp")
        out.parent.mkdir(parents=True, exist_ok=True)
        tmp.write_text(json.dumps(data, indent=1) + "\n")
        os.replace(tmp, out)

    def record(e, s, rec):
        with lock:
            ent = insts.setdefault(e.key, {"solvers": {}})
            ent["solvers"][s] = rec
            ent["status"] = consensus(ent["solvers"])
            msg = ""
            if ent["status"] == "conflict":
                msg = "  <<<<<< CONFLICT between reference solvers"
            elif e.expected and ent["status"] in ("sat", "unsat") and ent["status"] != e.expected:
                msg = f"  <<<<<< CONTRADICTS the set file ({e.expected})"
            if rec["status"] == "error":
                msg += f"  << {rec.get('note', '')}"
            if msg.strip().startswith("<<<<<<"):
                loud.append(f"{e.key}: {msg.strip()}")
            print(f"{e.key:<70} {s:<11} {rec['status']:<8} {rec['time']:>9.2f}{msg}", flush=True)
            save()

    try:
        with ThreadPoolExecutor(max_workers=max(1, args.jobs)) as ex:
            futs = {ex.submit(solve, e, s, *cmds[s], args): (e, s) for e, s in tasks}
            for f in as_completed(futs):
                e, s = futs[f]
                record(e, s, f.result())
    except KeyboardInterrupt:
        kill_all()
        print("interrupted; finished instances are saved", file=sys.stderr)
        return 130
    if loud:
        print("\n" + "!" * 78)
        for m in loud:
            print("!!! " + m)
        print("!" * 78)
        return 1
    print(f"written {paths.portable(out)} ({len(insts)} instances)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
