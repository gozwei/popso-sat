#!/usr/bin/env python3
"""Correctness gate: run benchmarks/sets/gate.txt strictly; must end with 'WRONG 0' and exit 0.

    .venv/bin/python benchmarks/gate.py                              # build/popso-sat
    .venv/bin/python benchmarks/gate.py --variant deterministic      # + --deterministic (for later)
    .venv/bin/python benchmarks/gate.py --solver pysat:cadical195    # harness self-test
    .venv/bin/python benchmarks/gate.py -- --keep-logs               # extra run.py options after --

Equivalent to
    run.py --set gate --strict -j 2 --mem-limit 2048 -t 30 --tag gate[-deterministic] [--extra --deterministic]
after making sure the SATLIB part of the set is in the cache (benchmarks/satlib.py --groups gate,
a few hundred KB from the SATLIB site).  --strict: any WRONG answer, any error (crash, bad exit
code, ignored time limit), and any UNSAT answer whose DRAT proof was not verified (drat-trim if
built, else the pure-Python pydrat for small proofs) fails the gate; add --allow-unchecked while
no checker can handle the proofs.  Unsolved instances do not fail the gate unless
--require-solved is given.
"""

from __future__ import annotations

import argparse
import sys
from pathlib import Path

BENCH = Path(__file__).resolve().parent
sys.path.insert(0, str(BENCH))

import run  # noqa: E402
import satlib  # noqa: E402
from lib import paths  # noqa: E402

VARIANTS = {"default": "", "deterministic": "--deterministic"}


def main(argv=None):
    argv = sys.argv[1:] if argv is None else argv
    extra_run = []
    if "--" in argv:
        i = argv.index("--")
        argv, extra_run = argv[:i], argv[i + 1:]
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--solver", default=str(paths.default_solver()))
    ap.add_argument("--variant", choices=sorted(VARIANTS), default="default")
    ap.add_argument("--set", default="gate")
    ap.add_argument("-t", "--time-limit", type=float, default=30.0)
    ap.add_argument("-j", "--jobs", type=int, default=2)
    ap.add_argument("--mem-limit", type=int, default=2048)
    ap.add_argument("--allow-unchecked", action="store_true")
    ap.add_argument("--require-solved", action="store_true")
    ap.add_argument("--no-download", action="store_true", help="do not fetch missing SATLIB files")
    ap.add_argument("--no-save", action="store_true")
    args = ap.parse_args(argv)

    if not args.no_download:
        groups = satlib.gate_groups() if args.set == "gate" else []
        root = paths.cache_dir() / "satlib"
        root.mkdir(parents=True, exist_ok=True)
        for g in groups:
            if not satlib.fetch(g, root, lambda m: print(f"[gate] {m}")):
                print(f"[gate] cannot fetch SATLIB group {g}", file=sys.stderr)
                return 2
    cmd = ["--solver", args.solver, "--set", args.set, "--strict", "-j", str(args.jobs),
           "--mem-limit", str(args.mem_limit), "-t", f"{args.time_limit:g}",
           "--tag", "gate" if args.variant == "default" else f"gate-{args.variant}"]
    flags = VARIANTS[args.variant]
    if flags:
        cmd.append(f"--extra={flags}")  # "=" form: the value starts with "-"
    if args.allow_unchecked:
        cmd.append("--allow-unchecked")
    if args.require_solved:
        cmd.append("--require-solved")
    if args.no_save:
        cmd.append("--no-save")
    cmd += extra_run
    print(f"[gate] variant {args.variant}: run.py {' '.join(paths.strip_local(c) for c in cmd)}", flush=True)
    rc = run.main(cmd)
    print(f"[gate] {'PASSED' if rc == 0 else 'FAILED'} (exit {rc})")
    return rc


if __name__ == "__main__":
    sys.exit(main())
