#!/usr/bin/env python3
"""Self-test of the fuzzing tools against buggy_solver.py (no real solver needed).

For every injectable bug, runs fuzz.py with --shrink and checks that the bug is
detected with the expected failure kind(s), nothing else is reported, and the
shrunk formulas are small. Then runs the correct stand-in (no bug) and expects
zero failures. Failures are written to a temporary directory.

  selftest.py                  all bugs + 1000 clean formulas (a few minutes with -j 2)
  selftest.py --clean 3000     larger false-alarm run
  selftest.py --only crash,hang
"""

from __future__ import annotations

import argparse
import re
import shlex
import subprocess
import sys
import tempfile
import time
from pathlib import Path

HERE = Path(__file__).resolve().parent
STANDIN = [sys.executable, str(HERE / "buggy_solver.py")]

# bug spec, accepted kinds, fuzz.py flags, formulas, max clauses after shrinking
CASES = [
    ("flip-answer:0.1", {"disagree", "model-invalid"}, [], 150, 2),
    ("bad-model:0.1", {"model-invalid"}, [], 150, 2),
    ("partial-model:0.1", {"model-incomplete", "model-invalid"}, [], 150, 2),
    ("crash:0.1", {"crash"}, [], 100, 0),
    ("drop-clause:1", {"model-invalid"}, [], 150, 2),
    ("truncate-long:1", {"disagree", "proof-rejected"},
     ["--family", "mixed", "--max-vars", "20", "--checker", "rupcheck"], 40, 8),
    ("garbage:0.1", {"garbage"}, [], 100, 0),
    ("bad-exit:0.1", {"exit-code"}, [], 100, 0),
    ("error:0.1", {"error"}, [], 100, 0),
    ("bad-proof:0.2", {"proof-rejected"}, ["--checker", "rupcheck"], 150, 12),
    # -t 1 with small formulas, so that the stand-in never runs out of time legitimately
    ("hang:0.1", {"hang"}, ["-t", "1", "--max-vars", "40"], 60, 0),
    ("unknown:0.1", {"timeout"}, ["-t", "1", "--max-vars", "40"], 60, 0),
]

FAIL_RE = re.compile(r"^FAIL (\S+) seed=(\d+) ")
SHRUNK_RE = re.compile(r"^SHRUNK (\S+) seed=(\d+): shrunk (\d+)v/(\d+)c -> (\d+)v/(\d+)c \((\d+) runs\)")


def run_fuzz(solver: list[str], flags: list[str], outdir: Path, jobs: int) -> tuple[list[tuple], str, float]:
    cmd = [sys.executable, str(HERE / "fuzz.py"), "--solver", shlex.join(solver), "-j", str(jobs),
           "--progress", "0", "-q", "--failures-dir", str(outdir)] + flags
    t0 = time.perf_counter()
    p = subprocess.run(cmd, capture_output=True, text=True)
    fails = []
    shrunk = {}
    summary = ""
    for line in p.stdout.splitlines():
        m = FAIL_RE.match(line)
        s = SHRUNK_RE.match(line)
        if m:
            fails.append((m.group(1), int(m.group(2))))
        elif s:
            shrunk[(s.group(1), int(s.group(2)))] = tuple(map(int, s.groups()[2:]))
        elif "summary:" in line:
            summary = line
    fails = [(k, seed, shrunk.get((k, seed))) for k, seed in fails]
    if p.returncode not in (0, 1):
        print(p.stdout + p.stderr, file=sys.stderr)
        raise SystemExit(f"fuzz.py exited with {p.returncode}")
    return fails, summary, time.perf_counter() - t0


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--clean", type=int, default=1000, help="formulas for the no-bug run (0 = skip)")
    ap.add_argument("--clean-checker", default="rupcheck", help="proof checker for the no-bug run")
    ap.add_argument("--only", help="comma-separated bug names to test")
    ap.add_argument("-j", "--jobs", type=int, default=2)
    ap.add_argument("--seed", type=int, default=7000)
    args = ap.parse_args(argv)
    only = set(args.only.split(",")) if args.only else None
    ok = True
    with tempfile.TemporaryDirectory(prefix="popso-selftest-") as td:
        print(f"{'bug':18} {'formulas':>8} {'failures':>8}  kinds / shrunk (vars/clauses, runs)")
        for spec, kinds, flags, count, max_clauses in CASES:
            name = spec.split(":")[0]
            if only and name not in only:
                continue
            fails, _, secs = run_fuzz(STANDIN + [f"--bug={spec}"],
                                      flags + ["--count", str(count), "--seed", str(args.seed), "--shrink"],
                                      Path(td) / name, args.jobs)
            found = {k for k, _, _ in fails}
            shrunk = [(k, s) for k, _, s in fails if s]
            problems = []
            if not fails:
                problems.append("bug not detected")
            if found - kinds:
                problems.append(f"unexpected kinds {sorted(found - kinds)}")
            big = [s for _, s in shrunk if s[3] > max_clauses]
            if big:
                problems.append(f"shrunk formula larger than {max_clauses} clauses")
            desc = ", ".join(f"{k}: {s[0]}v/{s[1]}c -> {s[2]}v/{s[3]}c ({s[4]} runs)" for k, s in shrunk)
            kc = ", ".join(f"{k} x{sum(1 for f in fails if f[0] == k)}" for k in sorted(found))
            print(f"{spec:18} {count:8} {len(fails):8}  {kc}; {desc}  [{secs:.0f}s]"
                  + (f"  <-- FAIL: {'; '.join(problems)}" if problems else ""), flush=True)
            ok &= not problems
        if args.clean and not only:
            fails, summary, secs = run_fuzz(STANDIN, ["--count", str(args.clean), "--seed", str(args.seed),
                                                      "--checker", args.clean_checker], Path(td) / "clean", args.jobs)
            print(f"{'(no bug)':18} {args.clean:8} {len(fails):8}  {summary.replace('c ---- summary: ', '')}"
                  + ("  <-- FAIL: false alarms" if fails else ""), flush=True)
            for f in fails[:10]:
                print(f"    {f}")
            ok &= not fails
    print("selftest:", "OK" if ok else "FAILED")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
