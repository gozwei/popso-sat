#!/usr/bin/env python3
"""Out-of-memory fuzzing: allocation failure injection on fuzz formulas.

The solver under test is the CLI linked with oom/alloc_fail.cpp (see there for the build line),
whose operator new fails at allocation number PSAT_FAIL_AT. For each formula (gen.py, with fuzzed
options from --option-ranges), one run counts the allocations, then the formula is rerun with
allocation N failing, once and from N on, for a sample of N (always 1, 2, 3 and the last), and
each run is checked by fuzzlib.check: running out of memory must end in 's UNKNOWN' (exit 0) or a
correct answer, never a crash, an error exit, malformed output or a wrong answer.

  c++ -std=c++20 -O2 -DNDEBUG -DPSAT_VERSION='"oom"' -Isrc apps/popso_sat_main.cpp \\
      benchmarks/fuzz/oom/alloc_fail.cpp build/libpsat_lib.a -o build/popso-sat-oom
  oomfuzz.py --solver build/popso-sat-oom --seed 9100000 --count 200
"""
import argparse
import os
import random
import shlex
import subprocess
import sys
import tempfile
from collections import Counter
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import fuzz  # noqa: E402
import fuzzlib  # noqa: E402
import gen  # noqa: E402


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--solver", required=True, help="the CLI linked with oom/alloc_fail.cpp")
    ap.add_argument("--seed", type=int, default=0)
    ap.add_argument("--count", type=int, default=100)
    ap.add_argument("--points", type=int, default=24, help="failing allocation numbers sampled per formula")
    ap.add_argument("--family", default=None)
    ap.add_argument("--option-ranges", default=str(HERE / "all_options.txt"))
    ap.add_argument("--option-prob", type=float, default=0.3)
    ap.add_argument("-t", "--time-limit", type=float, default=5)
    args = ap.parse_args()

    solver = shlex.split(args.solver)
    families = args.family.split(",") if args.family else None
    ranges = fuzz.parse_option_ranges(args.option_ranges) if args.option_ranges else []
    checker, label = fuzzlib.resolve_checker("auto")
    stats: Counter = Counter()
    failures = []
    tmp = Path(tempfile.mkdtemp(prefix="oomfuzz-"))
    for seed in range(args.seed, args.seed + args.count):
        f = gen.generate(seed, families)
        opts = fuzz.pick_options(seed, ranges, args.option_prob, True)
        work = tmp / str(seed)
        work.mkdir()
        cnf = work / "formula.cnf"
        fuzzlib.write_dimacs(cnf, f.nvars, f.clauses)
        r = subprocess.run(solver + opts + [f"--time-limit={int(args.time_limit)}", str(cnf)],
                           env=dict(os.environ, PSAT_ALLOC_COUNT="1"), capture_output=True, text=True,
                           timeout=3 * args.time_limit + 10)
        total = next((int(l.split()[2]) for l in r.stderr.splitlines() if l.startswith("c allocs")), 0)
        if total == 0:
            print(f"seed {seed}: no allocation count (is the solver linked with oom/alloc_fail.cpp?)")
            return 2
        rng = random.Random(seed)
        points = sorted({rng.randint(1, total) for _ in range(args.points)} | {1, 2, 3, total})
        for n in points:
            for persist in (False, True):
                env = ["env", f"PSAT_FAIL_AT={n}"] + (["PSAT_FAIL_PERSIST=1"] if persist else [])
                cfg = fuzzlib.Config(solver=env + solver, time_limit=args.time_limit, proof=True,
                                     checker=checker, checker_label=label)
                o = fuzzlib.check(f.nvars, f.clauses, cfg, opts, work, expected=f.expected)
                stats["runs"] += 1
                stats[o.status or "no answer"] += 1
                if o.kind:
                    stats[o.kind] += 1
                    failures.append(o)
                    print(f"FAIL seed={seed} n={n}/{total} persist={int(persist)} {o.kind}: {o.detail[:160]}",
                          flush=True)
        stats["formulas"] += 1
    print("c oomfuzz:", ", ".join(f"{k} {v}" for k, v in stats.items()))
    for o in failures[:10]:
        print("c replay:", fuzzlib.shell_join(o.cmd))
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())
