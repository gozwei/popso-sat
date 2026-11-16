#!/usr/bin/env python3
"""Faster screens: run only the instances a change can decide, reuse the baseline for the rest.

Most of a 300 s screen's time goes to instances nobody solves (81% of sc2026's CPU time at
1000 s, 86% of fresh's), and most changes are options that leave the default search unchanged
on most instances. Three steps cut a screen to those instances; the release gate stays the
full sets at 1000 s.

  subset    a dev subset of a set from earlier results: the instances some run solved within
            its limit, minus those every run solved within --easy seconds.

                screen.py subset --set sc2026 --out benchmarks/sets/sc2026_dev.txt R1.json R2.json ...

  affected  the instances whose search a change alters within --conflicts conflicts: both
            sides run with --conflicts=N, and an instance is affected unless conflicts,
            decisions, propagations, ticks and the answer agree. Counts, not timings, so any
            machine will do (the M4 while the box runs screens). A side that hits --timeout
            counts as affected. Fingerprints are cached per binary (sha256), arguments, limit
            and instance, so a second candidate against the same baseline runs one side.
            Late inprocessing differences beyond N conflicts are missed: raise --conflicts
            for changes to search-time passes.

                screen.py affected --set sc2026_dev --solver bin/popso-sat \\
                    --args='--mergepairs=1' --out sets_local/mp_sc2026.txt -j 2

  merge     a candidate run on a subset plus the baseline run on the full set: a full-set
            result file (baseline results for the instances the candidate did not run, which
            are unaffected by construction), for compare.py / the usual tables.

                screen.py merge --base S300_base.json --cand S300_cand_subset.json --out merged.json

The baseline must be a run of the same binary and limits on the same machine (the box: a
dedicated machine, so a cached baseline is fair for screening; a decision on a default takes a
paired or full run).
"""

from __future__ import annotations

import argparse
import concurrent.futures as cf
import hashlib
import json
import re
import shlex
import subprocess
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from lib import paths, sets  # noqa: E402

FIELDS = ("conflicts", "decisions", "propagations", "ticks")
LINE = re.compile(r"^c (conflicts|decisions|propagations|ticks)\s+(\d+)")


def solved(r, limit=None):
    return r["class"] == "ok" and r["status"] in ("SAT", "UNSAT") and (limit is None or r["time"] <= limit)


def load_results(path):
    return {r["instance"]: r for r in json.loads(Path(path).read_text())["results"]}


def cmd_subset(a):
    runs = [load_results(p) for p in a.results]
    entries = sets.read_set(a.set)
    keep = []
    for e in entries:
        rs = [run[e.key] for run in runs if e.key in run]
        if not any(solved(r) for r in rs):
            continue
        if rs and all(solved(r, a.easy) for r in rs):
            continue
        keep.append((e.key, e.expected, e.comment))
    header = [f"dev subset of {a.set}: {len(keep)} of {len(entries)} instances (benchmarks/tools/screen.py subset)",
              f"kept: solved by at least one of the runs below, and not solved within {a.easy:g} s by all of them",
              "for screens only; release gates and BENCHMARKS tables use the full set",
              "runs: " + ", ".join(Path(p).name for p in a.results)]
    sets.write_set(Path(a.out), keep, header)
    print(f"{a.out}: {len(keep)} of {len(entries)}")


def fingerprint(solver, args, conflicts, inst, timeout):
    cmd = shlex.split(solver) + shlex.split(args) + [f"--conflicts={conflicts}", "-v", str(inst)]
    try:
        out = subprocess.run(cmd, capture_output=True, text=True, timeout=timeout).stdout
    except subprocess.TimeoutExpired:
        return "timeout"
    fp = {}
    for ln in out.splitlines():
        m = LINE.match(ln)
        if m:
            fp[m.group(1)] = int(m.group(2))
        elif ln.startswith("s "):
            fp["s"] = ln[2:].strip()
    return fp if all(f in fp for f in FIELDS) else "incomplete"


def cmd_affected(a):
    binary = Path(shlex.split(a.solver)[0])
    sha = hashlib.sha256(binary.read_bytes()).hexdigest()[:16]
    cache_path = Path(a.cache) if a.cache else paths.results_dir() / "affected_cache.json"
    cache = json.loads(cache_path.read_text()) if cache_path.exists() else {}
    entries = sets.read_set(a.set)
    jobs = {}
    for e in entries:
        for side in (a.base_args, a.args):
            k = f"{sha}|{side}|{a.conflicts}|{e.key}"
            if k not in cache:
                jobs[k] = (side, e.path)
    print(f"{len(entries)} instances, {len(jobs)} runs to do ({2 * len(entries) - len(jobs)} cached)", flush=True)
    with cf.ThreadPoolExecutor(a.jobs) as ex:
        futs = {ex.submit(fingerprint, a.solver, side, a.conflicts, p, a.timeout): k for k, (side, p) in jobs.items()}
        for i, f in enumerate(cf.as_completed(futs), 1):
            cache[futs[f]] = f.result()
            if i % 20 == 0 or i == len(futs):
                cache_path.write_text(json.dumps(cache))
                print(f"  {i}/{len(futs)}", flush=True)
    cache_path.write_text(json.dumps(cache))
    keep = []
    for e in entries:
        fa = cache[f"{sha}|{a.base_args}|{a.conflicts}|{e.key}"]
        fb = cache[f"{sha}|{a.args}|{a.conflicts}|{e.key}"]
        if not isinstance(fa, dict) or not isinstance(fb, dict) or fa != fb:
            why = "differs" if isinstance(fa, dict) and isinstance(fb, dict) else f"{fa if not isinstance(fa, dict) else fb}"
            keep.append((e.key, e.expected, why))
    header = [f"instances of {a.set} whose search '{a.args}' changes (against '{a.base_args}') within "
              f"{a.conflicts} conflicts: {len(keep)} of {len(entries)} (benchmarks/tools/screen.py affected)",
              f"binary sha256 {sha}"]
    sets.write_set(Path(a.out), keep, header)
    print(f"{a.out}: {len(keep)} of {len(entries)} affected")


def cmd_merge(a):
    base = json.loads(Path(a.base).read_text())
    cand = load_results(a.cand)
    results = [cand.get(r["instance"], r) for r in base["results"]]
    missing = set(cand) - {r["instance"] for r in base["results"]}
    if missing:
        sys.exit(f"candidate instances not in the baseline: {sorted(missing)[:3]}")
    meta = dict(base["meta"])
    meta["merged"] = {"base": Path(a.base).name, "cand": Path(a.cand).name, "from_cand": len(cand)}
    ok = [r for r in results if solved(r)]
    summary = {"instances": len(results), "solved": len(ok),
               "sat": sum(r["status"] == "SAT" for r in ok), "unsat": sum(r["status"] == "UNSAT" for r in ok)}
    Path(a.out).write_text(json.dumps({"meta": meta, "summary": summary, "results": results}, indent=1))
    print(f"{a.out}: {len(cand)} from the candidate, {len(results) - len(cand)} from the baseline; "
          f"solved {summary['solved']}")


def main():
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = p.add_subparsers(dest="cmd", required=True)
    s = sub.add_parser("subset")
    s.add_argument("--set", required=True)
    s.add_argument("--out", required=True)
    s.add_argument("--easy", type=float, default=5.0)
    s.add_argument("results", nargs="+")
    f = sub.add_parser("affected")
    f.add_argument("--set", required=True)
    f.add_argument("--solver", default=str(paths.default_solver()))
    f.add_argument("--base-args", default="")
    f.add_argument("--args", required=True)
    f.add_argument("--conflicts", type=int, default=20000)
    f.add_argument("--timeout", type=float, default=300.0)
    f.add_argument("-j", "--jobs", type=int, default=1)
    f.add_argument("--cache")
    f.add_argument("--out", required=True)
    m = sub.add_parser("merge")
    m.add_argument("--base", required=True)
    m.add_argument("--cand", required=True)
    m.add_argument("--out", required=True)
    a = p.parse_args()
    {"subset": cmd_subset, "affected": cmd_affected, "merge": cmd_merge}[a.cmd](a)


if __name__ == "__main__":
    main()
