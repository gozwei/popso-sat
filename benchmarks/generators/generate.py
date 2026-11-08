#!/usr/bin/env python3
"""Generate the benchmark instance families with known status (deterministic).

    .venv/bin/python benchmarks/generators/generate.py                 # tiny + small (committed)
    .venv/bin/python benchmarks/generators/generate.py --tier medium   # medium -> <cache>/generated/medium
    .venv/bin/python benchmarks/generators/generate.py --check         # regenerate, compare sha256s
    .venv/bin/python benchmarks/generators/generate.py --only php,tseitin

Output:
  tiny    benchmarks/instances/tiny/<name>.cnf        (committed)
  small   benchmarks/instances/small/<name>.cnf.gz    (committed, deterministic gzip)
  medium  <main>/benchmarks/cache/generated/medium/<name>.cnf   (not committed; ~1-20 s for kissat)
  benchmarks/instances/manifest.json   key -> family, tier, params, status, how the status is
                                       known, sha256 of the file (all tiers, committed)
  benchmarks/sets/{tiny,small,medium}.txt

Names are <family>_<tier>_<params>.  Randomness comes from families.Rng seeded with SHA-256 of
(family, tier, params, seed).  Statuses are known by construction, by GF(2) elimination, or by
a reference solve with a PySAT solver (recorded with solver and version; UNSAT answers of tiny/
small instances are confirmed by a second solver).  Reference statuses are cached in the manifest
by formula hash, so regenerating does not solve again.  Changing a family's code changes its
instances: regenerate, re-run the reference for the affected sets, and commit the new manifest.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import platform
import subprocess
import sys
import time
from pathlib import Path

GEN = Path(__file__).resolve().parent
BENCH = GEN.parent
sys.path.insert(0, str(BENCH))
sys.path.insert(0, str(GEN))

import families as F  # noqa: E402
from lib import paths  # noqa: E402
from lib.dimacs import format_cnf, write_cnf  # noqa: E402
from lib.output import parse_output  # noqa: E402
from lib.proc import run_capped  # noqa: E402
from lib.sets import write_set  # noqa: E402
from lib.verify import verify_model  # noqa: E402

MANIFEST = paths.INSTANCES / "manifest.json"
TIERS = ("tiny", "small", "medium")

# family, tier, builder, params, and either seeds (construction) or want (reference / gf2 status)
TABLE = [
    # random k-SAT near the threshold (status by reference solve; balanced)
    ("rand3sat", "tiny", "rand_ksat", {"n": 50, "k": 3, "ratio": 4.26}, {"want": {"sat": 3, "unsat": 3}}),
    ("rand3sat", "small", "rand_ksat", {"n": 100, "k": 3, "ratio": 4.26}, {"want": {"sat": 2, "unsat": 2}}),
    ("rand3sat", "small", "rand_ksat", {"n": 150, "k": 3, "ratio": 4.26}, {"want": {"sat": 2, "unsat": 2}}),
    ("rand3sat", "medium", "rand_ksat", {"n": 275, "k": 3, "ratio": 4.26}, {"want": {"sat": 2, "unsat": 2}}),
    ("rand5sat", "small", "rand_ksat", {"n": 50, "k": 5, "ratio": 21.1}, {"want": {"sat": 1, "unsat": 1}}),
    ("rand5sat", "medium", "rand_ksat", {"n": 60, "k": 5, "ratio": 21.1}, {"want": {"sat": 1, "unsat": 1}}),
    # pigeonhole (UNSAT)
    ("php", "tiny", "php", {"n": 4}, {}),
    ("php", "tiny", "php", {"n": 5}, {}),
    ("php", "small", "php", {"n": 7}, {}),
    ("php", "small", "php", {"n": 8}, {}),
    ("php", "medium", "php", {"n": 10}, {}),
    # parity: random 3-XORSAT (status by GF(2) elimination) and XOR-chain equivalence (UNSAT)
    ("xorsat", "tiny", "xorsat", {"n": 20, "m": 20}, {"want": {"sat": 1, "unsat": 1}}),
    ("xorsat", "small", "xorsat", {"n": 60, "m": 60}, {"want": {"sat": 1, "unsat": 1}}),
    ("xorsat", "medium", "xorsat", {"n": 500, "m": 460}, {"want": {"sat": 1, "unsat": 1}}),
    ("xorchain", "tiny", "xorchain", {"n": 12}, {}),
    ("xorchain", "small", "xorchain", {"n": 30}, {}),
    ("xorchain", "medium", "xorchain", {"n": 40}, {}),
    ("xorchain", "medium", "xorchain", {"n": 48}, {}),
    # Tseitin on random regular graphs: odd charge UNSAT, even charge SAT
    ("tseitin", "tiny", "tseitin", {"n": 10, "d": 3, "odd": True}, {}),
    ("tseitin", "tiny", "tseitin", {"n": 10, "d": 3, "odd": False}, {}),
    ("tseitin", "small", "tseitin", {"n": 24, "d": 3, "odd": True}, {}),
    ("tseitin", "small", "tseitin", {"n": 16, "d": 4, "odd": True}, {}),
    ("tseitin", "small", "tseitin", {"n": 40, "d": 4, "odd": False}, {}),
    ("tseitin", "medium", "tseitin", {"n": 80, "d": 3, "odd": True}, {}),
    ("tseitin", "medium", "tseitin", {"n": 80, "d": 3, "odd": False}, {}),
    ("tseitin", "medium", "tseitin", {"n": 40, "d": 4, "odd": True}, {}),
    ("tseitin", "medium", "tseitin", {"n": 44, "d": 4, "odd": True}, {}),
    # graph coloring: planted (SAT) and random graphs (reference status)
    ("coloring", "tiny", "coloring_planted", {"n": 30, "k": 3, "deg": 4.0}, {}),
    ("coloring", "tiny", "coloring_random", {"n": 30, "k": 3, "deg": 4.7}, {"want": {"sat": 1, "unsat": 1}}),
    ("coloring", "small", "coloring_planted", {"n": 150, "k": 3, "deg": 4.4}, {}),
    ("coloring", "small", "coloring_random", {"n": 100, "k": 3, "deg": 4.7}, {"want": {"sat": 1, "unsat": 1}}),
    ("coloring", "small", "coloring_planted", {"n": 60, "k": 5, "deg": 12.0}, {}),
    ("coloring", "medium", "coloring_planted", {"n": 2000, "k": 3, "deg": 4.4}, {}),
    ("coloring", "medium", "coloring_random", {"n": 500, "k": 3, "deg": 4.65}, {"want": {"sat": 1, "unsat": 1}}),
    # n-queens (SAT)
    ("queens", "tiny", "queens", {"n": 8}, {}),
    ("queens", "small", "queens", {"n": 20}, {}),
    ("queens", "small", "queens", {"n": 40}, {}),
    ("queens", "medium", "queens", {"n": 100}, {}),
    # sudoku (SAT): published 9x9 puzzles; planted larger grids
    ("sudoku", "tiny", "sudoku_fixed", {"puzzle": "inkala2012"}, {}),
    ("sudoku", "tiny", "sudoku_fixed", {"puzzle": "escargot"}, {}),
    ("sudoku", "tiny", "sudoku_fixed", {"puzzle": "euler01"}, {}),
    ("sudoku", "tiny", "sudoku_fixed", {"puzzle": "norvighard1"}, {}),
    ("sudoku", "tiny", "sudoku_fixed", {"puzzle": "goldennugget"}, {}),
    ("sudoku", "small", "sudoku_planted", {"N": 4, "holes": 0.6}, {}),
    ("sudoku", "medium", "sudoku_planted", {"N": 6, "holes": 0.7}, {}),
    # circuits / bounded model checking
    ("addereq", "tiny", "addereq", {"n": 8, "buggy": False}, {}),
    ("addereq", "tiny", "addereq", {"n": 8, "buggy": True}, {}),
    ("addereq", "small", "addereq", {"n": 64, "buggy": False}, {}),
    ("addereq", "small", "addereq", {"n": 64, "buggy": True}, {}),
    ("multeq", "tiny", "multeq", {"n": 4, "buggy": False}, {}),
    ("multeq", "small", "multeq", {"n": 6, "buggy": False}, {}),
    ("multeq", "small", "multeq", {"n": 7, "buggy": True}, {}),
    ("multeq", "medium", "multeq", {"n": 8, "buggy": False}, {}),
    ("multeq", "medium", "multeq", {"n": 9, "buggy": False}, {}),
    ("multeq", "medium", "multeq", {"n": 24, "buggy": True}, {}),
    ("counter", "tiny", "counter", {"steps": 6, "target": 6}, {}),
    ("counter", "tiny", "counter", {"steps": 6, "target": 7}, {}),
    ("counter", "small", "counter", {"steps": 40, "target": 37}, {}),
    ("counter", "small", "counter", {"steps": 40, "target": 41}, {}),
    ("counter", "medium", "counter", {"steps": 1000, "target": 990}, {}),
    ("counter", "medium", "counter", {"steps": 1000, "target": 1001}, {}),
    # XOR-substituted formulas (for --xorsub)
    ("xorsubop", "small", "xorsub_op", {"m": 8, "d": 2, "sat": False}, {}),
    ("xorsubop", "small", "xorsub_op", {"m": 8, "d": 2, "sat": True}, {}),
    ("xorsubop", "medium", "xorsub_op", {"m": 12, "d": 2, "sat": False}, {}),
    ("xorsubphp", "small", "xorsub_php", {"n": 6, "d": 2}, {}),
    ("xorsubtseitin", "small", "xorsub_tseitin", {"n": 20, "deg": 3, "odd": True, "d": 2}, {}),
    ("xorsubtseitin", "small", "xorsub_tseitin", {"n": 20, "deg": 3, "odd": False, "d": 2}, {}),
    ("xorsubpebbling", "small", "xorsub_pebbling", {"h": 15, "d": 2}, {}),
    ("xorsubpebbling", "small", "xorsub_pebbling", {"h": 10, "d": 3}, {}),
    ("xorsubrand3sat", "small", "xorsub_ksat", {"n": 40, "k": 3, "ratio": 4.26, "d": 2}, {"want": {"sat": 1, "unsat": 1}}),
]


BOOL_TAGS = {"odd": ("odd", "even"), "buggy": ("bug", "ok"), "sat": ("sat", "unsat")}


def tag_of(params: dict) -> str:
    parts = []
    for k, v in params.items():
        if isinstance(v, bool):
            on, off = BOOL_TAGS.get(k, (k, "no" + k))
            parts.append(on if v else off)
        elif isinstance(v, float):
            parts.append(f"{k}{v:g}")
        elif isinstance(v, str):
            parts.append(v)
        else:
            parts.append(f"{k}{v}")
    return "-".join(parts).replace(".", "p")


def out_path(tier: str, name: str) -> tuple[Path, str]:
    if tier == "tiny":
        p = paths.INSTANCES / "tiny" / f"{name}.cnf"
    elif tier == "small":
        p = paths.INSTANCES / "small" / f"{name}.cnf.gz"
    else:
        p = paths.cache_dir() / "generated" / tier / f"{name}.cnf"
    return p, paths.portable(p)


def reference_status(cnf_path: Path, solver: str, time_limit: float, confirm: str | None):
    """Solve with the PySAT stand-in; SAT models are verified.  Returns a status record."""
    cli = BENCH / "tools" / "pysat_cli.py"

    def solve(name):
        cmd = [sys.executable, str(cli), f"--solver={name}", f"--time-limit={time_limit:g}", str(cnf_path)]
        out_file = cnf_path.with_name(cnf_path.name + ".refout")
        with open(out_file, "wb") as fh:
            r = run_capped(cmd, time_limit + 30, 2048, stdout=fh, stderr=subprocess.DEVNULL)
        with open(out_file, "rb") as fh:
            o = parse_output(fh)
        out_file.unlink()
        if o.status == "SAT":
            v = verify_model(cnf_path, o.model)
            if not v.ok:
                raise RuntimeError(f"{name} returned an invalid model for {cnf_path.name}: {v.message}")
            return "sat", r.wall
        if o.status == "UNSAT":
            return "unsat", r.wall
        return None, r.wall

    st, wall = solve(solver)
    sys.path.insert(0, str(BENCH / "tools"))
    from pysat_cli import version_string
    rec = {"status": st or "unknown", "solver": version_string(solver), "time": round(wall, 3),
           "time_limit": time_limit}
    if st == "unsat" and confirm:
        st2, wall2 = solve(confirm)
        if st2 != "unsat":
            raise RuntimeError(f"{confirm} says {st2} for {cnf_path.name}, {solver} said unsat")
        rec["confirmed_by"] = version_string(confirm)
    return rec


def save_status_cache(cache):
    """Merge the reference-status cache into the manifest on disk (instances untouched)."""
    man = json.loads(MANIFEST.read_text()) if MANIFEST.exists() else {"instances": {}}
    man["status_cache"] = dict(sorted({**man.get("status_cache", {}), **cache}.items()))
    tmp = MANIFEST.with_suffix(".json.tmp")
    tmp.write_text(json.dumps(man, indent=1) + "\n")
    tmp.replace(MANIFEST)


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--tier", default="tiny,small", help="comma list of tiers (default tiny,small)")
    ap.add_argument("--only", help="comma list of families")
    ap.add_argument("--check", action="store_true",
                    help="regenerate in memory and compare with the manifest's sha256 (no writes)")
    ap.add_argument("--ref-solver", default=None,
                    help="PySAT solver for reference statuses (default cadical195; kissat404 for medium)")
    ap.add_argument("--ref-time", type=float, default=300.0, help="reference solve time limit (s)")
    ap.add_argument("--max-tries", type=int, default=60, help="seeds tried per balanced entry")
    args = ap.parse_args(argv)
    tiers = [t for t in args.tier.split(",") if t]
    for t in tiers:
        if t not in TIERS:
            ap.error(f"unknown tier {t}")
    only = set(args.only.split(",")) if args.only else None

    man = json.loads(MANIFEST.read_text()) if MANIFEST.exists() else {}
    instances = man.get("instances", {})
    cache = man.get("status_cache", {})
    produced = {}
    bad = []
    t_start = time.perf_counter()
    for fam, tier, fn, params, opt in TABLE:
        if tier not in tiers or (only and fam not in only):
            continue
        build = getattr(F, fn)
        want = dict(opt.get("want", {}))
        seeds = opt.get("seeds", [0]) if not want else range(args.max_tries)
        got = {k: 0 for k in want}
        for seed in seeds:
            if want and all(got[k] >= want[k] for k in want):
                break
            tag = tag_of(params) + (f"-s{seed}" if want or "seeds" in opt else "")
            name = f"{fam}_{tier}_{tag}"
            rng = F.Rng(fam, tier, tag_of(params), seed)
            f = build(rng, **params)
            body = format_cnf(f.nvars, f.clauses)
            fhash = hashlib.sha256(body).hexdigest()
            path, key = out_path(tier, name)
            status, src = f.status, f.source
            refrec = None
            if status is None:
                old = cache.get(fhash)
                if old and (old["status"] in ("sat", "unsat") or args.check
                            or old.get("time_limit", 0) >= args.ref_time):
                    refrec = old
                elif args.check:
                    bad.append(f"{name}: no cached reference status")
                    continue
                else:
                    solver = args.ref_solver or ("kissat404" if tier == "medium" else "cadical195")
                    tmp = path.with_name(path.name.replace(".gz", "") + ".tmp.cnf")
                    tmp.parent.mkdir(parents=True, exist_ok=True)
                    tmp.write_bytes(body)
                    try:
                        refrec = reference_status(tmp, solver, args.ref_time,
                                                  "minisat22" if tier != "medium" else None)
                    finally:
                        tmp.unlink(missing_ok=True)
                    refrec["formula"] = name
                    cache[fhash] = refrec
                    save_status_cache(cache)  # an interrupted run keeps its reference solves
                    print(f"  reference {name}: {refrec['status']} ({refrec['time']:.2f} s)", flush=True)
                status = refrec["status"] if refrec["status"] in ("sat", "unsat") else None
                src = "reference"
                if status is None:
                    continue
            if want:
                if got.get(status, 0) >= want.get(status, 0):
                    continue
                got[status] += 1
            comments = [f"popso-sat benchmark generator: {name}",
                        f"family={fam} tier={tier} params={json.dumps(params, sort_keys=True)}"
                        + (f" seed={seed}" if want or "seeds" in opt else "")] + f.comments
            if src != "reference":
                comments.append(f"status: {status} (by {src})")
            data = format_cnf(f.nvars, f.clauses, comments)
            entry = {"family": fam, "tier": tier, "builder": fn, "params": params,
                     "seed": seed if (want or "seeds" in opt) else None, "status": status,
                     "status_source": src, "nvars": f.nvars, "nclauses": len(f.clauses),
                     "sha256": hashlib.sha256(data).hexdigest(), "formula_sha256": fhash}
            if refrec:
                entry["reference"] = {k: refrec[k] for k in ("solver", "time", "confirmed_by") if k in refrec}
            if args.check:
                old = instances.get(key)
                if not old or old.get("sha256") != entry["sha256"]:
                    bad.append(f"{name}: sha256 differs from the manifest")
                produced[key] = entry
                continue
            write_cnf(path, f.nvars, f.clauses, comments)
            produced[key] = entry
            print(f"{key:<72} {status:<6} {f.nvars:>7} vars {len(f.clauses):>8} clauses", flush=True)
        if want and not all(got[k] >= want[k] for k in want):
            print(f"WARNING: {fam} {tier} {params}: only {got} of {want} found in {args.max_tries} seeds",
                  file=sys.stderr)
    if args.check:
        if bad:
            print("\n".join(bad))
            return 1
        print(f"check ok: {len(produced)} instances match the manifest")
        return 0

    # drop old entries of the regenerated tiers/families, add the new ones
    for k in [k for k, v in instances.items() if v["tier"] in tiers and (not only or v["family"] in only)]:
        if k not in produced:
            del instances[k]
    instances.update(produced)
    man = {"generator": "benchmarks/generators/generate.py",
           "note": "status_source: construction | gf2-elimination | published puzzle | reference "
                   "(PySAT solve, see 'reference')",
           "updated": time.strftime("%Y-%m-%d"), "python": platform.python_version(),
           "instances": dict(sorted(instances.items())), "status_cache": dict(sorted(cache.items()))}
    MANIFEST.parent.mkdir(parents=True, exist_ok=True)
    MANIFEST.write_text(json.dumps(man, indent=1) + "\n")
    for tier in tiers:
        rows = [(k, v["status"], f"family={v['family']} {v['status_source']}")
                for k, v in sorted(instances.items()) if v["tier"] == tier]
        hdr = [f"generated {tier} instances (benchmarks/generators/generate.py --tier {tier})",
               "path  expected-status  # family, how the status is known"]
        if tier == "medium":
            hdr.insert(1, "files live in <main>/benchmarks/cache/generated/medium (not committed)")
        write_set(paths.SETS / f"{tier}.txt", rows, hdr)
    print(f"done in {time.perf_counter() - t_start:.1f} s; manifest {paths.portable(MANIFEST)}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
