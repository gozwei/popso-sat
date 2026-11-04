#!/usr/bin/env python3
"""SAT Competition instances from the Global Benchmark Database (https://benchmark-database.de).

    .venv/bin/python benchmarks/gbd.py fetch-meta            # meta.db, base.db, SC2022/23 runtimes
    .venv/bin/python benchmarks/gbd.py select                # -> sets/dev_candidates.txt (+ .json)
    .venv/bin/python benchmarks/gbd.py download --set dev_candidates --max-total-mb 1000
    .venv/bin/python benchmarks/gbd.py download --set dev_candidates --smallest 10
    .venv/bin/python benchmarks/gbd.py info <hash-prefix>

What GBD offers (checked 2026-11):
  * /getdatabase/meta, /getdatabase/base: SQLite files.  meta.db: per instance hash: filename,
    family, author, track (e.g. main_2024; multi-valued), result (sat/unsat/unknown),
    proceedings, minisat1m (yes/no: solved by MiniSat within a minute).  base.db: clauses,
    variables, bytes (uncompressed size), clause-size histogram and other features.
    GBD itself has no solver runtimes for these tracks.
  * /file/<hash>: the instance as .cnf.xz (HEAD gives the compressed size);
    /getinstances?track=main_2024&context=cnf (or ?query=...): download URL list.
  * Runtimes: the SAT Competition 2022 and 2023 pages publish per-instance runtimes of all main
    track solvers (sc2022-detailed-results.zip, sc2023-detailed-results.zip, downloaded by
    fetch-meta).  2024 and 2025 have none (downloads page "tbd" / 404), so instances from those
    years are marked 'unfiltered'.

Selection (select): main tracks 2022-2025, GBD result sat/unsat, compressed size <= --max-xz-mb
(50), uncompressed <= --max-plain-mb (300, so a 2 GB memory cap is realistic).  2022/2023
instances are 'filtered': the public Kissat of that competition (kissat-sc2022-bulky,
kissat-3.1.0; 5000 s limit on the competition machines) needed --min-time..--max-time
(10-300 s) and the competition's verified result agrees with GBD.  2024/2025 instances are
'unfiltered' (minisat1m=no preferred, i.e. not trivial).  Balanced SAT/UNSAT, at most
--per-family instances per family, deterministic order (hash-based).

Files: <main>/benchmarks/cache/gbd/files/<hash>-<filename>.cnf.xz, decompressed next to it
(.cnf, system `xz`) for solvers that cannot read .xz yet.  The set lists the .cnf.xz paths;
run.py --decompress xz (its default) hands the solver the plain sibling.
"""

from __future__ import annotations

import argparse
import csv
import hashlib
import json
import re
import shutil
import sqlite3
import subprocess
import sys
import time
import urllib.error
import urllib.request
import zipfile
from pathlib import Path

BENCH = Path(__file__).resolve().parent
sys.path.insert(0, str(BENCH))

from lib import paths  # noqa: E402
from lib.sets import read_set, write_set  # noqa: E402

GBD = "https://benchmark-database.de"
SC_RESULTS = {
    # year: (zip URL, csv member, column of the reference Kissat, result column)
    "2022": ("https://satcompetition.github.io/2022/downloads/sc2022-detailed-results.zip",
             "main-seq.csv", "kissat-sc2022-bulky", "verified-result"),
    "2023": ("https://satcompetition.github.io/2023/downloads/sc2023-detailed-results.zip",
             "results_main_detailed.csv", "kissat-3.1.0", "vresult"),
}
YEARS = ("2022", "2023", "2024", "2025")
UA = {"User-Agent": "popso-sat-benchmarks/0.1 (+benchmark tooling)"}


def gbd_dir() -> Path:
    return paths.cache_dir() / "gbd"


def _get(url, dest: Path, timeout=300):
    req = urllib.request.Request(url, headers=UA)
    part = dest.with_name(dest.name + ".part")
    with urllib.request.urlopen(req, timeout=timeout) as r, open(part, "wb") as fh:
        shutil.copyfileobj(r, fh, 1 << 20)
    part.replace(dest)


def head_size(h: str) -> int | None:
    req = urllib.request.Request(f"{GBD}/file/{h}", method="HEAD", headers=UA)
    try:
        with urllib.request.urlopen(req, timeout=60) as r:
            n = r.headers.get("Content-Length")
            return int(n) if n else None
    except (urllib.error.URLError, OSError, ValueError):
        return None


# ------------------------------------------------------------------ fetch-meta

def cmd_fetch_meta(args):
    d = gbd_dir()
    d.mkdir(parents=True, exist_ok=True)
    for name in ("meta", "base"):
        f = d / f"{name}.db"
        if f.exists() and not args.refresh:
            print(f"{paths.portable(f)} exists")
            continue
        print(f"downloading {GBD}/getdatabase/{name} ...", flush=True)
        _get(f"{GBD}/getdatabase/{name}", f)
    rd = paths.cache_dir() / "sc_results"
    rd.mkdir(parents=True, exist_ok=True)
    for year, (url, member, _, _) in SC_RESULTS.items():
        out = rd / f"sc{year}" / member
        if out.exists() and not args.refresh:
            print(f"{paths.portable(out)} exists")
            continue
        z = rd / Path(url).name
        print(f"downloading {url} ...", flush=True)
        try:
            _get(url, z)
        except (urllib.error.URLError, OSError) as e:
            print(f"UNREACHABLE {url}: {e}", file=sys.stderr)
            continue
        out.parent.mkdir(parents=True, exist_ok=True)
        with zipfile.ZipFile(z) as zf:
            with zf.open(member) as src, open(out, "wb") as dst:
                shutil.copyfileobj(src, dst)
    return 0


# ------------------------------------------------------------------ select

def load_runtimes():
    """year -> {hash: (kissat time, verified result, median time over all solvers)}."""
    out = {}
    for year, (_, member, kcol, rcol) in SC_RESULTS.items():
        f = paths.cache_dir() / "sc_results" / f"sc{year}" / member
        if not f.exists():
            continue
        m = {}
        with open(f, newline="") as fh:
            rd = csv.DictReader(fh)
            solver_cols = [c for c in rd.fieldnames if c not in ("hash", "benchmark", "verified-result",
                                                                   "claimed-result", "vresult")]
            for row in rd:
                try:
                    kt = float(row[kcol])
                except (KeyError, ValueError):
                    continue
                ts = sorted(float(row[c]) for c in solver_cols if row.get(c) not in (None, ""))
                med = ts[len(ts) // 2] if ts else None
                m[row["hash"]] = (kt, (row.get(rcol) or "").strip().lower(), med)
        out[year] = m
    return out


def _order_key(h: str) -> str:
    return hashlib.sha256(("popso-sat-dev/" + h).encode()).hexdigest()


def cmd_select(args):
    d = gbd_dir()
    meta, base = d / "meta.db", d / "base.db"
    if not meta.exists():
        print("meta.db missing: run  benchmarks/gbd.py fetch-meta", file=sys.stderr)
        return 2
    db = sqlite3.connect(f"file:{meta}?mode=ro", uri=True)
    rows = db.execute(
        "select t.value, f.hash, f.result, f.family, f.author, f.minisat1m from track t "
        "join features f on f.hash = t.hash where t.value in (%s)" %
        ",".join(f"'main_{y}'" for y in YEARS)).fetchall()
    fname = dict(db.execute("select hash, value from filename"))
    plain = {}
    if base.exists():
        bdb = sqlite3.connect(f"file:{base}?mode=ro", uri=True)
        for h, b, v, c in bdb.execute("select hash, bytes, variables, clauses from features"):
            plain[h] = (b, v, c)
    rt = load_runtimes()
    sizes_f = d / "xz_sizes.json"
    sizes = json.loads(sizes_f.read_text()) if sizes_f.exists() else {}

    cands = {}
    seen = set()
    for track, h, res, fam, author, ms in sorted(rows):
        if res not in ("sat", "unsat"):
            continue
        year = track.split("_")[1]
        if h in seen:  # an instance in several main tracks: only its earliest year counts
            continue
        seen.add(h)
        pb = plain.get(h, (None, None, None))
        try:
            pmb = int(pb[0]) / 1048576.0 if pb[0] not in (None, "empty") else None
        except ValueError:
            pmb = None
        if pmb is not None and pmb > args.max_plain_mb:
            continue
        c = {"hash": h, "filename": fname.get(h, h + ".cnf.xz"), "year": year, "family": fam or "unknown",
             "author": author, "result": res, "minisat1m": ms, "plain_mb": round(pmb, 2) if pmb else None,
             "variables": pb[1], "clauses": pb[2]}
        r = rt.get(year, {}).get(h)
        if year in rt:
            if r is None:
                continue
            kt, vres, med = r
            if vres and vres in ("sat", "unsat") and vres != res:
                continue  # GBD and the competition disagree: skip
            if not (args.min_time <= kt <= args.max_time):
                continue
            c.update({"filter": "filtered", "kissat_time": kt, "median_time": med,
                      "ref_solver": SC_RESULTS[year][2]})
        else:
            if args.require_nontrivial and ms == "yes":
                continue
            c.update({"filter": "unfiltered"})
        cands[h] = c
    print(f"{len(cands)} candidates after filters "
          f"({sum(1 for c in cands.values() if c['filter'] == 'filtered')} with runtimes)")

    n_total = args.size
    n_unf = round(n_total * args.unfiltered_share)
    quotas = {("filtered", "sat"): (n_total - n_unf) // 2, ("filtered", "unsat"): (n_total - n_unf) - (n_total - n_unf) // 2,
              ("unfiltered", "sat"): n_unf // 2, ("unfiltered", "unsat"): n_unf - n_unf // 2}
    fam_count = {}
    chosen = []
    heads = 0
    order = sorted(cands.values(), key=lambda c: _order_key(c["hash"]))
    for pass_ in (0, 1):  # pass 1 tops up quotas left empty (other filter class) if needed
        for c in order:
            if c in chosen:
                continue
            key = (c["filter"], c["result"])
            if pass_ == 0 and quotas[key] <= 0:
                continue
            if pass_ == 1:
                other = ("unfiltered" if c["filter"] == "filtered" else "filtered", c["result"])
                if quotas[other] <= 0:
                    continue
                key = other
            if fam_count.get(c["family"], 0) >= args.per_family:
                continue
            if c["hash"] not in sizes:
                sizes[c["hash"]] = head_size(c["hash"])
                heads += 1
                if heads % 25 == 0:
                    sizes_f.write_text(json.dumps(sizes, indent=0))
                    print(f"  ... {heads} size requests", flush=True)
            xz = sizes[c["hash"]]
            if xz is None or xz > args.max_xz_mb * 1048576:
                continue
            c["xz_mb"] = round(xz / 1048576.0, 2)
            chosen.append(c)
            quotas[key] -= 1
            fam_count[c["family"]] = fam_count.get(c["family"], 0) + 1
            if all(v <= 0 for v in quotas.values()):
                break
    sizes_f.write_text(json.dumps(sizes, indent=0))
    chosen.sort(key=lambda c: (c["result"], c["filter"], c["year"], c["family"], c["filename"]))
    rows_out = []
    for c in chosen:
        # GBD file names may contain '#', spaces etc. (set-file comment char, shell trouble)
        safe = re.sub(r"[^A-Za-z0-9._+-]", "_", c["filename"])
        key = f"gbd/files/{c['hash']}-{safe}"
        info = [f"family={c['family']}", f"year={c['year']}", c["filter"]]
        if c["filter"] == "filtered":
            info.append(f"{c['ref_solver']}={c['kissat_time']:.0f}s")
        info.append(f"xz={c['xz_mb']}MB")
        if c.get("plain_mb"):
            info.append(f"cnf={c['plain_mb']:.1f}MB")
        rows_out.append((key, c["result"], " ".join(info)))
    nsat = sum(1 for c in chosen if c["result"] == "sat")
    nf = sum(1 for c in chosen if c["filter"] == "filtered")
    hdr = [f"dev-set CANDIDATES from GBD main tracks {YEARS[0]}-{YEARS[-1]} (benchmarks/gbd.py select): "
           f"{len(chosen)} instances, {nsat} sat / {len(chosen) - nsat} unsat, {nf} runtime-filtered",
           f"filtered = {SC_RESULTS['2022'][2]} / {SC_RESULTS['2023'][2]} needed {args.min_time:g}-{args.max_time:g} s "
           "in that SAT Competition; unfiltered = no runtime data (2024/2025): filter by a reference run",
           "files: <main>/benchmarks/cache/gbd/files (benchmarks/gbd.py download --set dev_candidates)",
           f"total xz {sum(c['xz_mb'] for c in chosen):.0f} MB; at most {args.per_family} per family"]
    write_set(paths.SETS / "dev_candidates.txt", rows_out, hdr)
    (paths.REFERENCE / "gbd_dev_candidates.json").write_text(json.dumps(
        {"generated": time.strftime("%Y-%m-%d"), "args": {k: v for k, v in vars(args).items() if k != "func"},
         "instances": chosen}, indent=1) + "\n")
    fams = sorted({c["family"] for c in chosen})
    print(f"selected {len(chosen)}: {nsat} sat, {len(chosen) - nsat} unsat, {nf} filtered, "
          f"{len(fams)} families, {sum(c['xz_mb'] for c in chosen):.0f} MB xz total "
          f"({heads} HEAD requests)")
    left = {k: v for k, v in quotas.items() if v > 0}
    if left:
        print(f"quotas not filled: {left}")
    print(f"written {paths.portable(paths.SETS / 'dev_candidates.txt')}")
    return 0


# ------------------------------------------------------------------ download

def cmd_download(args):
    entries = read_set(args.set)
    entries = [e for e in entries if e.key.startswith("gbd/files/")]
    sizes_f = gbd_dir() / "xz_sizes.json"
    sizes = json.loads(sizes_f.read_text()) if sizes_f.exists() else {}

    def h_of(e):
        return Path(e.key).name.split("-", 1)[0]

    if args.smallest:
        entries = sorted(entries, key=lambda e: sizes.get(h_of(e)) or 1 << 40)[: args.smallest]
    elif args.limit:
        entries = entries[: args.limit]
    budget = args.max_total_mb * 1048576
    total = 0
    xz = shutil.which("xz")
    failed = []
    for e in entries:
        f = e.path
        h = h_of(e)
        plain = f.with_name(f.name[:-3]) if f.name.endswith(".xz") else None
        if f.exists():
            if args.decompress and plain and not plain.exists():
                _decompress(xz, f)
            continue
        sz = sizes.get(h) or head_size(h) or 0
        if total + sz > budget:
            print(f"budget of {args.max_total_mb} MB reached; stopping before {e.key}")
            break
        f.parent.mkdir(parents=True, exist_ok=True)
        t0 = time.time()
        try:
            _get(f"{GBD}/file/{h}", f)
        except (urllib.error.URLError, OSError) as ex:
            print(f"FAILED {e.key}: {ex}", file=sys.stderr)
            failed.append(e.key)
            continue
        total += f.stat().st_size
        ok = subprocess.run([xz, "-t", str(f)], capture_output=True).returncode == 0 if xz else True
        if not ok:
            print(f"CORRUPT {e.key} (xz -t failed); removed", file=sys.stderr)
            f.unlink()
            failed.append(e.key)
            continue
        print(f"{e.key}  {f.stat().st_size / 1048576:.1f} MB  {time.time() - t0:.1f} s", flush=True)
        if args.decompress and plain:
            _decompress(xz, f)
    print(f"downloaded {total / 1048576:.1f} MB")
    return 1 if failed else 0


def _decompress(xz, f: Path):
    if not xz:
        print("no `xz` on PATH: not decompressing", file=sys.stderr)
        return
    plain = f.with_name(f.name[:-3])
    r = subprocess.run([xz, "-dkf", str(f)], capture_output=True, text=True)
    if r.returncode != 0:
        print(f"xz -d failed for {f.name}: {r.stderr.strip()}", file=sys.stderr)
        plain.unlink(missing_ok=True)


def cmd_info(args):
    db = sqlite3.connect(f"file:{gbd_dir() / 'meta.db'}?mode=ro", uri=True)
    db.row_factory = sqlite3.Row
    for r in db.execute("select * from features where hash like ?", (args.hash + "%",)):
        d = dict(r)
        d["track"] = [t for (t,) in db.execute("select value from track where hash=?", (d["hash"],))]
        d["filename"] = [t for (t,) in db.execute("select value from filename where hash=?", (d["hash"],))]
        d.pop("local", None)
        print(json.dumps(d, indent=1))
    return 0


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = ap.add_subparsers(dest="cmd", required=True)
    p = sub.add_parser("fetch-meta", help="download meta.db, base.db and the SC 2022/2023 runtimes")
    p.add_argument("--refresh", action="store_true")
    p.set_defaults(func=cmd_fetch_meta)
    p = sub.add_parser("select", help="write sets/dev_candidates.txt")
    p.add_argument("--size", type=int, default=120)
    p.add_argument("--unfiltered-share", type=float, default=0.3, help="share of 2024/2025 (no runtimes)")
    p.add_argument("--per-family", type=int, default=4)
    p.add_argument("--min-time", type=float, default=10.0)
    p.add_argument("--max-time", type=float, default=300.0)
    p.add_argument("--max-xz-mb", type=float, default=50.0)
    p.add_argument("--max-plain-mb", type=float, default=300.0)
    p.add_argument("--require-nontrivial", action=argparse.BooleanOptionalAction, default=True,
                   help="unfiltered: skip minisat1m=yes instances (default on)")
    p.set_defaults(func=cmd_select)
    p = sub.add_parser("download", help="download the GBD files of a set into the cache")
    p.add_argument("--set", default="dev_candidates")
    p.add_argument("--max-total-mb", type=float, default=1000.0, help="download budget (default 1000 MB)")
    p.add_argument("--limit", type=int, help="first N entries of the set")
    p.add_argument("--smallest", type=int, help="the N smallest entries (testing)")
    p.add_argument("--decompress", action=argparse.BooleanOptionalAction, default=True,
                   help="also write the decompressed .cnf next to the .cnf.xz (system xz; default on)")
    p.set_defaults(func=cmd_download)
    p = sub.add_parser("info", help="GBD metadata of an instance")
    p.add_argument("hash")
    p.set_defaults(func=cmd_info)
    args = ap.parse_args(argv)
    return args.func(args)


if __name__ == "__main__":
    sys.exit(main())
