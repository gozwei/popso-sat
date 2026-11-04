#!/usr/bin/env python3
"""Download SATLIB benchmark archives into the cache and write the SATLIB set files.

    .venv/bin/python benchmarks/satlib.py                  # all groups below (~25 MB)
    .venv/bin/python benchmarks/satlib.py --groups gate    # only what sets/gate.txt needs
    .venv/bin/python benchmarks/satlib.py --groups uf50-218,uuf50-218,flat30-60
    .venv/bin/python benchmarks/satlib.py --write-sets     # (re)write sets/satlib_*.txt

Files land in <main>/benchmarks/cache/satlib/<group>/<file>.cnf (archives in satlib/_archives).
Source: SATLIB, https://www.cs.ubc.ca/~hoos/SATLIB/benchm.html (H. Hoos, T. Stuetzle).  The
expected status comes from the SATLIB descriptions ("all satisfiable" etc.), from the file
names (AIM: yes/no) or, where SATLIB gives none (QG, BMC, JNH, Beijing), from a reference
solve (benchmarks/reference.py -> reference/status.json); such entries are 'unknown' in the
set files.
"""

from __future__ import annotations

import argparse
import shutil
import sys
import tarfile
import time
import urllib.error
import urllib.request
from pathlib import Path

BENCH = Path(__file__).resolve().parent
sys.path.insert(0, str(BENCH))

from lib import paths  # noqa: E402
from lib.dimacs import CnfStream, write_cnf  # noqa: E402
from lib.sets import read_set, write_set  # noqa: E402

BASE = "https://www.cs.ubc.ca/~hoos/SATLIB/Benchmarks/SAT/"

# group -> (archive path below BASE, status rule)
#   rule: 'sat' / 'unsat' / 'aim' (yes/no in the name) / 'ssa' (by file) / None (reference solve)
GROUPS = {}
for _n, _m in ((20, 91), (50, 218), (75, 325), (100, 430), (125, 538), (150, 645), (175, 753),
               (200, 860), (225, 960), (250, 1065)):
    GROUPS[f"uf{_n}-{_m}"] = (f"RND3SAT/uf{_n}-{_m}.tar.gz", "sat")
    if _n != 20:
        GROUPS[f"uuf{_n}-{_m}"] = (f"RND3SAT/uuf{_n}-{_m}.tar.gz", "unsat")
for _g in ("flat30-60", "flat50-115", "flat75-180", "flat100-239", "flat125-301", "flat150-360",
           "flat175-417", "flat200-479"):
    GROUPS[_g] = (f"GCP/{_g}.tar.gz", "sat")
GROUPS.update({
    "sw100-8-lp0-c5": ("SW-GCP/sw100-8-lp0-c5.tar.gz", "sat"),
    "blocksworld": ("PLANNING/BlocksWorld/blocksworld.tar.gz", "sat"),
    "logistics": ("PLANNING/Logistics/logistics.tar.gz", "sat"),
    "ais": ("AIS/ais.tar.gz", "sat"),
    "qg": ("QG/QG.tar.gz", None),
    "bmc": ("BMC/bmc.tar.gz", None),
    "aim": ("DIMACS/AIM/aim.tar.gz", "aim"),
    "lran": ("DIMACS/LRAN/f.tar.gz", "sat"),
    "jnh": ("DIMACS/JNH/jnh.tar.gz", None),
    "dubois": ("DIMACS/DUBOIS/dubois.tar.gz", "unsat"),
    "gcp-large": ("DIMACS/GCP/gcp-large.tar.gz", "sat"),
    "parity": ("DIMACS/PARITY/parity.tar.gz", "sat"),
    "ii": ("DIMACS/II/inductive-inference.tar.gz", "sat"),
    "hanoi": ("DIMACS/HANOI/hanoi.tar.gz", "sat"),
    "bf": ("DIMACS/BF/bf.tar.gz", "unsat"),
    "ssa": ("DIMACS/SSA/ssa.tar.gz", "ssa"),
    "pigeon-hole": ("DIMACS/PHOLE/pigeon-hole.tar.gz", "unsat"),
    "pret": ("DIMACS/PRET/pret.tar.gz", "unsat"),
    "beijing": ("Bejing/Bejing.tar.gz", None),
})
# groups whose files get normalize()d after extraction (quirks found by scanning all files)
NORMALIZE = {"pret": True, "dubois": True}
# SATLIB SSA description: ssa7552-* satisfiable, the others unsatisfiable
SSA_SAT_PREFIX = "ssa7552"
RANDOM = [g for g in GROUPS if g.startswith(("uf", "uuf"))]
STRUCTURED = [g for g in GROUPS if g not in RANDOM]


def status_of(group: str, fname: str):
    rule = GROUPS[group][1]
    if rule in ("sat", "unsat"):
        return rule
    if rule == "aim":
        return "sat" if "-yes" in fname else ("unsat" if "-no" in fname else None)
    if rule == "ssa":
        return "sat" if fname.startswith(SSA_SAT_PREFIX) else "unsat"
    return None


def _safe_members(tf: tarfile.TarFile):
    for m in tf.getmembers():
        name = m.name
        if name.startswith("/") or ".." in Path(name).parts or not (m.isfile() or m.isdir()):
            continue
        yield m


def fetch(group: str, root: Path, log) -> bool:
    rel, _ = GROUPS[group]
    arch_dir = root / "_archives"
    arch_dir.mkdir(parents=True, exist_ok=True)
    arch = arch_dir / Path(rel).name
    dest = root / group
    if dest.exists() and any(dest.glob("*.cnf")):
        return True
    if not arch.exists():
        url = BASE + rel
        try:
            with urllib.request.urlopen(url, timeout=60) as r, open(arch.with_suffix(".part"), "wb") as fh:
                shutil.copyfileobj(r, fh)
            arch.with_suffix(".part").replace(arch)
        except (urllib.error.URLError, OSError, TimeoutError) as e:
            log(f"UNREACHABLE {group}: {url}: {e}")
            return False
    tmp = root / f"_extract_{group}"
    shutil.rmtree(tmp, ignore_errors=True)
    tmp.mkdir()
    try:
        with tarfile.open(arch, "r:*") as tf:
            members = list(_safe_members(tf))
            if sys.version_info >= (3, 12):
                tf.extractall(tmp, members=members, filter="data")
            else:
                tf.extractall(tmp, members=members)
    except (tarfile.TarError, OSError, EOFError) as e:
        log(f"BAD ARCHIVE {group}: {e}")
        shutil.rmtree(tmp, ignore_errors=True)
        return False
    dest.mkdir(parents=True, exist_ok=True)
    n = 0
    for f in sorted(tmp.rglob("*")):
        if f.is_file() and (f.name.endswith(".cnf") or f.suffix == ""):
            if f.suffix == "" and not _looks_like_cnf(f):
                continue
            target = dest / (f.name if f.name.endswith(".cnf") else f.name + ".cnf")
            shutil.move(str(f), target)
            if NORMALIZE.get(group):
                normalize(target, log)
            n += 1
    shutil.rmtree(tmp, ignore_errors=True)
    log(f"{group}: {n} files")
    return n > 0


def normalize(f: Path, log) -> bool:
    """Fix two quirks of SATLIB files (the archives in _archives stay untouched):
    * a stray '0' line after the last clause (all pret*: 'p cnf 60 160' + 161st, empty clause),
      which would make the formula trivially UNSAT -> trailing empty clauses beyond the header's
      count are dropped;
    * a header that declares more clauses than the file has (dubois100: 800 vs 598) -> the
      header count is corrected.
    Returns True if the file was rewritten."""
    s = CnfStream(f)
    s.keep_comments = 10 ** 6
    clauses = list(s)
    n = s.nclauses or 0
    fixed = []
    while len(clauses) > n and clauses and not clauses[-1]:
        clauses.pop()
        fixed.append("dropped a trailing empty clause")
    if len(clauses) < n:
        fixed.append(f"header clause count {n} -> {len(clauses)}")
    if not fixed:
        return False
    comments = s.comments + [f"popso-sat benchmarks/satlib.py: {'; '.join(sorted(set(fixed)))}"]
    write_cnf(f, max(s.nvars or 0, s.max_var), clauses, comments)
    log(f"normalized {f.parent.name}/{f.name}: {'; '.join(sorted(set(fixed)))}")
    return True


def _looks_like_cnf(f: Path) -> bool:
    try:
        with open(f, "rb") as fh:
            head = fh.read(4096)
    except OSError:
        return False
    return b"p cnf" in head


PER_GROUP_COMMITTED = 20   # uf/uuf: first 20 files per group in sets/satlib_random.txt
PER_FLAT_COMMITTED = 10    # flat*/sw*: first 10 per group in sets/satlib_structured.txt


def write_sets(root: Path):
    """Committed sets (subsets, sets/satlib_*.txt) and full lists in the cache
    (<cache>/satlib/all_random.txt, all_structured.txt; usable as --set <file>)."""

    def rows(groups, limit=None):
        out = []
        for g in groups:
            d = root / g
            files = sorted(d.glob("*.cnf"), key=lambda p: _natural(p.name)) if d.exists() else []
            lim = limit(g) if limit else None
            for f in files[:lim]:
                st = status_of(g, f.name)
                src = "SATLIB description" if GROUPS[g][1] in ("sat", "unsat", "ssa") else (
                    "file name" if GROUPS[g][1] == "aim" else "reference solve needed")
                out.append((f"satlib/{g}/{f.name}", st, f"family={g} {src}"))
        return out

    hdr = ["SATLIB (https://www.cs.ubc.ca/~hoos/SATLIB/benchm.html); files in <main>/benchmarks/cache/satlib",
           "download: benchmarks/satlib.py; 'unknown' = status from benchmarks/reference/status.json"]
    r_rand = rows(RANDOM, lambda g: PER_GROUP_COMMITTED)
    r_struct = rows(STRUCTURED, lambda g: PER_FLAT_COMMITTED if g.startswith(("flat", "sw")) else None)
    write_set(paths.SETS / "satlib_random.txt", r_rand,
              [f"uniform random 3-SAT uf (SAT) / uuf (UNSAT), first {PER_GROUP_COMMITTED} per group"] + hdr
              + ["all files: --set <main>/benchmarks/cache/satlib/all_random.txt"])
    write_set(paths.SETS / "satlib_structured.txt", r_struct,
              [f"structured SATLIB families (flat*/sw*: first {PER_FLAT_COMMITTED} per group)"] + hdr
              + ["all files: --set <main>/benchmarks/cache/satlib/all_structured.txt"])
    (paths.SETS / "satlib.txt").write_text("# SATLIB subsets\n@include satlib_random\n@include satlib_structured\n")
    a_rand, a_struct = rows(RANDOM), rows(STRUCTURED)
    write_set(root / "all_random.txt", a_rand, ["all SATLIB uf/uuf files"] + hdr)
    write_set(root / "all_structured.txt", a_struct, ["all structured SATLIB files"] + hdr)
    print(f"sets: satlib_random {len(r_rand)}, satlib_structured {len(r_struct)} instances "
          f"(cache lists: {len(a_rand)} random, {len(a_struct)} structured)")


def _natural(s):
    import re
    return [int(t) if t.isdigit() else t for t in re.split(r"(\d+)", s)]


def gate_groups():
    try:
        es = read_set("gate")
    except FileNotFoundError:
        return []
    return sorted({Path(e.key).parts[1] for e in es if e.key.startswith("satlib/")})


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--groups", default="all", help="comma list of groups, 'all', 'random', 'structured' or 'gate'")
    ap.add_argument("--write-sets", action="store_true", help="only rewrite sets/satlib_*.txt from the cache")
    ap.add_argument("--list", action="store_true", help="list the known groups")
    ap.add_argument("--normalize", action="store_true",
                    help="only re-apply the quirk fixes to already extracted files")
    args = ap.parse_args(argv)
    root = paths.cache_dir() / "satlib"
    if args.list:
        for g, (rel, rule) in GROUPS.items():
            print(f"{g:<18} {rule or 'reference':<10} {rel}")
        return 0
    if args.write_sets:
        write_sets(root)
        return 0
    if args.normalize:
        for g in NORMALIZE:
            for f in sorted((root / g).glob("*.cnf")):
                normalize(f, print)
        return 0
    sel = args.groups
    groups = (list(GROUPS) if sel == "all" else RANDOM if sel == "random" else STRUCTURED if sel == "structured"
              else gate_groups() if sel == "gate" else [g for g in sel.split(",") if g])
    unknown = [g for g in groups if g not in GROUPS]
    if unknown:
        ap.error(f"unknown group(s) {unknown}; see --list")
    root.mkdir(parents=True, exist_ok=True)
    logf = root / "download.log"
    failed = []

    def log(msg):
        print(msg, flush=True)
        with open(logf, "a") as fh:
            fh.write(time.strftime("%Y-%m-%d %H:%M:%S ") + msg + "\n")

    for g in groups:
        if not fetch(g, root, log):
            failed.append(g)
    if sel == "all":
        write_sets(root)
    if failed:
        print(f"failed: {failed} (see {paths.portable(logf)})", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
