#!/usr/bin/env python3
"""Benchmark runner for popso-sat (or any SAT Competition-format solver).

Runs   <solver> [--time-limit=T] [--mem-limit=M] [--seed=S] [extra] [--proof=<tmp>] <input>
on every selected instance and checks every answer independently:
  * SAT:   the 'v' model is verified against the original formula (every clause satisfied,
           no variable assigned both ways);
  * UNSAT: the DRAT proof is checked with drat-trim when <main>/benchmarks/tools/build/bin/
           drat-trim exists, otherwise with the pure-Python pydrat (benchmarks/tools/pydrat.py)
           for proofs up to --pydrat-max-mb; larger proofs are 'unchecked'.  The checker has its
           own time limit; a checker timeout is 'proof-timeout', not WRONG; a rejected proof is;
  * both:  the answer is compared with the expected status (set file, then
           benchmarks/reference/status.json); a contradiction is WRONG.
Each run is classified ok / unsolved (time limit, unknown) / memlimit / error / WRONG.

    .venv/bin/python benchmarks/run.py --set gate -j 2 --strict
    .venv/bin/python benchmarks/run.py --solver build/popso-sat --set small -t 30 --tag base
    .venv/bin/python benchmarks/run.py --solver "benchmarks/tools/pysat_cli.py --solver cadical195" --set gate
    .venv/bin/python benchmarks/run.py --solver pysat:kissat404 --set medium -t 60 --no-proof
    .venv/bin/python benchmarks/run.py --solver path/to/kissat --time-arg='--time={}' --mem-arg='' \\
        --proof-arg='{}' --set dev -t 300          # a competition binary (proof = 2nd argument)

Results: benchmarks/results/<timestamp>_<git-sha>[_tag].json and .csv; while running, every
finished instance is appended to the .jsonl of the same name (removed once the .json is
written), so an interrupted run can be continued with  --resume <that .jsonl>  (same options).
Exit code 1 on any WRONG answer; with --strict also on errors and on unchecked proofs (unless
--allow-unchecked), with --require-solved also on unsolved/memlimit runs.
"""

from __future__ import annotations

import argparse
import csv
import datetime as dt
import glob
import hashlib
import json
import math
import os
import platform
import re
import shlex
import shutil
import signal
import subprocess
import sys
import tempfile
import threading
import time
from concurrent.futures import ThreadPoolExecutor, as_completed
from pathlib import Path

BENCH = Path(__file__).resolve().parent
sys.path.insert(0, str(BENCH))

from lib import drat, paths  # noqa: E402
from lib.dimacs import COMPRESSED, instance_name, open_binary  # noqa: E402
from lib.output import SAT, UNKNOWN, UNSAT, parse_output  # noqa: E402
from lib.proc import kill_all, run_capped  # noqa: E402
from lib.sets import Entry, load_reference, read_set  # noqa: E402
from lib.verify import verify_model  # noqa: E402

REPO = paths.REPO

# result classes
OK = "ok"              # answer verified (SAT: model checked; UNSAT: proof verified or unchecked)
UNSOLVED = "unsolved"  # time limit / 's UNKNOWN' / answer after the time limit
MEMLIMIT = "memlimit"  # killed above the memory cap, or the solver reported running out of memory
ERROR = "error"        # crash, bad exit code, garbled output, time limit not respected
WRONG = "WRONG"        # model fails verification, rejected proof, or status contradicts expected
CLASSES = (OK, UNSOLVED, MEMLIMIT, ERROR, WRONG)
# proof states that count as "unchecked" for --strict
UNCHECKED_PROOF = (drat.UNCHECKED, drat.TIMEOUT, drat.MEMLIMIT, drat.ERROR, drat.MISSING)

RESUME_KEYS = ("time_limit", "mem_limit_mb", "seed", "extra", "proof", "solver")
SGM_SHIFT = 10.0


# ------------------------------------------------------------------ helpers

def sgm(times, shift=SGM_SHIFT):
    if not times:
        return None
    return math.exp(sum(math.log(t + shift) for t in times) / len(times)) - shift


def git_sha():
    try:
        sha = subprocess.run(["git", "rev-parse", "--short", "HEAD"], cwd=REPO, capture_output=True,
                             text=True, timeout=10).stdout.strip() or "nogit"
        dirty = subprocess.run(["git", "diff", "--quiet", "HEAD", "--", "src", "apps", "CMakeLists.txt"],
                               cwd=REPO, timeout=10).returncode != 0
        return sha + ("-dirty" if dirty else "")
    except (OSError, subprocess.SubprocessError):
        return "nogit"


def resolve_solver(spec: str) -> list[str]:
    """--solver value -> argv.  Accepted: a binary path; a quoted command line; 'pysat:<name>'
    (the PySAT stand-in); a bare name found in <main>/benchmarks/tools/build/bin; a .py script
    (run with this interpreter)."""
    if spec.startswith("pysat:"):
        return [sys.executable, str(BENCH / "tools" / "pysat_cli.py"), f"--solver={spec[6:]}"]
    cmd = [spec] if os.path.exists(spec) else shlex.split(spec)
    exe = cmd[0]
    if not os.path.exists(exe) and "/" not in exe:
        cand = paths.tools_bin() / exe
        if cand.exists():
            cmd[0] = str(cand)
        elif exe == "popso-sat":
            cmd[0] = str(paths.default_solver())
    elif not os.path.isabs(exe) and not os.path.exists(exe) and (REPO / exe).exists():
        cmd[0] = str(REPO / exe)
    if cmd[0].endswith(".py"):
        cmd = [sys.executable] + cmd
    return cmd


def solver_fingerprint(cmd):
    """sha256 prefix of the solver binary (or script), to tie results to a build."""
    for a in (cmd[1:] if cmd[0] == sys.executable else cmd):
        if os.path.isfile(a):
            h = hashlib.sha256()
            with open(a, "rb") as fh:
                for b in iter(lambda: fh.read(1 << 20), b""):
                    h.update(b)
            return h.hexdigest()[:16]
    return None


def family_of(e: Entry) -> str:
    m = re.search(r"family=(\S+)", e.comment or "")
    if m:
        return m.group(1)
    parts = Path(e.key).parts
    if parts[:2] == ("benchmarks", "instances") or parts[:1] == ("generated",):
        return instance_name(e.key).split("_")[0]
    if parts[:1] == ("satlib",) and len(parts) > 2:
        return parts[1]
    return instance_name(e.key).split("_")[0].split("-")[0]


def expand_positional(patterns) -> list[Entry]:
    out = []
    for pat in patterns:
        pp = Path(pat)
        if pp.is_dir():
            files = sorted(f for f in pp.rglob("*") if f.is_file() and
                           re.search(r"\.(cnf|dimacs)(\.(gz|xz|bz2|lzma))?$", f.name))
        else:
            files = [Path(f) for f in sorted(glob.glob(pat))] or [pp]
        for f in files:
            out.append(Entry(key=paths.portable(f), path=f.resolve() if f.exists() else f, expected=None))
    return out


def plain_input(path: Path, mode: str, tmpdir: Path):
    """(file to give the solver, temp file to delete or None).  mode: none / xz / all."""
    name = path.name
    comp = next((c for c in COMPRESSED if name.endswith(c)), None)
    if comp is None or mode == "none" or (mode == "xz" and comp not in (".xz", ".lzma")):
        return path, None
    sib = path.with_name(name[: -len(comp)])
    if sib.exists():
        return sib, None
    out = tmpdir / sib.name
    with open_binary(path) as src, open(out, "wb") as dst:
        shutil.copyfileobj(src, dst, 1 << 22)
    return out, out


def fmt_arg(template: str, value) -> list[str]:
    if not template or value is None:
        return []
    return shlex.split(template.replace("{}", str(value)))


# ------------------------------------------------------------------ one run

def run_one(e: Entry, expected, args, solver_cmd, tmproot: Path, keep_dir: Path | None):
    tmpdir = Path(tempfile.mkdtemp(prefix="run-", dir=tmproot))
    rec = {"instance": e.key, "name": instance_name(e.key), "family": family_of(e),
           "expected": expected, "status": None, "class": None, "message": "", "time": None,
           "cpu": None, "peak_rss_mb": None, "returncode": None, "proof": None, "proof_time": None,
           "proof_mb": None}
    try:
        return _run_one(e, expected, args, solver_cmd, tmpdir, rec, keep_dir)
    except Exception as ex:  # noqa: BLE001 - a harness bug must not lose the other results
        rec.update({"class": ERROR, "message": f"harness exception: {type(ex).__name__}: {ex}"})
        return rec
    finally:
        shutil.rmtree(tmpdir, ignore_errors=True)


def _run_one(e, expected, args, solver_cmd, tmpdir, rec, keep_dir):
    t = args.time_limit
    try:
        inp, _ = plain_input(e.path, args.decompress, tmpdir)
    except (OSError, EOFError, ValueError) as ex:
        rec.update({"class": ERROR, "message": f"cannot decompress input: {ex}"})
        return rec
    proof_file = tmpdir / "proof.drat"
    cmd = list(solver_cmd)
    cmd += fmt_arg(args.time_arg, f"{t:g}")
    if args.mem_limit:
        cmd += fmt_arg(args.mem_arg, args.mem_limit)
    cmd += fmt_arg(args.seed_arg, args.seed)
    cmd += shlex.split(args.extra) if args.extra else []
    positional_proof = args.proof and args.proof_arg.strip() == "{}"
    if args.proof and not positional_proof:
        cmd += fmt_arg(args.proof_arg, proof_file)
    cmd.append(str(inp))
    if positional_proof:
        cmd.append(str(proof_file))
    told_time = bool(args.time_arg)
    told_mem = bool(args.mem_arg) and bool(args.mem_limit)
    grace = args.grace if args.grace is not None else max(5.0, 0.1 * t)
    timeout = t + grace if told_time else t
    cap = (args.mem_limit * 1.25 if told_mem else args.mem_limit) or None
    out_path, err_path = tmpdir / "stdout", tmpdir / "stderr"
    with open(out_path, "wb") as so, open(err_path, "wb") as se:
        r = run_capped(cmd, timeout, cap, stdout=so, stderr=se)
    rec.update({"time": round(r.wall, 4), "cpu": round(r.cpu, 4), "peak_rss_mb": round(r.peak_rss_mb, 1),
                "returncode": r.returncode})
    with open(out_path, "rb") as fh:
        out = parse_output(fh)
    err_tail = err_path.read_bytes()[-600:].decode("utf-8", "replace").strip()
    if out.memory_hint is False and re.search(r"(out of memory|bad_alloc|MemoryError|cannot allocate)",
                                               err_tail, re.I):
        out.memory_hint = True
    rec["status"] = out.status

    def finish(cls, msg):
        rec["class"], rec["message"] = cls, msg
        if keep_dir is not None and cls in (WRONG, ERROR):
            d = keep_dir / re.sub(r"[^A-Za-z0-9_.-]+", "_", e.key)
            d.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(out_path, d / "stdout")
            shutil.copyfile(err_path, d / "stderr")
            (d / "command.txt").write_text(paths.strip_local(shlex.join(cmd)).replace(str(tmpdir), "<tmp>") + "\n")
        return rec

    # killed by the runner
    if r.reason == "memlimit":
        return finish(MEMLIMIT, f"killed: RSS above {cap:.0f} MB")
    if r.reason == "timeout":
        if told_time:
            return finish(ERROR, f"killed after {r.wall:.1f} s (time limit {t:g} s not respected)")
        return finish(UNSOLVED, f"killed at the time limit ({t:g} s)")

    notes = []
    exp_rc = {SAT: 10, UNSAT: 20, UNKNOWN: 0}.get(out.status)
    bad_rc = exp_rc is not None and r.returncode != exp_rc
    if out.errors:
        notes.append("output: " + "; ".join(out.errors[:3]))

    if out.status == SAT:
        if not out.model_terminated:
            if expected == "unsat":
                return finish(WRONG, "claimed SAT (no usable model) but expected UNSAT")
            return finish(ERROR, "claimed SAT without a complete 'v ... 0' model")
        tv = time.perf_counter()
        v = verify_model(inp, out.model)
        rec["verify_time"] = round(time.perf_counter() - tv, 3)
        rec["model_missing"] = v.missing
        if v.formula_error:
            return finish(ERROR, f"verifier cannot read the formula: {v.formula_error}")
        if not v.ok:
            return finish(WRONG, f"model INVALID: {v.message}")
        if v.message:
            notes.append("model: " + v.message)
        if expected == "unsat":
            return finish(WRONG, "verified model, but the expected status is UNSAT (reference wrong?)")
        if out.errors or bad_rc:
            return finish(ERROR, "; ".join(notes + ([f"exit code {r.returncode} != 10"] if bad_rc else [])))
        if r.wall > t:
            return finish(UNSOLVED, f"correct SAT answer after the time limit ({r.wall:.1f} s)")
        return finish(OK, "; ".join(notes))

    if out.status == UNSAT:
        if expected == "sat":
            return finish(WRONG, "claimed UNSAT but the instance is SAT")
        if args.proof:
            if args.checker_obj:
                pt = args.proof_time_limit if args.proof_time_limit is not None else 2 * t + 30
                if proof_file.exists():
                    rec["proof_mb"] = round(proof_file.stat().st_size / 1048576.0, 3)
                ps, pmsg, ptime = drat.check_proof(args.checker_obj, inp, proof_file, pt,
                                                   args.mem_limit or None, tmpdir)
                rec["proof"], rec["proof_time"] = ps, round(ptime, 3)
                rec["proof_checker"] = args.checker_obj.name
                if ps == drat.REJECTED:
                    return finish(WRONG, f"proof REJECTED: {pmsg}")
                if ps != drat.VERIFIED:
                    notes.append(f"proof {ps}" + (f": {pmsg}" if pmsg else ""))
            else:
                rec["proof"] = drat.MISSING if not proof_file.exists() else drat.UNCHECKED
                if proof_file.exists():
                    rec["proof_mb"] = round(proof_file.stat().st_size / 1048576.0, 3)
        else:
            rec["proof"] = "off"
        if out.errors or bad_rc:
            return finish(ERROR, "; ".join(notes + ([f"exit code {r.returncode} != 20"] if bad_rc else [])))
        if r.wall > t:
            return finish(UNSOLVED, f"UNSAT answer after the time limit ({r.wall:.1f} s)")
        return finish(OK, "; ".join(notes))

    # no definite answer
    if out.status == UNKNOWN and not bad_rc and not out.errors:
        if out.memory_hint:
            return finish(MEMLIMIT, "s UNKNOWN (memory limit reported)")
        return finish(UNSOLVED, "s UNKNOWN")
    if out.memory_hint or (r.returncode is not None and r.returncode < 0 and cap and r.peak_rss_mb > 0.9 * cap):
        return finish(MEMLIMIT, f"exit code {r.returncode}, out of memory" + (f"; {err_tail[-200:]}" if err_tail else ""))
    msg = "no 's' line" if out.status is None else f"status {out.status}"
    msg += f", exit code {r.returncode}"
    if r.returncode is not None and r.returncode < 0:
        msg += f" (signal {-r.returncode})"
    if err_tail:
        msg += f"; stderr: {err_tail[-200:]}"
    return finish(ERROR, "; ".join([msg] + notes))


# ------------------------------------------------------------------ resume / summary

def load_partial(path: Path):
    if path.suffix == ".json":
        d = json.loads(path.read_text())
        return d["meta"], d["results"]
    meta, recs = None, []
    for ln in path.read_text().splitlines():
        try:
            d = json.loads(ln)
        except json.JSONDecodeError:
            continue  # torn last line after a crash
        if "meta" in d:
            meta = d["meta"]
        elif "result" in d:
            recs.append(d["result"])
    if meta is None:
        raise ValueError(f"{path.name}: no meta line")
    return meta, recs


def summarize(recs, t):
    by = {c: 0 for c in CLASSES}
    for r in recs:
        by[r["class"]] = by.get(r["class"], 0) + 1
    solved = [r for r in recs if r["class"] == OK]
    eff = [min(r["time"], t) if r["class"] == OK else t for r in recs]
    par2 = (sum(r["time"] if r["class"] == OK else 2 * t for r in recs) / len(recs)) if recs else None
    proofs = {}
    for r in recs:
        if r.get("proof") and r["class"] == OK:
            proofs[r["proof"]] = proofs.get(r["proof"], 0) + 1
    return {
        "instances": len(recs),
        "solved": len(solved),
        "solved_sat": sum(1 for r in solved if r["status"] == SAT),
        "solved_unsat": sum(1 for r in solved if r["status"] == UNSAT),
        "classes": by,
        "wrong": by.get(WRONG, 0),
        "errors": by.get(ERROR, 0),
        "par2": par2,
        "sgm_time": sgm(eff),
        "sgm_shift": SGM_SHIFT,
        "time_limit": t,
        "proofs": proofs,
        "unchecked_proofs": sum(v for k, v in proofs.items() if k in UNCHECKED_PROOF),
    }


class _Terminated(BaseException):
    """SIGTERM; a BaseException so that run_one's harness-error handler does not swallow it."""


def _on_sigterm(signum, frame):
    raise _Terminated()


# ------------------------------------------------------------------ main

def main(argv=None):
    argv = sys.argv[1:] if argv is None else argv
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("instances", nargs="*", help="instance files, globs or directories (besides --set)")
    ap.add_argument("--solver", default=str(paths.default_solver()),
                    help="solver binary, quoted command line, 'pysat:<name>' or a name in "
                         "<main>/benchmarks/tools/build/bin (default: <repo>/build/popso-sat)")
    ap.add_argument("--set", action="append", default=[],
                    help="instance list: a name in benchmarks/sets/ or a file (repeatable)")
    ap.add_argument("-t", "--time-limit", type=float, default=60.0, help="seconds per instance (default 60)")
    ap.add_argument("-j", "--jobs", type=int, default=1,
                    help="instances run concurrently (default 1; shared machine: at most 2)")
    ap.add_argument("--mem-limit", type=int, default=2048,
                    help="MB per solver process (default 2048; 0 = none): passed to the solver via "
                         "--mem-arg and enforced by an RSS watchdog at 125%% (100%% if not passed)")
    ap.add_argument("--seed", type=int, help="passed to the solver via --seed-arg")
    ap.add_argument("--extra", default="", help="extra solver arguments, e.g. --extra='--deterministic' (the = form)")
    ap.add_argument("--tag", default="", help="label appended to the result file names")
    ap.add_argument("--no-save", action="store_true", help="do not write result files")
    ap.add_argument("--resume", metavar="FILE", help="continue an interrupted run (its .jsonl, or a .json)")
    ap.add_argument("--redo", default="", help="with --resume: classes to run again, e.g. error,memlimit")
    ap.add_argument("--strict", action="store_true",
                    help="exit 1 also on errors and on unchecked UNSAT proofs (see --allow-unchecked)")
    ap.add_argument("--allow-unchecked", action="store_true",
                    help="with --strict: unchecked proofs (no drat-trim, checker timeout, ...) are fine")
    ap.add_argument("--require-solved", action="store_true", help="exit 1 also if any instance is unsolved")
    pg = ap.add_mutually_exclusive_group()
    pg.add_argument("--proof", dest="proof", action="store_true", default=True,
                    help="ask for a DRAT proof and check UNSAT answers (default)")
    pg.add_argument("--no-proof", dest="proof", action="store_false", help="no proofs")
    ap.add_argument("--checker", default="auto",
                    help="DRAT checker: auto (default: drat-trim from <main>/benchmarks/tools/build/bin if "
                         "built, else pydrat for small proofs), drat-trim, pydrat, none, or a binary path")
    ap.add_argument("--pydrat-max-mb", type=float, default=10.0,
                    help="largest proof (MB) checked with the pure-Python pydrat (default 10)")
    ap.add_argument("--proof-time-limit", type=float, help="checker time limit (default 2*T + 30 s)")
    ap.add_argument("--time-arg", default="--time-limit={}", help="solver time-limit argument template ('' = none)")
    ap.add_argument("--mem-arg", default="--mem-limit={}", help="solver memory-limit argument template ('' = none)")
    ap.add_argument("--seed-arg", default="--seed={}", help="solver seed argument template")
    ap.add_argument("--proof-arg", default="--proof={}",
                    help="proof argument template; '{}' alone = proof file as the 2nd positional argument")
    ap.add_argument("--grace", type=float, help="seconds after the time limit before the solver is killed "
                    "(default max(5, 0.1*T))")
    ap.add_argument("--decompress", choices=("none", "xz", "all"), default="xz",
                    help="give the solver a decompressed input for these compressed files (default xz, "
                         "until popso-sat reads .xz; uses an existing plain sibling file if present)")
    ap.add_argument("--reference", default=str(paths.REFERENCE / "status.json"),
                    help="reference status file (expected status when the set file has none)")
    ap.add_argument("--filter", help="regex: run only instances whose key matches")
    ap.add_argument("--exclude", help="regex: skip instances whose key matches")
    ap.add_argument("--skip-missing", action="store_true", help="skip set entries whose file is missing")
    ap.add_argument("--list", action="store_true", help="list the selected instances and exit")
    ap.add_argument("--out-dir", default=str(paths.results_dir()))
    ap.add_argument("--keep-logs", action="store_true",
                    help="keep stdout/stderr of WRONG/error runs next to the results (<base>.logs/)")
    args = ap.parse_args(argv)

    try:
        args.checker_obj = drat.resolve_checker(args.checker if args.proof else None, args.pydrat_max_mb)
    except FileNotFoundError as ex:
        print(str(ex), file=sys.stderr)
        return 2

    # ---- instance selection
    entries: list[Entry] = []
    try:
        for s in args.set:
            entries += read_set(s)
    except (FileNotFoundError, ValueError) as ex:
        print(str(ex), file=sys.stderr)
        return 2
    entries += expand_positional(args.instances)
    if not args.set and not args.instances:
        print("nothing to run: give --set and/or instance files", file=sys.stderr)
        return 2
    seen, uniq = set(), []
    for e in entries:
        if e.key not in seen:
            seen.add(e.key)
            uniq.append(e)
    entries = uniq
    if args.filter:
        entries = [e for e in entries if re.search(args.filter, e.key)]
    if args.exclude:
        entries = [e for e in entries if not re.search(args.exclude, e.key)]
    missing = [e for e in entries if not e.path.exists()]
    if missing and not args.list:
        if not args.skip_missing:
            print(f"{len(missing)} instance file(s) missing, e.g. {[m.key for m in missing[:4]]}\n"
                  f"  (download/generate them: benchmarks/satlib.py, benchmarks/gbd.py download, "
                  f"benchmarks/generators/generate.py --tier medium; or use --skip-missing)", file=sys.stderr)
            return 2
        entries = [e for e in entries if e.path.exists()]
    if not entries:
        print("no instances selected", file=sys.stderr)
        return 2

    ref = load_reference(Path(args.reference)) if args.reference else {}
    expected = {}
    conflicts = []
    for e in entries:
        r = ref.get(e.key, {}).get("status")
        r = r if r in ("sat", "unsat") else None
        if e.expected and r and e.expected != r:
            conflicts.append(f"{e.key}: set says {e.expected}, reference says {r}")
        expected[e.key] = e.expected or r
    for c in conflicts:
        print(f"WARNING: expected-status conflict: {c} (using the set file)", file=sys.stderr)

    if args.list:
        for e in entries:
            print(f"{e.key:<70} {expected[e.key] or '-':<6} {family_of(e):<16}"
                  f"{'' if e.path.exists() else ' MISSING'}")
        n_sat = sum(1 for e in entries if expected[e.key] == "sat")
        n_unsat = sum(1 for e in entries if expected[e.key] == "unsat")
        print(f"{len(entries)} instances: {n_sat} sat, {n_unsat} unsat, "
              f"{len(entries) - n_sat - n_unsat} unknown; {len(missing)} missing")
        return 0

    solver_cmd = resolve_solver(args.solver)
    if not os.path.exists(solver_cmd[0]) and shutil.which(solver_cmd[0]) is None:
        print(f"solver not found: {paths.strip_local(solver_cmd[0])}", file=sys.stderr)
        return 2

    # ---- result files
    stamp = dt.datetime.now().strftime("%Y%m%d-%H%M%S")
    sha = git_sha()
    out_dir = Path(args.out_dir)
    base = f"{stamp}_{sha}" + (f"_{args.tag}" if args.tag else "")
    meta = {
        "timestamp": stamp, "git_sha": sha, "solver": paths.strip_local(args.solver),
        "solver_cmd": [paths.strip_local(a) for a in solver_cmd[1 if solver_cmd[0] == sys.executable else 0:]],
        "solver_sha256": solver_fingerprint(solver_cmd), "time_limit": args.time_limit,
        "mem_limit_mb": args.mem_limit, "jobs": args.jobs, "seed": args.seed, "extra": args.extra,
        "proof": args.proof, "checker": args.checker_obj.name if args.checker_obj else None,
        "sets": [paths.strip_local(x) for x in args.set], "argv": [paths.strip_local(a) for a in argv], "platform": platform.platform(),
        "machine": platform.machine(), "cpu_count": os.cpu_count(), "python": platform.python_version(),
    }
    done = []
    if args.resume:
        if args.no_save:
            print("--resume and --no-save exclude each other", file=sys.stderr)
            return 2
        rpath = Path(args.resume)
        try:
            old_meta, done = load_partial(rpath)
        except (OSError, ValueError, KeyError) as ex:
            print(f"cannot resume from {rpath.name}: {ex}", file=sys.stderr)
            return 2
        diff = {k: (old_meta.get(k), meta[k]) for k in RESUME_KEYS if old_meta.get(k) != meta[k]}
        if diff:
            print(f"cannot resume {rpath.name}: settings differ (old, new): {diff}", file=sys.stderr)
            return 2
        if old_meta.get("git_sha") != sha:
            print(f"WARNING: resuming a run of {old_meta.get('git_sha')} with {sha}", file=sys.stderr)
        redo = {c.strip() for c in args.redo.split(",") if c.strip()}
        done = [r for r in done if r["class"] not in redo]
        meta = {**old_meta, "resumed": list(old_meta.get("resumed", [])) + [
            {"timestamp": stamp, "git_sha": sha, "argv": meta["argv"], "kept": len(done)}]}
        out_dir = rpath.parent
        base = rpath.name.removesuffix(".jsonl").removesuffix(".json")
        finished = {r["instance"] for r in done}
        todo = [e for e in entries if e.key not in finished]
        print(f"resuming {rpath.name}: {len(done)} recorded, {len(todo)} to run")
    else:
        todo = entries
    jsonl = out_dir / f"{base}.jsonl"
    keep_dir = (out_dir / f"{base}.logs") if (args.keep_logs and not args.no_save) else None
    if not args.no_save:
        out_dir.mkdir(parents=True, exist_ok=True)
        tmp = jsonl.with_suffix(".jsonl.tmp")
        with open(tmp, "w") as fh:
            fh.write(json.dumps({"meta": meta}) + "\n")
            for r in done:
                fh.write(json.dumps({"result": r}) + "\n")
        tmp.replace(jsonl)

    chk = args.checker_obj.name if args.checker_obj else "none (UNSAT proofs unchecked)"
    print(f"running {len(todo)} instances, time limit {args.time_limit:g} s, mem {args.mem_limit} MB, "
          f"jobs {args.jobs}, proof {'on' if args.proof else 'off'} (checker: {chk if args.proof else '-'})")
    print(f"solver: {paths.strip_local(args.solver)}{(' ' + args.extra) if args.extra else ''}  @ {sha}")
    if not args.no_save:
        print(f"progress: {paths.portable(jsonl)}  (after an interruption: same command + "
              f"--resume {paths.portable(jsonl)})")
    hdr = f"{'instance':<52} {'exp':<6} {'class':<9} {'status':<8} {'time':>9} {'MB':>7}  proof"
    print(hdr)
    print("-" * len(hdr))
    recs = list(done)
    lock = threading.Lock()

    def show(r):
        key = r["instance"] if len(r["instance"]) <= 52 else "..." + r["instance"][-49:]
        tm = f"{r['time']:.2f}" if r.get("time") is not None else "-"
        mb = f"{r['peak_rss_mb']:.0f}" if r.get("peak_rss_mb") is not None else "-"
        line = (f"{key:<52} {r.get('expected') or '-':<6} {r['class']:<9} {str(r.get('status') or '-'):<8} "
                f"{tm:>9} {mb:>7}  {r.get('proof') or ''}")
        if r["class"] == WRONG:
            line += f"   <<<<<< WRONG: {r['message']}"
        elif r["class"] in (ERROR, MEMLIMIT) or (r["message"] and r["class"] != UNSOLVED):
            line += f"   << {r['message'][:160]}"
        print(line, flush=True)

    def record(r):
        with lock:
            show(r)
            recs.append(r)
            if not args.no_save:
                with open(jsonl, "a") as fh:
                    fh.write(json.dumps({"result": r}) + "\n")
                    fh.flush()
                    os.fsync(fh.fileno())

    tmproot = Path(tempfile.mkdtemp(prefix="psat-run-"))
    old_term = signal.signal(signal.SIGTERM, _on_sigterm)
    try:
        if args.jobs > 1:
            with ThreadPoolExecutor(max_workers=args.jobs) as ex:
                futs = [ex.submit(run_one, e, expected[e.key], args, solver_cmd, tmproot, keep_dir) for e in todo]
                try:
                    for fut in as_completed(futs):
                        record(fut.result())
                except BaseException:
                    for fu in futs:
                        fu.cancel()
                    kill_all()
                    raise
        else:
            for e in todo:
                record(run_one(e, expected[e.key], args, solver_cmd, tmproot, keep_dir))
    except (KeyboardInterrupt, _Terminated):
        kill_all()
        print(f"\ninterrupted; {len(recs)} instance(s) recorded", file=sys.stderr)
        if not args.no_save:
            print(f"continue with the same command plus  --resume {paths.portable(jsonl)}", file=sys.stderr)
        return 130
    finally:
        signal.signal(signal.SIGTERM, old_term)
        shutil.rmtree(tmproot, ignore_errors=True)
    order = {e.key: i for i, e in enumerate(entries)}
    recs.sort(key=lambda r: order.get(r["instance"], len(order)))

    # ---- summary
    t = args.time_limit
    s = summarize(recs, t)
    c = s["classes"]
    print("-" * len(hdr))
    print(f"instances {s['instances']}  solved {s['solved']} (sat {s['solved_sat']}, unsat {s['solved_unsat']})  "
          f"unsolved {c[UNSOLVED]}  memlimit {c[MEMLIMIT]}  errors {c[ERROR]}  WRONG {c[WRONG]}")
    if s["par2"] is not None:
        print(f"PAR-2 {s['par2']:.2f} s   shifted geometric mean {s['sgm_time']:.3f} s "
              f"(shift {SGM_SHIFT:g} s, unsolved = {t:g} s)")
    if s["proofs"]:
        print("UNSAT proofs: " + ", ".join(f"{k} {v}" for k, v in sorted(s["proofs"].items())))
    by_fam = {}
    for r in recs:
        f = by_fam.setdefault(r["family"], [0, 0])
        f[0] += 1
        f[1] += r["class"] == OK
    if len(by_fam) > 1:
        print("per family (solved/total): " + ", ".join(f"{k} {v[1]}/{v[0]}" for k, v in sorted(by_fam.items())))

    if not args.no_save:
        tmp = out_dir / f"{base}.json.tmp"
        tmp.write_text(json.dumps({"meta": meta, "summary": s, "results": recs}, indent=1) + "\n")
        tmp.replace(out_dir / f"{base}.json")
        jsonl.unlink(missing_ok=True)
        cols = ["instance", "family", "expected", "status", "class", "time", "cpu", "peak_rss_mb", "returncode",
                "proof", "proof_checker", "proof_time", "proof_mb", "verify_time", "model_missing", "message"]
        with open(out_dir / f"{base}.csv", "w", newline="") as fh:
            w = csv.DictWriter(fh, fieldnames=cols, extrasaction="ignore")
            w.writeheader()
            for r in recs:
                w.writerow(r)
        print(f"results: {paths.portable(out_dir / (base + '.json'))}")

    rc = 0
    wrong = [r for r in recs if r["class"] == WRONG]
    if wrong:
        print("\n" + "!" * 78)
        print(f"!!! {len(wrong)} WRONG ANSWER(S):")
        for r in wrong:
            print(f"!!!   {r['instance']}: {r['message']}")
        print("!" * 78)
        rc = 1
    if args.strict:
        if c[ERROR]:
            print(f"--strict: {c[ERROR]} error(s)")
            rc = 1
        if s["unchecked_proofs"] and not args.allow_unchecked:
            print(f"--strict: {s['unchecked_proofs']} UNSAT answer(s) without a verified proof "
                  f"(no drat-trim? see benchmarks/README.md; or --allow-unchecked)")
            rc = 1
    if args.require_solved and s["solved"] < s["instances"]:
        print(f"--require-solved: {s['instances'] - s['solved']} of {s['instances']} not solved")
        rc = 1
    return rc


if __name__ == "__main__":
    sys.exit(main())
