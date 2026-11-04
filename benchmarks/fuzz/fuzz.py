#!/usr/bin/env python3
"""Random CNF fuzzing of popso-sat against a PySAT reference solver.

For each seed, gen.py builds a formula; the PySAT reference (default
cadical195) solves it in-process; the solver under test runs on it with a time
limit; fuzzlib.check() classifies the result (status agreement, model check
including coverage of all variables, proof check with drat-trim when built,
crashes, malformed output, exit codes, hangs). Failures are saved to
benchmarks/fuzz/failures/ (formula + solver arguments + kind) and, with
--shrink, minimized by ddmin.py.

  fuzz.py                                   1000 formulas from seed 0, -j 2
  fuzz.py --count 100000 --seed 5000000 -j 4
  fuzz.py --time-budget 300                 run for 5 minutes
  fuzz.py --solver 'python3 buggy_solver.py --bug=crash:0.01' --shrink
  fuzz.py --option-ranges opts.txt          also fuzz solver options

Everything is deterministic per seed (formula, --seed passed to the solver,
fuzzed options), so `--seed S --count 1` with the same flags reproduces a
failure.

Option ranges (--option-ranges FILE or inline 'spec; spec; ...'), one per line:
  --restart=luby,ema,glucose    pick one value
  --reduce-int=100..3000        integer in the range
  --decay=0.80..0.99            float in the range (a bound contains '.')
  --proof-text                  bare flag
Each listed option is added with probability --option-prob (default 0.5), so
defaults keep being tested too. '#' starts a comment.
"""

from __future__ import annotations

import argparse
import json
import random
import shlex
import shutil
import sys
import tempfile
import time
from collections import Counter
from concurrent.futures import FIRST_COMPLETED, ProcessPoolExecutor, wait
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import fuzzlib  # noqa: E402
import gen  # noqa: E402
from fuzzlib import KINDS, Config, check, shell_join  # noqa: E402

FAILURES = fuzzlib.HERE / "failures"
MAX_JOBS = 4


# --------------------------------------------------------------------------- option fuzzing


def parse_option_ranges(spec: str) -> list[tuple[str, object]]:
    """[(name, values)], values: list[str] | ('int', lo, hi) | ('float', lo, hi) | None (flag)."""
    p = Path(spec)
    text = p.read_text() if p.is_file() else spec.replace(";", "\n")
    out = []
    for line in text.splitlines():
        line = line.split("#", 1)[0].strip()
        if not line:
            continue
        if "=" not in line:
            out.append((line, None))
            continue
        name, vals = line.split("=", 1)
        vals = vals.strip()
        if ".." in vals and "," not in vals:
            lo, hi = vals.split("..", 1)
            if "." in lo or "." in hi:
                out.append((name, ("float", float(lo), float(hi))))
            else:
                out.append((name, ("int", int(lo), int(hi))))
        else:
            out.append((name, [v.strip() for v in vals.split(",") if v.strip()]))
    return out


def pick_options(seed: int, ranges, prob: float, pass_seed: bool) -> list[str]:
    rng = random.Random(f"popso-sat-opts-{seed}")
    opts = [f"--seed={rng.randrange(1 << 31)}"] if pass_seed else []
    for name, vals in ranges:
        if rng.random() >= prob:
            continue
        if vals is None:
            opts.append(name)
        elif isinstance(vals, tuple):
            kind, lo, hi = vals
            v = rng.randint(lo, hi) if kind == "int" else round(rng.uniform(lo, hi), 4)
            opts.append(f"{name}={v}")
        else:
            opts.append(f"{name}={rng.choice(vals)}")
    return opts


# --------------------------------------------------------------------------- worker

_W: dict = {}


def _init_worker(cfg: Config, families, max_vars, ranges, option_prob, pass_seed, tmp_root):
    # Per-worker scratch directory inside the run's temp root (removed by the main process).
    _W.update(cfg=cfg, families=families, max_vars=max_vars, ranges=ranges, option_prob=option_prob,
              pass_seed=pass_seed, workdir=Path(tempfile.mkdtemp(prefix="w", dir=tmp_root)))


def _run_seed(seed: int) -> dict:
    f = gen.generate(seed, _W["families"], _W["max_vars"])
    opts = pick_options(seed, _W["ranges"], _W["option_prob"], _W["pass_seed"])
    t0 = time.perf_counter()
    o = check(f.nvars, f.clauses, _W["cfg"], opts, _W["workdir"], expected=f.expected)
    res = dict(seed=seed, family=f.family, nvars=f.nvars, nclauses=len(f.clauses), expected=f.expected,
               opts=opts, kind=o.kind, detail=o.detail, status=o.status, ref=o.ref, exit_code=o.exit_code,
               seconds=o.seconds, ref_seconds=o.ref_seconds, proof=o.proof, wall=time.perf_counter() - t0,
               cmd=o.cmd)
    if o.kind:
        res["dimacs"] = f.dimacs()
    return res


# --------------------------------------------------------------------------- failures


def _rel(p: Path) -> str:
    try:
        return str(p.resolve().relative_to(fuzzlib.REPO))
    except ValueError:
        return str(p)


def save_failure(res: dict, cfg: Config, outdir: Path) -> Path:
    outdir.mkdir(parents=True, exist_ok=True)
    stem = outdir / f"{res['kind']}-s{res['seed']}"
    header = [
        f"c fuzz-kind: {res['kind']}",
        f"c fuzz-detail: {res['detail']}",
        f"c fuzz-solver: {shell_join(cfg.solver)}",
        f"c fuzz-extra: {shell_join(cfg.extra)}",
        f"c fuzz-args: {shell_join(res['opts'])}",
        f"c fuzz-proof: {'yes' if cfg.proof else 'no'} {cfg.proof_style}",
        f"c fuzz-time-limit: {cfg.time_limit:g}",
        f"c fuzz-reference: {cfg.reference} -> {res['ref']}",
    ]
    stem.with_suffix(".cnf").write_text("\n".join(header) + "\n" + res["dimacs"])
    meta = {k: v for k, v in res.items() if k != "dimacs"}
    cnf = stem.with_suffix(".cnf")
    meta.update(solver=cfg.solver, extra=cfg.extra, proof_requested=cfg.proof, proof_style=cfg.proof_style,
                time_limit=cfg.time_limit, reference=cfg.reference, checker=cfg.checker_label,
                replay=shell_join(fuzzlib.solver_command(cfg, res["opts"], cnf, None)),
                ddmin=f"benchmarks/fuzz/ddmin.py {_rel(cnf)}")
    stem.with_suffix(".json").write_text(json.dumps(meta, indent=1) + "\n")
    return stem.with_suffix(".cnf")


def shrink_failure(path: Path, res: dict, cfg: Config, quiet: bool, jobs: int) -> str:
    import ddmin

    nvars, clauses, _ = fuzzlib.parse_dimacs(path.read_text())
    out = path.with_suffix(".min.cnf")
    with tempfile.TemporaryDirectory(prefix="popso-ddmin-") as wd:
        r = ddmin.shrink(nvars, clauses, cfg, res["opts"], res["kind"], Path(wd), log=None if quiet else _log,
                         jobs=jobs)
    if r is None:
        return "does not reproduce"
    n2, c2, tests = r
    comments = [l for l in path.read_text().splitlines() if l.startswith("c fuzz-")]
    comments.append(f"c fuzz-shrunk: from {nvars} vars / {len(clauses)} clauses in {tests} runs")
    fuzzlib.write_dimacs(out, n2, c2, comments)
    return f"shrunk {nvars}v/{len(clauses)}c -> {n2}v/{len(c2)}c ({tests} runs): {_rel(out)}"


def _log(msg: str) -> None:
    print(f"  ddmin: {msg}", file=sys.stderr, flush=True)


# --------------------------------------------------------------------------- main


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--solver", default=fuzzlib.default_solver(),
                    help="solver command (shell-quoted string; default <checkout>/build/popso-sat)")
    ap.add_argument("--extra", default="", help="extra solver options for every run (shell-quoted string)")
    ap.add_argument("--option-ranges", help="file or inline 'spec; spec' of options to fuzz (see above)")
    ap.add_argument("--option-prob", type=float, default=0.5, help="probability to add each fuzzed option")
    ap.add_argument("--no-seed", action="store_true", help="do not pass --seed=<n> to the solver")
    ap.add_argument("--seed", type=int, default=0, help="first formula seed (default 0)")
    ap.add_argument("--count", type=int, help="number of formulas (default 1000 unless --time-budget)")
    ap.add_argument("--time-budget", type=float, help="stop starting new formulas after this many seconds")
    ap.add_argument("-j", "--jobs", type=int, default=2, help=f"parallel workers (default 2, max {MAX_JOBS})")
    ap.add_argument("--family", help="comma-separated generator families (default: full mix; see gen.py --list)")
    ap.add_argument("--max-vars", type=int, default=200, help="variable cap for scalable families (default 200)")
    ap.add_argument("-t", "--time-limit", type=float, default=10.0, help="per-run solver time limit (default 10 s)")
    ap.add_argument("--reference", default="cadical195", help="PySAT reference solver (default cadical195)")
    ap.add_argument("--checker", default="auto",
                    help="proof checker: auto (drat-trim if built), none, drat-trim, rupcheck, or a command")
    ap.add_argument("--proof", choices=["auto", "always", "never"], default="auto",
                    help="request proofs: auto = when a checker is available")
    ap.add_argument("--proof-style", choices=["positional", "option"], default="positional",
                    help="pass the proof as '<input> <proof>' or '--proof=<file>'")
    ap.add_argument("--allow-partial-model", action="store_true", help="do not require all variables in the model")
    ap.add_argument("--shrink", action="store_true",
                    help="ddmin the first failure of each kind (after the fuzz loop, -j parallel runs)")
    ap.add_argument("--shrink-all", action="store_true", help="ddmin every failure")
    ap.add_argument("--stop-after", type=int, default=0, help="stop after this many failures (0 = never)")
    ap.add_argument("--failures-dir", default=str(FAILURES),
                    help="where failures are saved (default benchmarks/fuzz/failures)")
    ap.add_argument("--progress", type=float, default=30.0, help="progress line every N seconds (0 = off)")
    ap.add_argument("-q", "--quiet", action="store_true")
    args = ap.parse_args(argv)

    jobs = max(1, min(args.jobs, MAX_JOBS))
    if args.jobs > MAX_JOBS:
        print(f"c -j capped at {MAX_JOBS} (shared machine)", file=sys.stderr)
    count = args.count if args.count is not None else (None if args.time_budget else 1000)
    checker, label = fuzzlib.resolve_checker(args.checker)
    want_proof = args.proof == "always" or (args.proof == "auto" and checker is not None)
    cfg = Config(solver=shlex.split(args.solver), extra=shlex.split(args.extra), time_limit=args.time_limit,
                 proof=want_proof, proof_style=args.proof_style, checker=checker, checker_label=label,
                 reference=args.reference, allow_partial=args.allow_partial_model)
    exe = shutil.which(cfg.solver[0]) or (cfg.solver[0] if Path(cfg.solver[0]).exists() else None)
    if not exe:
        print(f"error: solver {cfg.solver[0]!r} not found", file=sys.stderr)
        return 2
    families = args.family.split(",") if args.family else None
    gen._select(families)  # validate names early
    ranges = parse_option_ranges(args.option_ranges) if args.option_ranges else []

    print(f"c fuzz: solver {shell_join(cfg.solver + cfg.extra)}; reference {cfg.reference}; -j {jobs}; "
          f"time limit {cfg.time_limit:g}s; seeds from {args.seed}"
          + (f", count {count}" if count is not None else "") + (f", budget {args.time_budget:g}s" if args.time_budget else ""))
    if checker is None:
        print(f"c fuzz: proof checks disabled ({label})" + ("; proofs still requested" if want_proof else ""))
    else:
        print(f"c fuzz: proofs checked with {label}")
    if ranges:
        print(f"c fuzz: fuzzing {len(ranges)} options (p={args.option_prob:g})")

    outdir = Path(args.failures_dir)
    tmp_root = tempfile.mkdtemp(prefix="popso-fuzz-")
    stats = Counter()
    fails = Counter()
    proofs = Counter()
    shrunk_kinds: set[str] = set()
    to_shrink: list[tuple[Path, dict]] = []
    t_start = time.perf_counter()
    last_progress = t_start
    next_seed = args.seed
    end_seed = None if count is None else args.seed + count
    stop = False

    def more() -> bool:
        if stop:
            return False
        if end_seed is not None and next_seed >= end_seed:
            return False
        if args.time_budget and time.perf_counter() - t_start >= args.time_budget:
            return False
        return True

    ex = ProcessPoolExecutor(max_workers=jobs, initializer=_init_worker,
                             initargs=(cfg, families, args.max_vars, ranges, args.option_prob, not args.no_seed,
                                       tmp_root))
    with ex:
        pending = set()
        try:
            while True:
                while more() and len(pending) < 2 * jobs:
                    pending.add(ex.submit(_run_seed, next_seed))
                    next_seed += 1
                if not pending:
                    break
                done, pending = wait(pending, timeout=5, return_when=FIRST_COMPLETED)
                for fut in done:
                    res = fut.result()
                    stats["formulas"] += 1
                    stats[f"status:{res['status']}"] += 1
                    stats[f"ref:{res['ref']}"] += 1
                    stats["solver_seconds"] += res["seconds"]
                    stats["ref_seconds"] += res["ref_seconds"]
                    if res["proof"]:
                        proofs[res["proof"]] += 1
                    if res["kind"]:
                        fails[res["kind"]] += 1
                        path = save_failure(res, cfg, outdir)
                        line = (f"FAIL {res['kind']} seed={res['seed']} family={res['family']} "
                                f"n={res['nvars']} m={res['nclauses']} args={shell_join(res['opts']) or '-'}: "
                                f"{res['detail']} -> {_rel(path)}")
                        if args.shrink_all or (args.shrink and res["kind"] not in shrunk_kinds):
                            shrunk_kinds.add(res["kind"])
                            to_shrink.append((path, res))
                        print(line, flush=True)
                        if args.stop_after and sum(fails.values()) >= args.stop_after:
                            stop = True
                now = time.perf_counter()
                if args.progress and now - last_progress >= args.progress and not args.quiet:
                    last_progress = now
                    el = now - t_start
                    print(f"c [{el:6.0f}s] {stats['formulas']} formulas ({stats['formulas'] / max(el, 1e-9):.1f}/s), "
                          f"SAT {stats['status:SAT']} UNSAT {stats['status:UNSAT']} UNKNOWN {stats['status:UNKNOWN']}, "
                          f"failures {sum(fails.values())}", file=sys.stderr, flush=True)
        except KeyboardInterrupt:
            print("c interrupted", file=sys.stderr)
        finally:
            ex.shutdown(wait=True, cancel_futures=True)
            shutil.rmtree(tmp_root, ignore_errors=True)

    el = time.perf_counter() - t_start
    # Shrink after the fuzz loop, so ddmin's parallel runs never overlap the workers.
    t_shrink = time.perf_counter()
    for path, res in to_shrink:
        try:
            msg = shrink_failure(path, res, cfg, args.quiet, jobs)
        except KeyboardInterrupt:
            print("c shrinking interrupted", file=sys.stderr)
            break
        print(f"SHRUNK {res['kind']} seed={res['seed']}: {msg}", flush=True)
    t_shrink = time.perf_counter() - t_shrink
    n = stats["formulas"]
    print(f"c ---- summary: {n} formulas in {el:.1f}s ({n / max(el, 1e-9):.1f} formulas/s, -j {jobs})"
          + (f", then shrinking {t_shrink:.1f}s" if to_shrink else ""))
    print(f"c solver:    SAT {stats['status:SAT']}  UNSAT {stats['status:UNSAT']}  "
          f"UNKNOWN {stats['status:UNKNOWN']}  no answer {stats['status:None']}   "
          f"(mean {stats['solver_seconds'] / max(n, 1) * 1000:.1f} ms)")
    print(f"c reference: SAT {stats['ref:SAT']}  UNSAT {stats['ref:UNSAT']}  UNKNOWN {stats['ref:UNKNOWN']}   "
          f"(mean {stats['ref_seconds'] / max(n, 1) * 1000:.1f} ms, {cfg.reference})")
    if cfg.proof:
        print("c proofs:    " + ("  ".join(f"{k} {v}" for k, v in sorted(proofs.items())) or "none")
              + f"   (checker: {label})")
    else:
        print("c proofs:    not checked")
    if fails:
        print("c failures:  " + "  ".join(f"{k} {fails[k]}" for k in KINDS if fails[k])
              + f"   (saved in {_rel(outdir)}/)")
    else:
        print("c failures:  0")
    return 1 if fails else 0


if __name__ == "__main__":
    sys.exit(main())
