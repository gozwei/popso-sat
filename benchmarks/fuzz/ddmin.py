#!/usr/bin/env python3
"""Delta debugging of a failing CNF for popso-sat.

  ddmin.py <cnf> --solver <cmd> --kind <kind> -o <out.cnf>
  ddmin.py benchmarks/fuzz/failures/disagree-s123.cnf      (settings from its 'c fuzz-*' header)

The failure predicate re-runs the same check as fuzz.py (fuzzlib.check) and
asks for the same failure kind:
  disagree, model-invalid, model-incomplete, proof-rejected, proof-missing,
  crash, hang, timeout, exit-code, garbage, error, reference-wrong
  exit:<X>   the solver exits with code X (any output)
  any        any failure kind

Minimization, repeated until nothing changes:
  1. ddmin over the clause list (complement-based, as in cnfdd: the empty
     formula first, then removing chunks of n/2, n/4, ..., 1 clauses, keeping
     every removal that still fails, until 1-minimal);
  2. the same over the literals of each clause;
then variables are renumbered compactly (1..k, header k) if the failure
survives that, else the header is lowered by bisection towards the largest
used variable. The output header always matches the clauses.

Candidates of one ddmin step are tested -j at a time (default 2, max 4); the
first failing one in order is taken, so the result does not depend on -j.
"""

from __future__ import annotations

import argparse
import itertools
import shlex
import sys
import tempfile
import threading
import time
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import fuzzlib  # noqa: E402
from fuzzlib import KINDS, Config, check, run_solver, solver_command, write_dimacs  # noqa: E402

Clauses = list[list[int]]


class Budget(Exception):
    pass


class Predicate:
    """fails(nvars, clauses) -> True if the solver still shows the failure.
    first(candidates) evaluates candidates in batches of `jobs` parallel runs
    and returns the index of the first failing one (results are cached)."""

    def __init__(self, cfg: Config, opts: list[str], kind: str, workdir: Path, max_tests: int, jobs: int = 1):
        self.cfg, self.opts, self.kind, self.workdir = cfg, opts, kind, Path(workdir)
        self.max_tests = max_tests
        self.jobs = max(1, jobs)
        self.tests = 0
        self.exhausted = False
        self.cache: dict = {}
        self.need_ref = kind in ("disagree", "reference-wrong", "timeout", "any")
        self.check_proof = kind in ("proof-rejected", "proof-missing", "any")
        self._pool = ThreadPoolExecutor(self.jobs) if self.jobs > 1 else None
        self._local = threading.local()
        self._ids = itertools.count()

    def close(self) -> None:
        if self._pool:
            self._pool.shutdown()

    def _dir(self) -> Path:
        d = getattr(self._local, "dir", None)
        if d is None:
            d = self.workdir / f"t{next(self._ids)}"
            d.mkdir(parents=True, exist_ok=True)
            self._local.dir = d
        return d

    def _eval(self, nvars: int, clauses: Clauses) -> bool:
        wd = self._dir()
        if self.kind.startswith("exit:"):
            cnf = wd / "formula.cnf"
            write_dimacs(cnf, nvars, clauses)
            proof = wd / "proof.drat" if self.cfg.proof else None
            r = run_solver(self.cfg, solver_command(self.cfg, self.opts, cnf, proof))
            return not r.killed and r.returncode == int(self.kind[5:])
        o = check(nvars, clauses, self.cfg, self.opts, wd, need_ref=self.need_ref, check_proof_now=self.check_proof)
        return o.kind is not None if self.kind == "any" else o.kind == self.kind

    @staticmethod
    def _key(nvars: int, clauses: Clauses):
        return nvars, tuple(tuple(c) for c in clauses)

    def first(self, candidates) -> int:
        it = iter(candidates)
        base = 0
        while True:
            batch = list(itertools.islice(it, self.jobs))
            if not batch:
                return -1
            keys = [self._key(nv, cl) for nv, cl in batch]
            todo, seen = [], set()
            for i, k in enumerate(keys):
                if k in self.cache:
                    if self.cache[k]:
                        break  # an earlier candidate is already known to fail
                elif k not in seen:
                    seen.add(k)
                    todo.append(i)
            if todo:
                if self.tests + len(todo) > self.max_tests:
                    raise Budget()
                self.tests += len(todo)
                if self._pool and len(todo) > 1:
                    results = list(self._pool.map(lambda i: self._eval(*batch[i]), todo))
                else:
                    results = [self._eval(*batch[i]) for i in todo]
                for i, r in zip(todo, results):
                    self.cache[keys[i]] = r
            for i, k in enumerate(keys):
                if self.cache.get(k):
                    return base + i
            base += len(batch)

    def __call__(self, nvars: int, clauses: Clauses) -> bool:
        return self.first([(nvars, clauses)]) == 0


def ddmin_list(items: list, cand, pred: Predicate, say=None) -> list:
    """Complement-based ddmin over `items` (the variant used by CNF delta
    debuggers such as cnfdd): try removing chunks of size len/2, len/4, ..., 1,
    sweeping left to right and keeping every removal that still fails; at size 1
    repeat until nothing can be removed (1-minimal). Removing one half is the
    same as Zeller's subset test, so tiny cores are found in O(log n) steps.
    cand(sub) builds the (nvars, clauses) to test; it must fail for `items`.
    The removals at the remaining chunk positions are tested `jobs` at a time and
    the first failing one in order is taken. When the run budget is exhausted the
    smallest failing list so far is returned and pred.exhausted is set."""
    try:
        if pred.first([cand([])]) == 0:
            return []
        chunk = max(1, len(items) // 2)
        while True:
            changed = False
            i = 0
            while i < len(items):
                k = pred.first(cand(items[:s] + items[s + chunk:]) for s in range(i, len(items), chunk))
                if k < 0:
                    break
                s = i + k * chunk
                items = items[:s] + items[s + chunk:]
                changed, i = True, s
            if say:
                say(f"  chunk {chunk}: {len(items)} left ({pred.tests} runs)")
            if chunk > 1:
                chunk = max(1, min(chunk // 2, len(items) // 2))
            elif not changed:
                return items
    except Budget:
        pred.exhausted = True
        return items


def renumber(nvars: int, clauses: Clauses, fails) -> tuple[int, Clauses]:
    """Compact variable numbering (1..k in order of the old indices), then the
    smallest header >= the largest used variable that still fails (bisection)."""
    used = sorted({abs(l) for c in clauses for l in c})
    m = {v: i + 1 for i, v in enumerate(used)}
    ren = [[m[abs(l)] * (1 if l > 0 else -1) for l in c] for c in clauses]
    if ren != clauses:
        if fails(len(used), ren):
            return len(used), ren
        if fails(nvars, ren):
            clauses = ren
    lo, hi = max(used, default=0), nvars
    while lo < hi:
        mid = (lo + hi) // 2
        if fails(mid, clauses):
            hi = mid
        else:
            lo = mid + 1
    return hi, clauses


def shrink(nvars: int, clauses: Clauses, cfg: Config, opts: list[str], kind: str, workdir: Path,
           log=None, max_tests: int = 5000, jobs: int = 1) -> tuple[int, Clauses, int] | None:
    """Minimized (nvars, clauses, number of solver runs), or None if the
    failure does not reproduce on the input. Up to `jobs` solver runs at a time."""
    fails = Predicate(cfg, opts, kind, workdir, max_tests, jobs)
    try:
        if not fails(nvars, clauses):
            return None
        say = log or (lambda m: None)
        for rnd in range(1, 6):
            before = (nvars, [c[:] for c in clauses])
            clauses = ddmin_list(clauses, lambda sub: (nvars, sub), fails, say if log else None)
            say(f"round {rnd}: clauses -> {len(clauses)} ({fails.tests} runs)")
            for i in range(len(clauses)):
                if fails.exhausted:
                    break
                clauses[i] = ddmin_list(clauses[i], lambda lits, i=i: (nvars, clauses[:i] + [lits] + clauses[i + 1:]),
                                        fails)
            say(f"round {rnd}: literals -> {sum(map(len, clauses))} ({fails.tests} runs)")
            if fails.exhausted or (nvars, clauses) == before:
                break
        if not fails.exhausted:
            try:
                nvars, clauses = renumber(nvars, clauses, fails)
            except Budget:
                fails.exhausted = True
        if fails.exhausted:
            say(f"run budget of {max_tests} exhausted; keeping the smallest failing formula so far")
        return nvars, clauses, fails.tests
    except Budget:  # only if max_tests == 0
        return nvars, clauses, fails.tests
    finally:
        fails.close()


def _header(comments: list[str]) -> dict[str, str]:
    out = {}
    for c in comments:
        if c.startswith("c fuzz-") and ":" in c:
            k, v = c[len("c fuzz-"):].split(":", 1)
            out[k.strip()] = v.strip()
    return out


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("cnf")
    ap.add_argument("--solver", help="solver command (default: from the file header, else <checkout>/build/popso-sat)")
    ap.add_argument("--kind", help=f"failure kind: {', '.join(KINDS)}, exit:<X>, any (default: from the file header)")
    ap.add_argument("--args", help="solver options of the failing run, e.g. '--seed=7' (default: from the header)")
    ap.add_argument("--extra", help="extra solver options (default: from the header)")
    ap.add_argument("-o", "--output", help="output file (default <input>.min.cnf)")
    ap.add_argument("-t", "--time-limit", type=float, help="per-run time limit (default: header, else 10)")
    ap.add_argument("--reference", help="PySAT reference (default: header, else cadical195)")
    ap.add_argument("--checker", default="auto", help="proof checker: auto, none, drat-trim, rupcheck, or a command")
    ap.add_argument("--proof", choices=["auto", "always", "never"], default="auto",
                    help="request proofs (auto: as in the failing run, else when a checker is available)")
    ap.add_argument("--proof-style", choices=["positional", "option"], help="default: header, else positional")
    ap.add_argument("--allow-partial-model", action="store_true")
    ap.add_argument("--max-tests", type=int, default=5000, help="maximum solver runs (default 5000)")
    ap.add_argument("-j", "--jobs", type=int, default=2, help="parallel solver runs (default 2, max 4)")
    ap.add_argument("-q", "--quiet", action="store_true")
    args = ap.parse_args(argv)
    jobs = max(1, min(args.jobs, 4))

    text = Path(args.cnf).read_text()
    nvars, clauses, comments = fuzzlib.parse_dimacs(text)
    hdr = _header(comments)
    kind = args.kind or hdr.get("kind")
    if not kind:
        ap.error("--kind is required (no 'c fuzz-kind:' line in the file)")
    if kind not in KINDS and kind != "any" and not (kind.startswith("exit:") and kind[5:].lstrip("-").isdigit()):
        ap.error(f"unknown kind {kind!r}")
    solver = args.solver or hdr.get("solver") or fuzzlib.default_solver()
    extra = args.extra if args.extra is not None else hdr.get("extra", "")
    opts = args.args if args.args is not None else hdr.get("args", "")
    time_limit = args.time_limit or float(hdr.get("time-limit", 10))
    proof_hdr = hdr.get("proof", "").split()
    checker, label = fuzzlib.resolve_checker(args.checker)
    if args.proof == "auto":
        want_proof = proof_hdr[0] == "yes" if proof_hdr else checker is not None
    else:
        want_proof = args.proof == "always"
    if kind in ("proof-rejected",) and checker is None:
        ap.error("kind proof-rejected needs a proof checker (--checker drat-trim|rupcheck|<cmd>)")
    if kind.startswith("proof-") and not want_proof:
        want_proof = True
    style = args.proof_style or (proof_hdr[1] if len(proof_hdr) > 1 else "positional")
    reference = args.reference or hdr.get("reference", "cadical195").split(" ")[0]
    cfg = Config(solver=shlex.split(solver), extra=shlex.split(extra), time_limit=time_limit, proof=want_proof,
                 proof_style=style, checker=checker, checker_label=label, reference=reference,
                 allow_partial=args.allow_partial_model)
    opts_l = shlex.split(opts)
    out = Path(args.output) if args.output else Path(args.cnf).with_suffix(".min.cnf")

    log = None if args.quiet else (lambda m: print(f"c ddmin: {m}", file=sys.stderr, flush=True))
    if log:
        log(f"{nvars} vars, {len(clauses)} clauses; kind {kind}; solver {fuzzlib.shell_join(cfg.solver + cfg.extra + opts_l)}")
    t0 = time.perf_counter()
    with tempfile.TemporaryDirectory(prefix="popso-ddmin-") as wd:
        r = shrink(nvars, clauses, cfg, opts_l, kind, Path(wd), log=log, max_tests=args.max_tests, jobs=jobs)
    if r is None:
        print(f"c ddmin: the failure ({kind}) does not reproduce on {args.cnf}", file=sys.stderr)
        return 1
    n2, c2, tests = r
    keep = [c for c in comments if c.startswith("c fuzz-") and not c.startswith("c fuzz-shrunk")]
    if not keep:
        keep = [f"c fuzz-kind: {kind}", f"c fuzz-solver: {solver}", f"c fuzz-extra: {extra}", f"c fuzz-args: {opts}"]
    keep.append(f"c fuzz-shrunk: from {nvars} vars / {len(clauses)} clauses in {tests} runs")
    write_dimacs(out, n2, c2, keep)
    print(f"c ddmin: {nvars}v/{len(clauses)}c -> {n2}v/{len(c2)}c in {tests} runs "
          f"({time.perf_counter() - t0:.1f}s) -> {out}")
    if len(c2) <= 20:
        sys.stdout.write(fuzzlib.dimacs_text(n2, c2))
    return 0


if __name__ == "__main__":
    sys.exit(main())
