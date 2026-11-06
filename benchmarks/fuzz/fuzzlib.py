"""Shared pieces of the fuzzing tools: DIMACS I/O, running the solver under
test, parsing its output, checking models and proofs, and the PySAT reference.

`check()` runs one formula through the solver and returns an `Outcome` whose
`kind` is None (no problem found) or one of KINDS. fuzz.py and ddmin.py use the
same function, so a shrunk formula fails exactly the way the original did.
"""

from __future__ import annotations

import os
import shlex
import signal
import subprocess
import sys
import time
from dataclasses import dataclass, field
from pathlib import Path

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[1]  # the checkout (worktree) containing this file

# Failure kinds, roughly in the order they are checked.
KINDS = [
    "hang",              # did not stop within the hard wall-clock limit (ignored --time-limit)
    "sanitizer",         # ASan / UBSan / LSan / TSan / MSan report on stderr
    "crash",             # killed by a signal (segfault, abort, ...)
    "error",             # exit code 1 on a valid formula
    "garbage",           # malformed output (no/multiple s lines, bad v lines, unknown lines)
    "exit-code",         # exit code does not match the s line (10 SAT, 20 UNSAT, 0 UNKNOWN)
    "model-invalid",     # SAT model falsifies a clause, has out-of-range or contradictory literals
    "model-incomplete",  # SAT model does not assign every variable 1..n of the header
    "disagree",          # UNSAT, but the reference finds a (verified) model / SAT vs. known UNSAT
    "proof-missing",     # UNSAT, a proof was requested, no proof file written
    "proof-rejected",    # UNSAT, the proof checker rejects the proof
    "timeout",           # UNKNOWN after the full time limit on a formula the reference solves instantly
    "reference-wrong",   # the reference (or the generator's known status) is contradicted by a verified model
]

SANITIZER_MARKERS = ("ERROR: AddressSanitizer", "ERROR: LeakSanitizer", "ERROR: MemorySanitizer",
                     "WARNING: ThreadSanitizer", "runtime error:", "ERROR: UndefinedBehaviorSanitizer")
CRASH_SIGNALS = {signal.SIGSEGV, signal.SIGABRT, signal.SIGBUS, signal.SIGILL, signal.SIGFPE}


# --------------------------------------------------------------------------- locations


def main_checkout() -> Path | None:
    """The main checkout: parent of `git rev-parse --git-common-dir`."""
    try:
        out = subprocess.run(["git", "-C", str(HERE), "rev-parse", "--path-format=absolute", "--git-common-dir"],
                             capture_output=True, text=True, timeout=10)
    except (OSError, subprocess.TimeoutExpired):
        return None
    if out.returncode != 0 or not out.stdout.strip():
        return None
    return Path(out.stdout.strip()).parent


def find_tool(name: str) -> Path | None:
    roots = [REPO]
    main = main_checkout()
    if main and main.resolve() != REPO.resolve():
        roots.append(main)
    for root in roots:
        p = root / "benchmarks" / "tools" / "build" / "bin" / name
        if p.is_file() and os.access(p, os.X_OK):
            return p
    return None


def find_drat_trim() -> Path | None:
    return find_tool("drat-trim")


def default_solver() -> str:
    return str(REPO / "build" / "popso-sat")


def resolve_checker(spec: str) -> tuple[list[str] | None, str]:
    """Checker command prefix (called as `<cmd> <cnf> <proof>`) and a label.
    spec: auto (dpr-trim if built, else drat-trim, else none) | none | dpr-trim | drat-trim |
    rupcheck | <command>. dpr-trim also reads the PR lines of --counting (drat-trim rejects them)."""
    if spec == "none":
        return None, "none"
    if spec in ("auto", "dpr-trim"):
        p = find_tool("dpr-trim")
        if p:
            return [str(p)], "dpr-trim"
        if spec == "dpr-trim":
            raise SystemExit("dpr-trim not found under benchmarks/tools/build/bin (worktree or main checkout)")
    if spec in ("auto", "drat-trim"):
        p = find_drat_trim()
        if p:
            return [str(p)], "drat-trim"
        if spec == "drat-trim":
            raise SystemExit("drat-trim not found under benchmarks/tools/build/bin (worktree or main checkout)")
        return None, "drat-trim not built at benchmarks/tools/build/bin/ in this or the main checkout"
    if spec == "rupcheck":
        return [sys.executable, str(HERE / "rupcheck.py")], "rupcheck"
    return shlex.split(spec), "custom"


# --------------------------------------------------------------------------- DIMACS


def parse_dimacs(text: str) -> tuple[int, list[list[int]], list[str]]:
    """Returns (header nvars, clauses, comment lines). Tolerant: no header ->
    nvars = max variable; a '%' line ends the formula (SATLIB style)."""
    nvars = None
    clauses: list[list[int]] = []
    comments: list[str] = []
    cur: list[int] = []
    for line in text.splitlines():
        s = line.strip()
        if not s:
            continue
        if s[0] == "c":
            comments.append(line)
            continue
        if s[0] == "p":
            parts = s.split()
            if len(parts) != 4 or parts[1] != "cnf":
                raise ValueError(f"bad header: {line!r}")
            nvars = int(parts[2])
            continue
        if s[0] == "%":
            break
        for tok in s.split():
            v = int(tok)
            if v == 0:
                clauses.append(cur)
                cur = []
            else:
                cur.append(v)
    if cur:
        clauses.append(cur)
    maxv = max((abs(l) for c in clauses for l in c), default=0)
    return (maxv if nvars is None else max(nvars, maxv)), clauses, comments


def dimacs_text(nvars: int, clauses: list[list[int]], comments: list[str] = ()) -> str:
    out = [c if c.startswith("c") else "c " + c for c in comments]
    out.append(f"p cnf {nvars} {len(clauses)}")
    out.extend(" ".join(map(str, c + [0])) for c in clauses)
    return "\n".join(out) + "\n"


def write_dimacs(path: Path, nvars: int, clauses: list[list[int]], comments: list[str] = ()) -> None:
    Path(path).write_text(dimacs_text(nvars, clauses, comments))


# --------------------------------------------------------------------------- reference


def reference_solve(clauses: list[list[int]], name: str, time_limit: float) -> tuple[str, list[int] | None, float]:
    """(status, model, seconds) from a PySAT solver. Time-limited through
    growing conflict budgets (CaDiCaL in PySAT cannot be interrupted)."""
    from pysat.solvers import Solver

    t0 = time.perf_counter()
    if any(len(c) == 0 for c in clauses):
        return "UNSAT", None, 0.0
    with Solver(name=name, bootstrap_with=clauses) as s:
        budget = 20000
        while True:
            try:
                s.conf_budget(budget)
                r = s.solve_limited()
            except NotImplementedError:
                r = s.solve()
            if r is not None:
                return ("SAT", s.get_model() or [], time.perf_counter() - t0) if r else \
                       ("UNSAT", None, time.perf_counter() - t0)
            if time.perf_counter() - t0 > time_limit:
                return "UNKNOWN", None, time.perf_counter() - t0
            budget = min(budget * 2, 1_000_000)


# --------------------------------------------------------------------------- model check


def check_model(nvars: int, clauses: list[list[int]], lits: list[int], allow_partial: bool = False) -> tuple[str | None, str]:
    value: dict[int, bool] = {}
    for l in lits:
        v = abs(l)
        if v == 0 or v > nvars:
            return "model-invalid", f"literal {l} out of range 1..{nvars}"
        if value.get(v, l > 0) != (l > 0):
            return "model-invalid", f"variable {v} assigned both ways"
        value[v] = l > 0
    for i, c in enumerate(clauses):
        if not any(value.get(abs(l)) == (l > 0) for l in c):
            shown = " ".join(map(str, c[:12])) + (" ..." if len(c) > 12 else "")
            return "model-invalid", f"clause #{i + 1} ({shown}) not satisfied"
    if not allow_partial and len(value) < nvars:
        missing = next(v for v in range(1, nvars + 1) if v not in value)
        return "model-incomplete", f"{nvars - len(value)} of {nvars} variables unassigned (first: {missing})"
    return None, ""


# --------------------------------------------------------------------------- solver run


@dataclass
class Config:
    solver: list[str]                   # command prefix of the solver under test
    extra: list[str] = field(default_factory=list)  # options added to every run
    time_limit: float = 10.0            # passed as --time-limit; hard kill after kill_factor * limit + 2 s
    kill_factor: float = 1.5
    proof: bool = False                 # pass a proof file to the solver
    proof_style: str = "positional"     # positional (<input> <proof>) or option (--proof=<file>)
    checker: list[str] | None = None    # proof checker command prefix (None: no proof check)
    checker_label: str = "none"
    reference: str = "cadical195"
    ref_time_limit: float = 30.0
    allow_partial: bool = False         # accept models that leave variables unassigned
    tiny_fraction: float = 0.05         # UNKNOWN is a failure if the reference needed < this * time_limit
    mem_limit_mb: int = 2048            # RLIMIT_AS for the solver (Linux only)


def solver_command(cfg: Config, opts: list[str], cnf: Path, proof: Path | None) -> list[str]:
    tl = max(1, int(cfg.time_limit + 0.999))
    cmd = cfg.solver + cfg.extra + opts + [f"--time-limit={tl}"]
    if proof is not None and cfg.proof_style == "option":
        cmd.append(f"--proof={proof}")
    cmd.append(str(cnf))
    if proof is not None and cfg.proof_style == "positional":
        cmd.append(str(proof))
    return cmd


def _limit_memory(mb: int):
    if not sys.platform.startswith("linux") or mb <= 0:
        return None

    def fn():
        import resource
        resource.setrlimit(resource.RLIMIT_AS, (mb << 20, mb << 20))
    return fn


@dataclass
class Run:
    cmd: list[str]
    returncode: int | None
    stdout: str
    stderr: str
    seconds: float
    killed: bool


def run_solver(cfg: Config, cmd: list[str]) -> Run:
    hard = cfg.time_limit * cfg.kill_factor + 2.0
    t0 = time.perf_counter()
    p = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, stdin=subprocess.DEVNULL,
                         start_new_session=True, preexec_fn=_limit_memory(cfg.mem_limit_mb))
    killed = False
    try:
        out, err = p.communicate(timeout=hard)
    except subprocess.TimeoutExpired:
        killed = True
        try:
            os.killpg(p.pid, signal.SIGKILL)
        except ProcessLookupError:
            pass
        out, err = p.communicate()
    return Run(cmd, p.returncode, out.decode(errors="replace"), err.decode(errors="replace"),
               time.perf_counter() - t0, killed)


def parse_output(stdout: str, need_model: bool = True) -> tuple[str | None, list[int], str]:
    """(status, model literals, error). error != '' means malformed output."""
    status = None
    lits: list[int] = []
    ended = False
    for raw in stdout.splitlines():
        line = raw.rstrip()
        if not line:
            continue
        if line[0] == "c" and (len(line) == 1 or line[1] in " \t"):
            continue
        if line[0] == "s" and line[1:2] == " ":
            if status is not None:
                return None, [], "more than one s line"
            st = line[2:].strip()
            if st not in ("SATISFIABLE", "UNSATISFIABLE", "UNKNOWN"):
                return None, [], f"bad s line {line!r}"
            status = {"SATISFIABLE": "SAT", "UNSATISFIABLE": "UNSAT"}.get(st, "UNKNOWN")
            continue
        if line[0] == "v" and (len(line) == 1 or line[1] in " \t"):
            if status != "SAT":
                return None, [], "v line without a preceding 's SATISFIABLE'"
            for tok in line[1:].split():
                try:
                    x = int(tok)
                except ValueError:
                    return None, [], f"bad token {tok!r} in v line"
                if ended:
                    return None, [], "literals after the terminating 0"
                if x == 0:
                    ended = True
                else:
                    lits.append(x)
            continue
        return None, [], f"unexpected output line {line[:60]!r}"
    if status is None:
        return None, [], "no s line"
    if status == "SAT" and need_model and not ended:
        return None, [], "model missing or not terminated by 0" if lits else "no v lines"
    return status, lits, ""


def check_proof(cfg: Config, cnf: Path, proof: Path) -> tuple[str, str]:
    """('verified' | 'rejected' | 'timeout', detail)."""
    cmd = cfg.checker + [str(cnf), str(proof)]
    limit = max(10.0, 4 * cfg.time_limit)
    if cfg.checker_label in ("drat-trim", "dpr-trim"):
        cmd += ["-t", str(int(limit))]
    try:
        p = subprocess.run(cmd, capture_output=True, text=True, timeout=limit + 5)
    except subprocess.TimeoutExpired:
        return "timeout", "checker timed out"
    lines = [l.strip() for l in p.stdout.splitlines()]
    if "s VERIFIED" in lines:
        return "verified", ""
    if any("TIMEOUT" in l.upper() for l in lines if l.startswith(("c", "s"))) and "s NOT VERIFIED" not in lines:
        return "timeout", "checker timed out"
    tail = [l for l in lines if l][-3:] + [l.strip() for l in p.stderr.splitlines() if l.strip()][-2:]
    return "rejected", f"checker exit {p.returncode}: " + " | ".join(tail)[:300]


# --------------------------------------------------------------------------- the check


@dataclass
class Outcome:
    kind: str | None
    detail: str = ""
    status: str | None = None        # solver status SAT/UNSAT/UNKNOWN (None if unparsable)
    ref: str | None = None           # reference status (None if not run)
    exit_code: int | None = None
    seconds: float = 0.0
    ref_seconds: float = 0.0
    proof: str | None = None         # verified / rejected / timeout / trivial / skipped / None
    cmd: list[str] = field(default_factory=list)


def check(nvars: int, clauses: list[list[int]], cfg: Config, opts: list[str], workdir: Path,
          need_ref: bool = True, check_proof_now: bool = True, expected: str | None = None) -> Outcome:
    """Run the solver on the formula and classify the result (see KINDS).
    The formula is written without comments, so the solver input depends only
    on (nvars, clauses) and a saved failure reproduces byte for byte."""
    workdir = Path(workdir)
    cnf = workdir / "formula.cnf"
    write_dimacs(cnf, nvars, clauses)
    proof = workdir / "proof.drat" if cfg.proof else None
    if proof is not None and proof.exists():
        proof.unlink()

    ref, ref_model, ref_seconds = (None, None, 0.0)
    if need_ref:
        ref, ref_model, ref_seconds = reference_solve(clauses, cfg.reference, cfg.ref_time_limit)
        if ref == "SAT":
            k, d = check_model(nvars, clauses, ref_model, allow_partial=True)
            if k:
                return Outcome("reference-wrong", f"reference model invalid: {d}", ref=ref)
        if expected and ref in ("SAT", "UNSAT") and ref != expected:
            return Outcome("reference-wrong", f"generator expects {expected}, reference says {ref}", ref=ref)

    cmd = solver_command(cfg, opts, cnf, proof)
    r = run_solver(cfg, cmd)
    o = Outcome(None, ref=ref, exit_code=r.returncode, seconds=r.seconds, ref_seconds=ref_seconds, cmd=cmd)

    def fail(kind: str, detail: str) -> Outcome:
        o.kind, o.detail = kind, detail
        return o

    err_tail = " | ".join(l.strip() for l in r.stderr.splitlines() if l.strip())[-200:]
    if r.killed:
        return fail("hang", f"killed after {r.seconds:.1f}s (time limit {cfg.time_limit:g}s)")
    san = next((l.strip() for l in r.stderr.splitlines() if any(m in l for m in SANITIZER_MARKERS)), None)
    if san:
        return fail("sanitizer", san[:200])
    rc = r.returncode
    if rc < 0 or (rc > 128 and rc - 128 in {int(s) for s in CRASH_SIGNALS}):
        sig = -rc if rc < 0 else rc - 128
        try:
            name = signal.Signals(sig).name
        except ValueError:
            name = f"signal {sig}"
        return fail("crash", f"{name}" + (f"; stderr: {err_tail}" if err_tail else ""))
    if rc == 1:
        return fail("error", f"exit 1; stderr: {err_tail or '(empty)'}")

    need_model = not any(a in ("-n", "--no-model") for a in cfg.extra + opts)
    status, lits, perr = parse_output(r.stdout, need_model)
    o.status = status
    if perr:
        return fail("garbage", perr)
    want = {"SAT": 10, "UNSAT": 20, "UNKNOWN": 0}[status]
    if rc != want:
        return fail("exit-code", f"exit {rc} with s {status}")

    if status == "SAT":
        if need_model:
            k, d = check_model(nvars, clauses, lits, cfg.allow_partial)
            if k:
                return fail(k, d)
            if ref == "UNSAT" or expected == "UNSAT":
                who = "reference" if ref == "UNSAT" else "generator"
                return fail("reference-wrong", f"verified model, but {who} says UNSAT")
        elif ref == "UNSAT" or expected == "UNSAT":
            return fail("disagree", "SAT (no model printed), reference UNSAT")
    elif status == "UNSAT":
        if ref == "SAT":
            return fail("disagree", "UNSAT, reference found a verified model")
        if expected == "SAT":
            return fail("disagree", "UNSAT, formula SAT by construction")
        if cfg.proof:
            if any(len(c) == 0 for c in clauses):
                o.proof = "trivial"
            elif not proof.exists():
                return fail("proof-missing", "no proof file written")
            elif cfg.checker and check_proof_now:
                verdict, d = check_proof(cfg, cnf, proof)
                o.proof = verdict
                if verdict == "rejected":
                    return fail("proof-rejected", d)
            else:
                o.proof = "skipped"
    else:  # UNKNOWN
        if (r.seconds >= 0.8 * cfg.time_limit and ref in ("SAT", "UNSAT")
                and ref_seconds < cfg.tiny_fraction * cfg.time_limit):
            return fail("timeout", f"UNKNOWN after {r.seconds:.1f}s; reference {ref} in {ref_seconds * 1000:.0f} ms")
    return o


def shell_join(cmd: list[str]) -> str:
    return " ".join(shlex.quote(c) for c in cmd)
