"""UNSAT proof checking: drat-trim (external binary) or pydrat (pure-Python fallback).

    drat-trim <plain.cnf> <proof> -t <seconds>          <main>/benchmarks/tools/build/bin/drat-trim
    python benchmarks/tools/pydrat.py <cnf> <proof> -t <seconds>
Both print 's VERIFIED' when the proof refutes the formula and 's NOT VERIFIED' otherwise and
detect binary/text DRAT themselves.  drat-trim reads plain DIMACS only, so a compressed formula
is decompressed to a temporary file first.

Checker selection (run.py --checker): 'auto' (default) = drat-trim if built, else pydrat for
proofs up to --pydrat-max-mb (larger proofs stay 'unchecked'); 'drat-trim', 'pydrat', 'none',
or a path to another drat-trim-compatible binary.

Proof status values:
  verified        the checker accepted the proof
  rejected        the checker rejected it (the UNSAT claim is not certified: counted WRONG)
  proof-timeout   the checker ran out of time (not WRONG; counts as unchecked for --strict)
  proof-memlimit  the checker exceeded the memory cap (likewise)
  proof-error     the checker crashed or printed no verdict (likewise)
  missing         the solver claimed UNSAT but wrote no proof file (likewise)
  unchecked       no checker available / proof too large for pydrat / checking disabled
"""

from __future__ import annotations

import shutil
import subprocess
import sys
from pathlib import Path

from . import paths
from .dimacs import COMPRESSED, open_binary
from .proc import run_capped

VERIFIED = "verified"
REJECTED = "rejected"
TIMEOUT = "proof-timeout"
MEMLIMIT = "proof-memlimit"
ERROR = "proof-error"
MISSING = "missing"
UNCHECKED = "unchecked"

PYDRAT = paths.BENCH / "tools" / "pydrat.py"


class Checker:
    """A resolved checker: name ('drat-trim' / 'pydrat' / file name), argv prefix, and whether
    it needs a plain (uncompressed) formula."""

    def __init__(self, name, argv, needs_plain, max_mb=None):
        self.name, self.argv, self.needs_plain, self.max_mb = name, argv, needs_plain, max_mb


def resolve_checker(spec: str | None, pydrat_max_mb: float):
    """None if checking is off / impossible."""
    if spec in (None, "", "none"):
        return None
    if spec == "auto":
        dt = paths.drat_trim()
        if dt:
            return Checker("drat-trim", [str(dt)], True)
        return Checker("pydrat", [sys.executable, str(PYDRAT)], False, pydrat_max_mb)
    if spec == "pydrat":
        return Checker("pydrat", [sys.executable, str(PYDRAT)], False, pydrat_max_mb)
    if spec == "drat-trim":
        dt = paths.drat_trim()
        if not dt:
            raise FileNotFoundError(f"drat-trim not found in {paths.strip_local(str(paths.tools_bin()))}/")
        return Checker("drat-trim", [str(dt)], True)
    p = Path(spec)
    if not p.exists():
        raise FileNotFoundError(f"checker not found: {spec}")
    return Checker(p.name, [str(p.resolve())], True)


def plain_copy(cnf: Path, tmpdir: Path) -> Path:
    """The formula as a plain DIMACS file (decompressed into tmpdir if needed)."""
    if not str(cnf).endswith(COMPRESSED):
        return cnf
    out = tmpdir / (cnf.name.rsplit(".", 1)[0])
    if not out.exists():
        with open_binary(cnf) as src, open(out, "wb") as dst:
            shutil.copyfileobj(src, dst, 1 << 22)
    return out


def check_proof(checker: Checker, cnf: Path, proof: Path, time_limit: float, mem_mb, tmpdir: Path,
                extra=()) -> tuple[str, str, float]:
    """Returns (status, message, seconds)."""
    if not proof.exists():
        return MISSING, "no proof file written", 0.0
    if checker.max_mb is not None and proof.stat().st_size > checker.max_mb * 1048576:
        return UNCHECKED, f"proof {proof.stat().st_size / 1048576:.1f} MB > {checker.max_mb:g} MB (pydrat limit)", 0.0
    plain = plain_copy(cnf, tmpdir) if checker.needs_plain else cnf
    log = tmpdir / (proof.name + ".check.log")
    cmd = checker.argv + [str(plain), str(proof), "-t", str(int(max(1, time_limit)))] + list(extra)
    with open(log, "wb") as fh:
        r = run_capped(cmd, time_limit + max(5.0, 0.1 * time_limit), mem_mb, stdout=fh,
                       stderr=subprocess.STDOUT)
    text = log.read_text(errors="replace")
    log.unlink(missing_ok=True)
    if plain != cnf:
        plain.unlink(missing_ok=True)
    if r.reason == "memlimit":
        return MEMLIMIT, f"checker above {mem_mb} MB", r.wall
    if r.reason == "timeout":
        return TIMEOUT, f"checker killed after {r.wall:.0f} s", r.wall
    lines = [ln.strip() for ln in text.splitlines()]
    if "s VERIFIED" in lines:
        return VERIFIED, "", r.wall
    low = text.lower()
    if "timeout" in low or "time limit" in low:
        return TIMEOUT, "checker time limit", r.wall
    if "s NOT VERIFIED" in lines:
        info = [ln for ln in lines if ln and ln != "s NOT VERIFIED"][-3:]
        return REJECTED, f"{checker.name}: NOT VERIFIED; " + " | ".join(info)[:300], r.wall
    return ERROR, f"checker exit {r.returncode}: " + " | ".join(lines[-3:])[:300], r.wall
