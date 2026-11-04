"""Path conventions (worktree-safe).

* REPO: the checkout this file lives in (a git worktree or the main checkout).  Code, committed
  instances, set files, the reference status file and results/ belong to it.
* MAIN: the main checkout, i.e. the parent of `git rev-parse --git-common-dir`, or $PSAT_ROOT.
  Large or derived data is shared between all worktrees and lives there (gitignored):
    <main>/benchmarks/cache/            downloaded and generated instances (CACHE)
    <main>/benchmarks/tools/build/bin/  reference binaries such as drat-trim (TOOLS_BIN)
  $PSAT_CACHE and $PSAT_TOOLS_BIN override the two directories individually.
* RESULTS: <repo>/benchmarks/results/ (gitignored); $PSAT_RESULTS overrides it.

Paths written into committed files or result files are always relative (to REPO or CACHE),
never absolute local paths.
"""

from __future__ import annotations

import functools
import os
import re
import subprocess
from pathlib import Path

BENCH = Path(__file__).resolve().parents[1]
REPO = BENCH.parent
SETS = BENCH / "sets"
INSTANCES = BENCH / "instances"
REFERENCE = BENCH / "reference"


@functools.lru_cache(maxsize=None)
def main_root() -> Path:
    env = os.environ.get("PSAT_ROOT")
    if env:
        return Path(env).expanduser().resolve()
    try:
        # (without --path-format=absolute, which needs git >= 2.31; a relative answer is
        # relative to the working directory, i.e. REPO)
        out = subprocess.run(["git", "rev-parse", "--git-common-dir"],
                             cwd=REPO, capture_output=True, text=True, timeout=10)
        if out.returncode == 0 and out.stdout.strip():
            return (REPO / out.stdout.strip()).resolve().parent
    except (OSError, subprocess.SubprocessError):
        pass
    return REPO


def cache_dir() -> Path:
    env = os.environ.get("PSAT_CACHE")
    return Path(env).expanduser().resolve() if env else main_root() / "benchmarks" / "cache"


def tools_bin() -> Path:
    env = os.environ.get("PSAT_TOOLS_BIN")
    return Path(env).expanduser().resolve() if env else main_root() / "benchmarks" / "tools" / "build" / "bin"


def results_dir() -> Path:
    env = os.environ.get("PSAT_RESULTS")
    return Path(env).expanduser().resolve() if env else BENCH / "results"


def default_solver() -> Path:
    return REPO / "build" / "popso-sat"


def drat_trim() -> Path | None:
    p = tools_bin() / "drat-trim"
    return p if p.exists() and os.access(p, os.X_OK) else None


def resolve_instance(rel: str) -> Path:
    """Instance path from a set file: absolute, or relative to the repository, or relative to
    the cache directory (first existing wins; the cache path is returned if neither exists)."""
    p = Path(rel)
    if p.is_absolute():
        return p
    for base in (REPO, cache_dir()):
        q = base / p
        if q.exists():
            return q
    return cache_dir() / p


def portable(path) -> str:
    """Instance key / path for files and messages: relative to the repo (committed files start
    with 'benchmarks/'), else relative to the cache (as written in set files: 'satlib/...',
    'gbd/...', 'generated/...'), else '<main>/<rel>', else the bare file name.  Never an
    absolute local path."""
    p = Path(os.path.abspath(path))
    for base, prefix in ((cache_dir(), ""), (REPO, ""), (main_root(), "<main>/")):
        for cand in (p, p.resolve()):
            try:
                return prefix + cand.relative_to(base).as_posix()
            except ValueError:
                pass
    return p.name


_TMP_RX = re.compile(r"(?:/private)?(?:/tmp|/var/folders)/\S*?([^/\s]+)(?=\s|$)")


def strip_local(s: str) -> str:
    """Remove local directory prefixes from a command string or message: cache, repository,
    main checkout and home become 'cache:', '', '<main>/', '~/'; a path in a temporary
    directory becomes '<tmp>/<file name>'."""
    s = _TMP_RX.sub(lambda m: "<tmp>/" + m.group(1), s)
    for base, repl in ((cache_dir(), "cache:"), (REPO, ""), (main_root(), "<main>/"), (Path.home(), "~/")):
        s = s.replace(str(base) + os.sep, repl)
    return s
