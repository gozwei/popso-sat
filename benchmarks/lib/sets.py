"""Instance list files (benchmarks/sets/<name>.txt) and expected statuses.

Set file format, one instance per line:

    <path> [sat|unsat|unknown]   [# comment]

<path> is relative to the repository (committed instances: 'benchmarks/instances/...') or to the
cache directory (downloaded / generated: 'satlib/...', 'gbd/...', 'generated/...').  A line
'@include <other set>' includes another set.  Blank lines and '#' comments are ignored.

Expected status precedence (run.py): the set file, then benchmarks/reference/status.json.
"""

from __future__ import annotations

import json
from dataclasses import dataclass
from pathlib import Path

from . import paths

STATUSES = ("sat", "unsat", "unknown")


@dataclass
class Entry:
    key: str                  # the path as written (repo- or cache-relative), the instance id
    path: Path                # resolved file
    expected: str | None      # 'sat' / 'unsat' / None
    comment: str = ""


def set_path(spec: str) -> Path:
    p = Path(spec)
    if p.exists():
        return p
    return paths.SETS / (spec if spec.endswith(".txt") else spec + ".txt")


def read_set(spec: str, _seen=None) -> list[Entry]:
    p = set_path(spec)
    if not p.exists():
        raise FileNotFoundError(f"set {spec!r} not found (looked for {paths.portable(p)})")
    seen = _seen if _seen is not None else set()
    rp = p.resolve()
    if rp in seen:
        return []
    seen.add(rp)
    out: list[Entry] = []
    for ln in p.read_text().splitlines():
        body, _, comment = ln.partition("#")
        f = body.split()
        if not f:
            continue
        if f[0] == "@include":
            for sub in f[1:]:
                out += read_set(sub, seen)
            continue
        st = None
        if len(f) > 1:
            s = f[1].lower()
            if s not in STATUSES:
                raise ValueError(f"{p.name}: bad status {f[1]!r} in line {ln!r}")
            st = None if s == "unknown" else s
        out.append(Entry(key=f[0], path=paths.resolve_instance(f[0]), expected=st,
                         comment=comment.strip()))
    return out


def write_set(path: Path, entries, header=()):
    """entries: iterable of (key, status or None, comment)."""
    lines = [f"# {h}" if h else "#" for h in header]
    rows = [(k, s or "unknown", c) for k, s, c in entries]
    w = max((len(k) for k, _, _ in rows), default=10)
    for k, s, c in rows:
        lines.append(f"{k:<{w}}  {s:<7}" + (f"  # {c}" if c else "").rstrip())
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text("\n".join(x.rstrip() for x in lines) + "\n")


def load_reference(path: Path | None = None) -> dict:
    """benchmarks/reference/status.json -> {key: entry}; entry has 'status' (sat/unsat/unknown)."""
    p = path or (paths.REFERENCE / "status.json")
    if not p.exists():
        return {}
    d = json.loads(p.read_text())
    return d.get("instances", {})
