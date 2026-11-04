"""DIMACS CNF reading (streaming, .cnf / .cnf.gz / .cnf.xz / .cnf.bz2) and writing.

The reader is deliberately independent of the solver's C++ parser: it is used to verify models
against the original formula.  Accepted input:
  * comment lines starting with 'c' (anywhere), one 'p cnf <vars> <clauses>' header,
  * clauses as whitespace-separated literals terminated by 0, possibly spanning lines,
  * a line starting with '%' ends the formula (old SATLIB files end with '%' and '0').
"""

from __future__ import annotations

import bz2
import gzip
import io
import lzma
import os
from pathlib import Path
from typing import Iterator

CHUNK = 1 << 22
COMPRESSED = (".gz", ".xz", ".lzma", ".bz2")


class DimacsError(ValueError):
    pass


def open_binary(path) -> io.BufferedIOBase:
    p = str(path)
    if p.endswith(".gz"):
        return gzip.open(p, "rb")
    if p.endswith(".xz") or p.endswith(".lzma"):
        return lzma.open(p, "rb")
    if p.endswith(".bz2"):
        return bz2.open(p, "rb")
    return open(p, "rb")


def instance_name(path) -> str:
    """File name without .cnf and compression suffixes."""
    n = Path(path).name
    for ext in COMPRESSED:
        if n.endswith(ext):
            n = n[: -len(ext)]
            break
    for ext in (".cnf", ".dimacs"):
        if n.endswith(ext):
            n = n[: -len(ext)]
            break
    return n


class CnfStream:
    """Iterate the clauses of a DIMACS file without keeping them in memory.

        s = CnfStream(path)
        for clause in s: ...          # lists of ints, without the terminating 0
        s.nvars, s.nclauses           # header values (None if there is no header)
        s.max_var, s.count            # largest variable seen, clauses read

    A missing final 0 before end of file is accepted (the pending literals form the last
    clause), as most solvers do.  Errors raise DimacsError.
    """

    def __init__(self, path):
        self.path = path
        self.nvars: int | None = None
        self.nclauses: int | None = None
        self.max_var = 0
        self.count = 0
        self.comments: list[str] = []
        self.keep_comments = 50  # first N comment lines are kept (generator/provenance info)

    def _tokens(self) -> Iterator[list[int]]:
        """Yield lists of literal ints (chunks), handling comment/header/'%' lines."""
        with open_binary(self.path) as fh:
            rest = b""
            done = False
            while not done:
                chunk = fh.read(CHUNK)
                if not chunk:
                    data, rest, done = rest, b"", True
                else:
                    data = rest + chunk
                    cut = data.rfind(b"\n")
                    if cut < 0:
                        rest = data
                        continue
                    data, rest = data[: cut + 1], data[cut + 1:]
                if not data:
                    continue
                special = (data[:1] in (b"c", b"p", b"%") or b"\nc" in data or b"\np" in data
                           or b"\n%" in data or b"\r" in data)
                if not special:
                    yield self._ints(data)
                    continue
                buf = []
                for line in data.splitlines():
                    s = line.lstrip()
                    if not s:
                        continue
                    c = s[:1]
                    if c == b"c":
                        if len(self.comments) < self.keep_comments:
                            self.comments.append(s[1:].strip().decode("utf-8", "replace"))
                        continue
                    if c == b"p":
                        if buf:
                            yield self._ints(b" ".join(buf))
                            buf = []
                        self._header(s)
                        continue
                    if c == b"%":
                        done = True
                        break
                    buf.append(s)
                if buf:
                    yield self._ints(b" ".join(buf))

    def _ints(self, data: bytes) -> list[int]:
        try:
            return [int(t) for t in data.split()]
        except ValueError:
            bad = next(t for t in data.split() if not _is_int(t))
            raise DimacsError(f"{self.path}: unexpected token {bad[:40]!r}") from None

    def _header(self, line: bytes):
        f = line.split()
        if self.nvars is not None:
            raise DimacsError(f"{self.path}: second 'p' line")
        if len(f) != 4 or f[1] != b"cnf":
            raise DimacsError(f"{self.path}: bad header {line[:80]!r}")
        try:
            self.nvars, self.nclauses = int(f[2]), int(f[3])
        except ValueError:
            raise DimacsError(f"{self.path}: bad header {line[:80]!r}") from None
        if self.nvars < 0 or self.nclauses < 0:
            raise DimacsError(f"{self.path}: negative counts in header")

    def __iter__(self) -> Iterator[list[int]]:
        """Clauses as lists of ints.  self.max_var is updated before each clause is yielded."""
        cur: list[int] = []
        for toks in self._tokens():
            if self.nvars is None:
                raise DimacsError(f"{self.path}: clause before the 'p cnf' header")
            start = 0
            while True:
                try:
                    z = toks.index(0, start)
                except ValueError:
                    cur.extend(toks[start:])
                    break
                cur.extend(toks[start:z])
                start = z + 1
                if cur:
                    m = max(cur)
                    if m > self.max_var:
                        self.max_var = m
                    m = -min(cur)
                    if m > self.max_var:
                        self.max_var = m
                self.count += 1
                yield cur
                cur = []
        if cur:
            self.max_var = max(self.max_var, max(cur), -min(cur))
            self.count += 1
            yield cur
        if self.nvars is None:
            raise DimacsError(f"{self.path}: no 'p cnf' header")


def _is_int(t: bytes) -> bool:
    try:
        int(t)
        return True
    except ValueError:
        return False


def read_cnf(path):
    """Whole formula in memory: (nvars, clauses).  For small and medium files only."""
    s = CnfStream(path)
    clauses = list(s)
    return max(s.nvars or 0, s.max_var), clauses


def header(path):
    """(nvars, nclauses) from the header, reading only up to it."""
    with open_binary(path) as fh:
        for raw in fh:
            s = raw.strip()
            if s.startswith(b"p"):
                f = s.split()
                if len(f) == 4 and f[1] == b"cnf":
                    return int(f[2]), int(f[3])
                raise DimacsError(f"{path}: bad header {s[:80]!r}")
            if s and not s.startswith(b"c"):
                break
    raise DimacsError(f"{path}: no 'p cnf' header")


def format_cnf(nvars: int, clauses, comments=()) -> bytes:
    out = io.StringIO()
    for c in comments:
        for ln in str(c).splitlines() or [""]:
            out.write(f"c {ln}\n" if ln else "c\n")
    clauses = list(clauses)
    out.write(f"p cnf {nvars} {len(clauses)}\n")
    for cl in clauses:
        out.write(" ".join(map(str, cl)))
        out.write(" 0\n" if cl else "0\n")
    return out.getvalue().encode()


def write_cnf(path, nvars: int, clauses, comments=()) -> Path:
    """Write a DIMACS file; '.gz' paths are gzip-compressed deterministically (no mtime/name)."""
    path = Path(path)
    data = format_cnf(nvars, clauses, comments)
    path.parent.mkdir(parents=True, exist_ok=True)
    tmp = path.with_name(path.name + ".tmp")
    if path.name.endswith(".gz"):
        with open(tmp, "wb") as raw, gzip.GzipFile(filename="", mode="wb", fileobj=raw, mtime=0,
                                                  compresslevel=9) as gz:
            gz.write(data)
    else:
        tmp.write_bytes(data)
    os.replace(tmp, path)
    return path
