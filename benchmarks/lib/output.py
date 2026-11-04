"""Parsing of SAT Competition solver output.

    c <comment>                  any number
    s SATISFIABLE | s UNSATISFIABLE | s UNKNOWN     exactly one
    v <lit> <lit> ... 0          the model (SAT only), possibly over many lines, ends with 0
Exit codes 10 (SAT), 20 (UNSAT), 0 (unknown) are checked against the 's' line by the caller.
"""

from __future__ import annotations

import re
from dataclasses import dataclass, field

SAT = "SAT"
UNSAT = "UNSAT"
UNKNOWN = "UNKNOWN"

_S = {"SATISFIABLE": SAT, "UNSATISFIABLE": UNSAT, "UNKNOWN": UNKNOWN}
EXIT_CODE = {SAT: 10, UNSAT: 20, UNKNOWN: 0}

# hints in comment / error lines that the solver stopped because of memory
_MEM_RX = re.compile(rb"(out of memory|memory limit|mem(ory)?[ -]?out|bad_alloc|cannot allocate|"
                     rb"MemoryError|memlimit)", re.I)


@dataclass
class SolverOutput:
    status: str | None = None          # SAT / UNSAT / UNKNOWN / None (no 's' line)
    raw_status: str | None = None
    model: list[int] = field(default_factory=list)
    model_terminated: bool = False     # the 'v' lines ended with 0
    errors: list[str] = field(default_factory=list)
    memory_hint: bool = False          # a line mentions memory exhaustion
    v_lines: int = 0


def parse_output(fh) -> SolverOutput:
    """Parse solver stdout from a binary file object."""
    out = SolverOutput()
    lits: list[int] = []
    for raw in fh:
        line = raw.strip()
        if not line:
            continue
        tag = line[:1]
        if tag == b"c":
            if not out.memory_hint and _MEM_RX.search(line):
                out.memory_hint = True
            continue
        if tag == b"s" and (len(line) == 1 or line[1:2] in (b" ", b"\t")):
            word = line[1:].strip().decode("ascii", "replace")
            if out.raw_status is not None:
                out.errors.append(f"second 's' line: {word!r}")
                continue
            out.raw_status = word
            out.status = _S.get(word)
            if out.status is None:
                out.errors.append(f"unknown status line 's {word}'")
            continue
        if tag == b"v" and (len(line) == 1 or line[1:2] in (b" ", b"\t")):
            out.v_lines += 1
            if out.model_terminated:
                out.errors.append("'v' line after the terminating 0")
                continue
            try:
                toks = [int(t) for t in line[1:].split()]
            except ValueError:
                out.errors.append(f"non-integer in 'v' line: {line[:60]!r}")
                continue
            if 0 in toks:
                z = toks.index(0)
                if z != len(toks) - 1:
                    out.errors.append("literals after the terminating 0")
                lits.extend(toks[:z])
                out.model_terminated = True
            else:
                lits.extend(toks)
            continue
        if _MEM_RX.search(line):
            out.memory_hint = True
        # other lines (e.g. stray debug output) are tolerated
    out.model = lits
    return out
