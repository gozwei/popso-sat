"""Model verification against the original formula (streaming: memory O(variables)).

A model is the list of literals from the solver's 'v' lines.  It is valid when
  * no variable occurs with both signs (contradiction -> invalid),
  * every clause of the formula contains a literal of the model.
Variables of the formula that the model does not mention are reported (`missing`); they do not
make the model invalid as long as every clause is satisfied by the listed literals (a partial
assignment that satisfies all clauses is a valid certificate).  Literals of variables beyond the
formula are reported as `extra` (a warning only).
"""

from __future__ import annotations

from dataclasses import asdict, dataclass

from .dimacs import CnfStream, DimacsError


@dataclass
class Verification:
    ok: bool
    message: str = ""
    nvars: int = 0                 # header
    nclauses: int = 0              # header
    clauses_read: int = 0
    falsified: int = 0             # clauses not satisfied by the model
    first_falsified: int = -1      # 0-based index of the first one
    first_falsified_clause: list | None = None
    contradictions: int = 0        # variables listed with both signs
    duplicates: int = 0            # literals listed twice
    missing: int = 0               # variables 1..max(nvars, max var in formula) not in the model
    extra: int = 0                 # literals of variables beyond the formula
    formula_error: str = ""        # the file could not be read (then ok is False)

    def to_dict(self):
        return asdict(self)


def verify_model(path, model) -> Verification:
    lits = model
    nv_model = max((abs(x) for x in lits), default=0)
    try:
        stream = CnfStream(path)
        it = iter(stream)
        first = next(it, None)  # reads the header
    except (DimacsError, OSError, EOFError, ValueError) as e:
        return Verification(ok=False, message=f"cannot read formula: {e}", formula_error=str(e))
    nvars = stream.nvars or 0
    n = max(nvars, nv_model, stream.max_var)
    # tl[n + lit] == 1  <=>  literal lit is true in the model
    tl = bytearray(2 * n + 1)
    contradictions = duplicates = 0
    for x in lits:
        if tl[n + x]:
            duplicates += 1
            continue
        if tl[n - x]:
            contradictions += 1
        tl[n + x] = 1
    falsified = 0
    first_idx, first_cl = -1, None
    idx = 0
    try:
        if first is not None:
            for cl in _chain(first, it):
                if stream.max_var > n:
                    # formula variable beyond header and model: grow the table (unassigned)
                    m = stream.max_var
                    new = bytearray(2 * m + 1)
                    new[m - n: m + n + 1] = tl
                    tl, n = new, m
                for x in cl:
                    if tl[n + x]:
                        break
                else:
                    if falsified == 0:
                        first_idx, first_cl = idx, cl[:20]
                    falsified += 1
                idx += 1
    except (DimacsError, OSError, EOFError, ValueError) as e:
        return Verification(ok=False, message=f"cannot read formula: {e}", formula_error=str(e))
    fv = max(nvars, stream.max_var)
    assigned = sum(1 for v in range(1, fv + 1) if tl[n + v] or tl[n - v])
    extra = sum(1 for x in lits if abs(x) > fv)
    v = Verification(ok=(falsified == 0 and contradictions == 0), nvars=nvars,
                     nclauses=stream.nclauses or 0, clauses_read=stream.count, falsified=falsified,
                     first_falsified=first_idx, first_falsified_clause=first_cl,
                     contradictions=contradictions, duplicates=duplicates,
                     missing=fv - assigned, extra=extra)
    msgs = []
    if contradictions:
        msgs.append(f"{contradictions} variable(s) assigned both ways")
    if falsified:
        msgs.append(f"{falsified} clause(s) falsified, first #{first_idx}: {first_cl}")
    if v.ok:
        notes = []
        if v.missing:
            notes.append(f"{v.missing} variable(s) unassigned")
        if v.extra:
            notes.append(f"{v.extra} literal(s) beyond the formula's variables")
        if v.duplicates:
            notes.append(f"{v.duplicates} duplicate literal(s)")
        msgs = notes
    v.message = "; ".join(msgs)
    return v


def _chain(first, rest):
    yield first
    yield from rest
