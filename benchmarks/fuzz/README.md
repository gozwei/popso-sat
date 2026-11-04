# Fuzzing and delta debugging

Random CNF fuzzing of popso-sat against a reference solver (PySAT), plus delta
debugging of failing formulas. Self-contained: the tools here only need Python 3.10+
and `python-sat` (the repo venv: `.venv/bin/python`, `pip install python-sat`).

| file | what |
|---|---|
| `gen.py` | deterministic (seeded) CNF generators: random k-SAT, mixed lengths, cnfuzz-style layered formulas, edge cases, pigeonhole, parity |
| `fuzz.py` | the fuzz loop: generate, solve with the reference, run the solver under test, check, save and shrink failures |
| `ddmin.py` | delta debugging of a failing CNF (clauses, then literals, then variable renumbering) |
| `fuzzlib.py` | shared code: solver runs, output parsing, model and proof checks, the failure classification |
| `buggy_solver.py` | a stand-in implementing the popso-sat CLI on top of PySAT, with injectable bugs (to validate the tools) |
| `selftest.py` | runs fuzz.py + ddmin against every injectable bug and a clean stand-in; expects each bug found, no false alarms |
| `rupcheck.py` | minimal RUP proof checker on PySAT, a fallback when drat-trim is not built (RUP only, no RAT) |

Failures go to `benchmarks/fuzz/failures/` (gitignored; `--failures-dir` to change).

## Quick start

```sh
cmake -S . -B build -DCMAKE_BUILD_TYPE=Release && cmake --build build -j 4
.venv/bin/python benchmarks/fuzz/fuzz.py                       # 1000 formulas, -j 2
.venv/bin/python benchmarks/fuzz/fuzz.py --time-budget 600 -j 4 --shrink
.venv/bin/python benchmarks/fuzz/fuzz.py --seed 1000000 --count 100000 --extra '--some-option=1'
```

The solver is called per the CLI contract in PLAN.md:
`<solver> <extra...> <fuzzed options...> --seed=<n> --time-limit=<sec> <formula.cnf> [<proof>]`.
`--solver` takes a shell-quoted command (default `<checkout>/build/popso-sat`), so a
wrapper or an interpreter works, e.g. `--solver 'nice -n 10 build-asan/popso-sat'`.
`--no-seed` drops `--seed`, `--proof-style option` passes `--proof=<file>` instead of
the positional proof argument.

Resource rules (shared machine): `-j` defaults to 2 and is capped at 4; each run has a
time limit (`-t`, default 10 s) and is killed at 1.5 x limit + 2 s; on Linux the solver
gets a 2 GB address-space limit. `--shrink` runs ddmin after the fuzz loop (with `-j`
parallel runs), so it never overlaps the fuzz workers.

## What is checked

Each formula is solved by the reference (`--reference`, default `cadical195`, run
in-process, time-limited through conflict budgets) and by the solver under test. The
result is classified (first match wins):

| kind | meaning |
|---|---|
| `hang` | had to be killed (did not honour `--time-limit`) |
| `sanitizer` | an ASan / UBSan / LSan / TSan / MSan report on stderr (for sanitizer builds: `--solver build-asan/popso-sat`) |
| `crash` | killed by a signal (SIGSEGV, SIGABRT, ...; also shell-style exit 128+n) |
| `error` | exit code 1 on a valid formula |
| `garbage` | malformed output: no or several `s` lines, `v` lines without `s SATISFIABLE`, bad tokens, missing terminating `0`, unknown line types |
| `exit-code` | exit code does not match the `s` line (10 / 20 / 0) |
| `model-invalid` | the model falsifies a clause, or has out-of-range or contradictory literals |
| `model-incomplete` | the model does not assign every variable 1..n of the header (`--allow-partial-model` to accept) |
| `disagree` | `s UNSATISFIABLE`, but the reference found a model (which is verified), or the formula is SAT by construction; or SAT without a model (`-n`) on an UNSAT formula |
| `proof-missing` | UNSAT, a proof was requested, no proof file |
| `proof-rejected` | UNSAT and the proof checker does not print `s VERIFIED` |
| `timeout` | `s UNKNOWN` after the full time limit on a formula the reference solved in < 5% of it |
| `reference-wrong` | sanity check of the oracle: a verified model contradicts the reference or the generator's known status |

An `s UNKNOWN` that arrives early (e.g. a fuzzed `--conflicts` limit) is counted, not
flagged. Proofs: `--checker auto` (default) uses drat-trim from
`benchmarks/tools/build/bin/drat-trim`, looked up in this checkout and in the main
checkout (parent of `git rev-parse --git-common-dir`); without it proof checks are
skipped and the run says so once. `--checker rupcheck` uses the slow Python fallback;
`--checker '<cmd>'` any drat-trim-compatible command (`<cmd> <cnf> <proof>`, prints
`s VERIFIED`). `--proof always` requests proofs even without a checker (exercises the
proof writer; only `proof-missing` is then detected). Formulas containing the empty
clause are not proof-checked (`trivial`).

On a failure fuzz.py prints one line, saves `failures/<kind>-s<seed>.cnf` (the formula,
with `c fuzz-*` header lines recording kind, detail, solver, options, proof mode, time
limit) and a `.json` with the same plus timings and a replay command line, and
continues. With `--shrink` the first failure of each kind is minimized after the loop to
`failures/<kind>-s<seed>.min.cnf` (`--shrink-all`: every failure; `--stop-after 1
--shrink` = find one bug and minimize it). The summary lists formulas run, SAT / UNSAT / UNKNOWN counts of the
solver and the reference, proof verdicts, failures by kind and formulas per second. The
exit code is 1 if anything failed.

Everything is a function of the seed: the formula (`gen.generate(seed)`), the solver
`--seed` and the fuzzed options, so `fuzz.py --seed <s> --count 1 <same flags>`
reproduces a failure. The solver input is written without comments, so it depends only on
the formula.

## Generators (`gen.py`)

```sh
.venv/bin/python benchmarks/fuzz/gen.py --list
.venv/bin/python benchmarks/fuzz/gen.py --seed 42                 # one formula to stdout
.venv/bin/python benchmarks/fuzz/gen.py --seed 0 --count 500 --outdir /some/dir
.venv/bin/python benchmarks/fuzz/gen.py --stats --count 3000      # mix, SAT/UNSAT balance, reference time
```

| family | share | shape |
|---|---|---|
| `ksat` | 38% | uniform random k-SAT, k = 2..5 (weights 1:6:2:1), n log-uniform in 5..200 (k=4: ..70, k=5: ..45), density 0.85..1.15 x threshold (2-SAT 0.9..1.6) |
| `mixed` | 10% | clause lengths 1..7 with random weights, density from the harmonic mixture of the k thresholds |
| `layered` | 32% | cnfuzz-style: 1..10 layers of 5..40 variables; clauses of a layer take literals from the layer or (geometrically) earlier layers; lengths from 2 or 3 growing geometrically up to 10; half of them with scrambled variable numbering |
| `php` | 3% | pigeonhole, 3..6 holes, UNSAT (15%: as many pigeons as holes, SAT) |
| `parity` | 4% | two XOR chains over different orders of 4..24 variables, UNSAT if the parities differ |
| `edge-*` | 13% | `empty` (no clauses, also `p cnf 0 0`), `single`, `empty-clause`, `unit-chain` (UNSAT by unit propagation half of the time), `dups` (duplicate literals, tautologies, duplicate clauses), `unused` (sparse numbering, header larger than the largest variable), `long` (clauses of 50..600 literals), `2sat` (equivalence cycles and implication chains), `units` |

The non-edge families also get each mutator (duplicate literals, tautologies, duplicate
clauses, unused header variables, a few units) with probability ~4%. php, parity and some
edge cases carry their status by construction, which is checked against the reference.
Use `--family ksat,edge` (`edge` = all `edge-*`) to restrict the mix and `--max-vars` to
scale the scalable families.

The default mix is about 56% SAT / 44% UNSAT; generation takes ~0.4 ms per formula and
cadical195 needs ~3 ms on average (max ~0.5 s) per formula.

## Fuzzing options

`--option-ranges <file>` (or an inline `'spec; spec'`) lists solver options to randomize;
each is added with probability `--option-prob` (default 0.5), deterministically per seed:

```
# name=values        one value from the list
--restart=luby,ema
--reduce-int=100..3000    # integer range
--decay=0.80..0.99        # float range (a bound contains '.')
--proof-text              # bare flag
--conflicts=50..5000      # early UNKNOWNs are counted, not flagged
```

## Delta debugging (`ddmin.py`)

```sh
.venv/bin/python benchmarks/fuzz/ddmin.py benchmarks/fuzz/failures/disagree-s123.cnf
.venv/bin/python benchmarks/fuzz/ddmin.py bug.cnf --solver build/popso-sat --kind crash -o bug.min.cnf
.venv/bin/python benchmarks/fuzz/ddmin.py bug.cnf --kind exit:1 --args '--seed=7 --restart=luby'
```

The predicate re-runs `fuzzlib.check` and asks for the same kind (`any` = any failure,
`exit:<X>` = exit code X). Solver, options, proof mode, time limit and reference default
to the `c fuzz-*` header lines of a saved failure, so a failure file is enough; command
line flags override them. Steps, repeated until no change: ddmin over the clause list
(complement-based, as in cnfdd: the empty formula first, then removing chunks of n/2,
n/4, ..., 1 clauses left to right, keeping every removal that still fails, until no
single clause can be removed), the same over the literals of each clause; then compact
renumbering of variables (header = number of variables) if the failure survives it,
else the header is lowered towards the largest used variable (bisection). Results are cached; the candidates of a step are run
`-j` at a time (default 2, max 4) and the first failing one in order wins, so the result
does not depend on `-j`; `--max-tests` (default 5000) bounds the solver runs (the
smallest failing formula so far is kept). For `hang`/`timeout` pass a small `-t`.

## Validating the tools: `buggy_solver.py`

A stand-in solver (PySAT glucose4 by default, `--engine=<name>` for others, so it differs
from the cadical195 reference) with the popso-sat CLI: binary or text DRUP proofs,
`--time-limit`, `--conflicts`, `--seed`, `-n`; unknown `--x=y` options are accepted and
ignored. Bugs are injected with `--bug=<name>[:<p>]` (p = probability, default 1).
Whether a bug fires is a hash of the bug name and the `--seed` value (the input bytes
without `--seed`), so failures reproduce exactly and ddmin, which keeps the seed, sees the
bug on every candidate. Most of these bugs do not depend on the formula, so their minimal
failing formula is trivial (empty formula, one empty clause, one unit clause);
`truncate-long` is the structured one, whose core is a long clause plus the clauses that
refute its shortened version.

| bug | detected as |
|---|---|
| `flip-answer` | `disagree` (SAT reported UNSAT) / `model-invalid` (UNSAT reported SAT) |
| `bad-model` | `model-invalid` (when the flipped variable matters) |
| `partial-model` | `model-incomplete` / `model-invalid` |
| `crash` | `crash` |
| `drop-clause` | `model-invalid` (ignores the last clause) |
| `truncate-long` | `disagree` / `proof-rejected` (drops the last literal of clauses longer than 3) |
| `hang` | `hang` |
| `unknown` | `timeout` |
| `garbage` | `garbage` |
| `bad-exit` | `exit-code` |
| `error` | `error` |
| `bad-proof` | `proof-rejected` (needs a checker) |

```sh
.venv/bin/python benchmarks/fuzz/selftest.py                  # every bug + 1000 clean formulas
S=".venv/bin/python benchmarks/fuzz/buggy_solver.py"
.venv/bin/python benchmarks/fuzz/fuzz.py --solver "$S --bug=crash:0.02" --count 300 --shrink
.venv/bin/python benchmarks/fuzz/fuzz.py --solver "$S" --count 3000 --checker rupcheck   # expect 0 failures
```

The stand-in starts a Python interpreter (and PySAT) per formula, so it runs at only
10-25 formulas/s with `-j 2`; the tools themselves (generation ~0.4 ms, reference ~2 ms,
checks) are not the bottleneck for a native solver.

## Validation results (2026-11-03, stand-in only)

popso-sat had no working core yet, so the tools were validated against `buggy_solver.py`
on the shared macOS machine (M4 Pro, load average ~28 from other jobs), `-j 2`.
drat-trim was not built, so proofs were checked with `rupcheck.py`.

`selftest.py` (seed 7000; failures = formulas flagged; shrunk = first failure of each kind):

| bug | formulas | failures | kinds | shrunk (vars/clauses, solver runs) |
|---|---|---|---|---|
| `flip-answer:0.1` | 150 | 15 | disagree 9, model-invalid 6 | 27v/100c -> 0v/0c (7); 26v/89c -> 0v/1c (75) |
| `bad-model:0.1` | 150 | 5 | model-invalid 5 | 13v/132c -> 1v/1c (90) |
| `partial-model:0.1` | 150 | 8 | model-incomplete 2, model-invalid 6 | 35v/113c -> 1v/0c (8); 115v/448c -> 1v/1c (40) |
| `crash:0.1` | 100 | 13 | crash 13 | 26v/89c -> 0v/0c (7) |
| `drop-clause:1` | 150 | 19 | model-invalid 19 | 1v/2c -> 0v/1c (6) |
| `truncate-long:1` | 40 | 10 | disagree 7, proof-rejected 3 | 10v/69c -> 4v/4c (223); 13v/78c -> 4v/4c (207) |
| `garbage:0.1` | 100 | 3 | garbage 3 | 13v/62c -> 0v/0c (6) |
| `bad-exit:0.1` | 100 | 12 | exit-code 12 | 10v/48c -> 0v/0c (6) |
| `error:0.1` | 100 | 8 | error 8 | 19v/167c -> 0v/0c (7) |
| `bad-proof:0.2` | 150 | 8 | proof-rejected 8 | 30v/81c -> 8v/11c (515) |
| `hang:0.1` (`-t 1`) | 60 | 10 | hang 10 | 7v/34c -> 0v/0c (5) |
| `unknown:0.1` (`-t 1`) | 60 | 3 | timeout 3 | 12v/136c -> 0v/0c (6) |

Every bug is found, only with its expected kinds. Bugs that fire independently of the
formula shrink to trivial formulas, as they should. The structured `truncate-long` bug
shrinks to the expected 4-clause core, e.g. `4 -3 -1 2 0`, `-4 0`, `3 0`, `1 0`: the
clause without its last literal is refuted by the units. A larger case, run standalone
with `ddmin.py -j 2`, went from 28v/610c to the same kind of 4v/4c core in 1559 runs
(124 s with the Python stand-in). Shrinking costs grow with the size of the core: here
the clause pass first had to keep an unsatisfiable 157-clause core of the truncated
formula.

False-alarm run with the correct stand-in and fuzzed options (engines glucose4 /
glucose3 / maplechrono / cadical153, `--proof-text`, `--conflicts=200..20000`, two
ignored options):
`fuzz.py --count 3000 --seed 2000000 --checker rupcheck --option-ranges ...`, **0 failures**.
The stand-in answered SAT 1695, UNSAT 1295 and UNKNOWN 10 (conflict limits; not flagged).
The reference answered SAT 1696 and UNSAT 1304. 1259 proofs were verified and 36 were
trivial (formulas containing an empty clause). The run took 580 s, 5.2 formulas/s; the
stand-in took 283 ms per run on average under that load, and the reference 2.4 ms.
`selftest.py` itself also runs 1000 clean formulas: 0 failures, 10.5 formulas/s.

## Known limitations

- The drat-trim path is untested so far (drat-trim was not built when this was written).
  It expects drat-trim's `s VERIFIED` / `s NOT VERIFIED` lines and passes `-t`.
  Formulas with an empty clause are never proof-checked.
- `rupcheck.py` checks RUP only (no RAT) and ignores deletions. That is sound for RUP
  proofs, but it starts one Python process per proof, so use it for validation only.
- The memory cap (RLIMIT_AS) is applied on Linux only.
- If a worker process dies (for example a PySAT crash in the reference), the run aborts.
- `timeout` is a heuristic: UNKNOWN after at least 80% of the limit, when the reference
  needed under 5% of it.
- The current popso-sat placeholder takes only `<input>` and treats `--seed=...` as a
  file name, so every run reports `error` until the real CLI is in place.
