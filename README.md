# popso-sat

**popso-sat** is an open-source SAT solver for Boolean formulas in conjunctive normal form
(DIMACS CNF). It is a CDCL (conflict-driven clause learning) solver written from scratch in
C++20, using only the standard library. It belongs to the popso family (Polkowski's
Optimization Solver) but shares no code with popso.

This is a side project by [Marcin Polkowski](https://marcinpolkowski.com), built with heavy
use of AI coding agents. The goal is a fully open-source solver that holds its own against the
best open-source SAT solvers on real benchmarks, with an entry in the SAT Competition as the
first milestone. It is at an early stage: on 36 instances from recent SAT Competitions it solves
21 within 120 s, where Kissat solves 22 (see [BENCHMARKS.md](BENCHMARKS.md)).

## Build

You need CMake ≥ 3.20 and a C++20 compiler (clang or gcc). No other dependencies.

```sh
cmake -S . -B build -DCMAKE_BUILD_TYPE=Release
cmake --build build -j 4
(cd build && ctest)            # unit tests
```

Without CMake, `./build.sh` compiles `bin/popso-sat` directly with the system C++ compiler
(this is what the SAT Competition harness uses).

The solver is developed on macOS (Apple silicon) and Linux. Windows (MSVC) is not tested yet.

## Usage

```sh
./build/popso-sat formula.cnf                    # also .cnf.gz and .cnf.xz
./build/popso-sat formula.cnf proof.drat         # with a DRAT proof (binary format)
./build/popso-sat --time-limit=60 -v formula.cnf
```

Output follows the SAT Competition conventions: comment lines start with `c`, the answer is
`s SATISFIABLE` (followed by the model in `v` lines), `s UNSATISFIABLE` or `s UNKNOWN`, and the
exit code is 10, 20 or 0. Main options:

| option | meaning |
|---|---|
| `--proof=<file>` or a second file argument | write a DRAT proof of unsatisfiability (binary; `--proof-text` for text) |
| `-t <s>`, `--time-limit=<s>` | wall-clock limit |
| `--mem-limit=<MB>` | memory limit (approximate, from the solver's own accounting) |
| `--seed=<n>` | random seed (shuffles the initial variable order) |
| `-v`, `-q`, `-n` | verbose statistics / no comments / no model lines |
| `--<name>=<value>` | any solver option, see `--help` |

Inputs are read in a single streaming pass. gzip and xz data are recognized by their magic
bytes and decompressed on the fly by decoders written from the format specifications. By
default every model is checked against the original formula before it is printed.

## Performance

36 instances from the main tracks of the SAT Competitions 2022 to 2025 (mostly ones on which
Kissat needed 10 to 300 s in the competition), 120 s limit, one Linux machine, every model checked:

| solver | solved of 36 | PAR-2 (s) |
|---|---|---|
| popso-sat 0.3 | 21 | 110.9 |
| popso-sat 0.2 | 18 | 134.2 |
| popso-sat 0.1.1 | 15 | 152.6 |
| Kissat 4.0.4 | 22 | 113.8 |

The defaults of 0.3 were chosen with A/B runs on these instances, so this is not an independent
test; single runs, and satisfiable instances vary a lot from run to run.

On 25 generated formulas (coloring, Tseitin, pigeonhole, random k-SAT, xor chains, multiplier
equivalence, ...) popso-sat 0.3 solves all 25 in 60 s (PAR-2 7.5 s), Kissat 25 (8.5 s),
CaDiCaL 23, Glucose 21, MiniSat 17.
Setup, caveats (the reference solvers run through PySAT), per-instance times and plots are in
[BENCHMARKS.md](BENCHMARKS.md).

## What's inside

- DIMACS push parser (strict by default, `--relaxed` for malformed-but-unambiguous files).
- Two-watched-literal propagation with blocking literals; binary clauses live in the watch
  lists only; long clauses in one compact arena with a compacting garbage collector.
- First-UIP conflict analysis with recursive clause minimization, glue (LBD) computation and
  glue updates of learned clauses used in later conflicts, reason-side variable bumping.
- Two search modes, switched on a deterministic effort measure with phases growing
  quadratically: *focused* (VMTF decision queue, restarts on glue moving averages) and *stable*
  (EVSIDS scores, reluctant-doubling restarts, target phases), as in Kissat. Restarts keep the
  decisions that would be taken again (trail reuse).
- Phase saving, target and best phases, periodic rephasing.
- Learned clauses in three tiers by glue, with usage-based aging.
- Pre- and inprocessing in rounds scheduled by search effort: subsumption and strengthening,
  bounded variable elimination with gate definitions (AND, XOR, if-then-else, and semantic
  definitions found by Kitten) and model reconstruction (XOR constraints are not merged into
  longer ones, which hurts parity formulas), equivalent literal substitution, congruence closure on AND, XOR and
  if-then-else gates, vivification with conflict analysis, failed literal probing, eager
  subsumption of learned clauses.
- Kitten, a small CDCL sub-solver for local sub-formulas, used for sweeping (backbones and
  equivalences in the environment of a variable) and for definition mining in elimination.
- Local search (ProbSAT with incrementally maintained break values) for rephasing, and lucky
  assignments tried before search.
- DRAT proof output; every UNSAT answer in the test suite and the benchmark runner is checked.

## Correctness

Every answer is checked: models against the formula, and proofs of unsatisfiability with a
proof checker. The unit tests compare against a brute-force oracle on thousands of small
random formulas under option settings that force frequent restarts, reductions and mode
switches. The fuzzing tools in [benchmarks/fuzz](benchmarks/fuzz) compare against reference
solvers on random and structured formulas and shrink failures with delta debugging.

## Current limitations

- Bounded variable addition is implemented but off by default (on the test set it costs more
  than it gains); no chronological backtracking yet (in development), no transitive reduction or
  symmetry handling.
- Single-threaded; no incremental (IPASIR) interface or C API yet.
- Memory per variable is larger than in Kissat; very large formulas need more memory.

## Repository layout

```
src/psat/core     literals, options
src/psat/io       DIMACS parser, input streaming, gzip / xz decoders, DRAT writer
src/psat/solver   the CDCL solver
apps              the popso-sat command line
tests             unit tests (tiny std-only harness)
benchmarks        benchmark runner, instance generators, reference results, fuzzing
docs              benchmark plots
```

## License

Apache-2.0, see [LICENSE](LICENSE) and [NOTICE](NOTICE).

## Contact

Marcin Polkowski, [marcinpolkowski.com](https://marcinpolkowski.com).
