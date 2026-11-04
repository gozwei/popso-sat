# popso-sat

**popso-sat** is an open-source SAT solver for Boolean formulas in conjunctive normal form
(DIMACS CNF). It is a CDCL (conflict-driven clause learning) solver written from scratch in
C++20, using only the standard library. It belongs to the popso family (Polkowski's
Optimization Solver) but shares no code with popso.

This is a side project by [Marcin Polkowski](https://marcinpolkowski.com), built with heavy
use of AI coding agents. The goal is a fully open-source solver that holds its own against the
best open-source SAT solvers on real benchmarks, with an entry in the SAT Competition as the
first milestone. It is at an early stage. On a set of generated benchmark formulas it is
already close to Kissat, but it has no pre- or inprocessing yet, which matters most on the
application instances of the SAT Competition (see [BENCHMARKS.md](BENCHMARKS.md)).

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

25 generated formulas from 11 families (coloring, Tseitin, pigeonhole, random 3- and 5-SAT,
xor chains, multiplier equivalence, ...), 60 s limit, every model checked:

| solver | solved of 25 | PAR-2 (s) |
|---|---|---|
| popso-sat 0.1 | 25 | 5.6 |
| Kissat 4.0.4 | 25 | 4.4 |
| CaDiCaL 1.9.5 | 23 | 16.4 |
| Glucose 4 | 23 | 18.7 |
| MiniSat 2.2 | 20 | 34.1 |

These are crafted formulas, not competition instances; setup, caveats, the per-instance times
and a plot are in [BENCHMARKS.md](BENCHMARKS.md).

## What's inside

- DIMACS push parser (strict by default, `--relaxed` for malformed-but-unambiguous files).
- Two-watched-literal propagation with blocking literals; binary clauses live in the watch
  lists only; long clauses in one compact arena with a compacting garbage collector.
- First-UIP conflict analysis with recursive clause minimization, glue (LBD) computation and
  glue updates of learned clauses used in later conflicts, reason-side variable bumping.
- Two search modes, switched on a deterministic effort measure: *focused* (VMTF decision queue,
  restarts on glue moving averages) and *stable* (EVSIDS scores, reluctant-doubling restarts,
  target phases), as in Kissat.
- Phase saving, target and best phases, periodic rephasing.
- Learned clauses in three tiers by glue, with usage-based aging.
- DRAT proof output; every UNSAT answer in the test suite and the benchmark runner is checked.

## Correctness

Every answer is checked: models against the formula, and proofs of unsatisfiability with a
proof checker. The unit tests compare against a brute-force oracle on thousands of small
random formulas under option settings that force frequent restarts, reductions and mode
switches. The fuzzing tools in [benchmarks/fuzz](benchmarks/fuzz) compare against reference
solvers on random and structured formulas and shrink failures with delta debugging.

## Current limitations

- No pre- or inprocessing yet (variable elimination, subsumption, vivification, ...): planned
  for the next version, and the main reason for the gap to state-of-the-art solvers.
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
