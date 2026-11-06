# popso-sat

**popso-sat** is an open-source SAT solver for Boolean formulas in conjunctive normal form
(DIMACS CNF). It is a CDCL (conflict-driven clause learning) solver written from scratch in
C++20, using only the standard library. It belongs to the popso family (Polkowski's
Optimization Solver) but shares no code with popso.

This is a side project by [Marcin Polkowski](https://marcinpolkowski.com), built with heavy
use of AI coding agents. The goal is a fully open-source solver that holds its own against the
best open-source SAT solvers on real benchmarks, with an entry in the SAT Competition as the
first milestone. It is at an early stage. On a sample of 168 instances of the SAT Competition 2026
it solves 98 within 1000 s, against 67 for version 0.3.3, all of the 61 UNSAT answers checked
with their proofs. On 32 instances from earlier SAT Competitions that were not used for tuning it
solves 21 within 120 s, where Kissat solves 24 (see [BENCHMARKS.md](BENCHMARKS.md)).

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
./build/popso-sat formula.cnf proof.dpr          # with a proof of unsatisfiability (binary)
./build/popso-sat --time-limit=60 -v formula.cnf
```

Output follows the SAT Competition conventions: comment lines start with `c`, the answer is
`s SATISFIABLE` (followed by the model in `v` lines), `s UNSATISFIABLE` or `s UNKNOWN`, and the
exit code is 10, 20 or 0. Main options:

| option | meaning |
|---|---|
| `--proof=<file>` or a second file argument | write a proof of unsatisfiability: DRAT, plus PR lines (the DPR format) where a counting certificate is used (binary; `--proof-text` for text) |
| `-t <s>`, `--time-limit=<s>` | wall-clock limit |
| `--mem-limit=<MB>` | memory limit: `s UNKNOWN` once the peak resident size reaches 7/8 of it |
| `--seed=<n>` | random seed (shuffles the initial variable order) |
| `-v`, `-q`, `-n` | verbose statistics / no comments / no model lines |
| `--<name>=<value>` | any solver option, see `--help` |

Inputs are read in a single streaming pass. gzip and xz data are recognized by their magic
bytes and decompressed on the fly by decoders written from the format specifications. By
default every model is checked against the original formula before it is printed.

## Performance

A sample of 168 instances of the SAT Competition 2026 main track (`sets/sc2026.txt`): 1000 s
and 12 GB per instance, Intel i7-7700K, Linux, four instances at a time. Every model was checked,
and every UNSAT answer of 0.4.0 was checked with its proof by dpr-trim (solved / PAR-2 in
seconds):

| set | popso-sat 0.4.0 | popso-sat 0.3.3 |
|---|---|---|
| sc2026 (168) | 98 / 926.4 | 67 / 1303.8 |

0.4.0 solves 35 of these instances that 0.3.3 does not, and loses 4 (all satisfiable).
- 25 of the 35 are refuted by counting certificates within 2.5 s: pigeonhole-like, parity and
  counting formulas whose resolution proofs are exponentially long.
- 7 more are solved with Gauss-Jordan elimination: lights-out and parity formulas.

The 0.4.0 defaults were chosen on this set, so it is no longer a held-out test. Kissat 4.0.4 is
being run on it for the next release.

Smaller sets of instances from the SAT Competitions 2022 to 2025, 120 s, Apple M4 Pro (0.4.0 and
0.3.4 run in alternation on a shared machine; Kissat on the idle machine, in the v0.3.4 section of
BENCHMARKS.md):

| set | popso-sat 0.4.0 | popso-sat 0.3.4 | Kissat 4.0.4 (idle machine) |
|---|---|---|---|
| 26 unsatisfiable instances (A/B set) | 22 / 57.2 | 22 / 55.2 | 22 / 52.9 |
| 29 tuning instances (mixed) | 25 / 47.4 | 25 / 45.7 | 26 / 45.5 |
| 32 held-out instances (one per family) | 21 / 103.7 | 20 / 109.9 | 24 / 83.9 |

The first two sets were used for tuning decisions, so they are not an independent test; the
held-out set is. Satisfiable instances vary a lot from run to run. On 25 generated formulas
(coloring, Tseitin, pigeonhole, random k-SAT, xor chains, multiplier equivalence, ...)
popso-sat 0.4.0 solves all 25 within 60 s (PAR-2 2.7 s on the M4), as Kissat does. Setup,
per-instance times and plots, and the earlier measurements, are in
[BENCHMARKS.md](BENCHMARKS.md).

## What's inside

- DIMACS push parser (strict by default, `--relaxed` for malformed-but-unambiguous files).
- Two-watched-literal propagation with blocking literals; binary clauses live in the watch
  lists only; long clauses in one compact arena with a compacting garbage collector.
- First-UIP conflict analysis with recursive clause minimization and shrinking (learned clauses
  are shrunk to block UIPs, lower-level reason literals included), glue (LBD) computation and
  glue updates of learned clauses used in later conflicts, reason-side variable bumping.
- Two search modes, switched on a deterministic effort measure with phases growing
  quadratically: *focused* (VMTF decision queue, restarts on glue moving averages at intervals
  growing with the logarithm of the restart count) and *stable*
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
  equivalences in the environment of a variable, candidates refined by the models found; the
  environments grow when sweeping finds little) and for definition mining in elimination.
- Equivalences found by random simulation: the extracted AND and XOR gates are evaluated on 512
  random input vectors, and variables with equal signatures are proven equivalent by Kitten on
  small windows of their fan-in cones (functional equivalences between distant parts of a
  circuit, such as the two halves of a miter).
- Bounded variable addition (re-encoding at-most-one cliques and similar structure with new
  variables) behind a trial: the matching runs once without changing the formula, and the
  replacements are made only if they remove at least a fifth of the clauses.
- Counting certificates before search: pigeonhole, functional pigeonhole and clique formulas,
  parity (perfect matchings of an odd complete graph), Count^3, clique-colouring and
  relativized pigeonholes are recognized, also with shuffled polarities and, for pigeonholes
  and cliques, inside larger formulas. Such a structure is refuted with polynomially many PR
  clauses (symmetry-style steps, each checked by the solver before it is written) where
  resolution needs exponentially many steps. Without a structure the search is unchanged.
- Gauss-Jordan elimination on XOR constraints. The XORs are taken from complete clause
  encodings. An inconsistent XOR system is refuted before search, with a DRAT proof that sums
  the XORs as chains of extension variables. Otherwise, if the XORs cover enough of the
  formula, a detached copy of the solver with Gauss-Jordan propagation searches besides the
  main one. It writes no proof, and only a model can come back from it. Its share of the
  search effort adapts: it grows while Gauss-Jordan finds a good part of the copy's conflicts,
  and the copy is stopped where Gauss-Jordan adds nothing to unit propagation.
- Local search (ProbSAT with incrementally maintained break values) for rephasing, and lucky
  assignments tried before search.
- Proofs in the DRAT format, with PR clauses (the DPR format) for counting certificates.
  Every UNSAT answer in the test suite and the benchmark runner is checked, with dpr-trim (and
  the formally verified cake_lpr on the competition chain).

## Correctness

Every answer is checked: models against the formula, and proofs of unsatisfiability with a
proof checker. The unit tests compare against a brute-force oracle on thousands of small
random formulas under option settings that force frequent restarts, reductions and mode
switches. The fuzzing tools in [benchmarks/fuzz](benchmarks/fuzz) compare against reference
solvers on random and structured formulas and shrink failures with delta debugging.

## Current limitations

- Several techniques are implemented but off by default because they cost more than they gain
  in our A/B runs: chronological backtracking, unhiding (transitive reduction, hidden
  tautologies and literals), and some vivification variants. No symmetry handling beyond the
  counting certificates.
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
