# popso-sat

**popso-sat** is an open-source SAT solver for Boolean formulas in conjunctive normal form
(DIMACS CNF). It is a CDCL (conflict-driven clause learning) solver written from scratch in
C++20, using only the standard library. It belongs to the popso family (Polkowski's
Optimization Solver) but shares no code with popso.

This is a side project by [Marcin Polkowski](https://marcinpolkowski.com), built with heavy
use of AI coding agents. The goal is a fully open-source solver that holds its own against the
best open-source SAT solvers on real benchmarks, with an entry in the SAT Competition as the
first milestone. It is at an early stage.

On a sample of 168 instances of the SAT Competition 2026, version 0.4.5 solves 110 within 1000 s,
against 80 for Kissat 4.0.4 and 98 for version 0.4.0 on the same machine. All 65 UNSAT answers
were checked with their proofs. Most of the lead over Kissat comes from reasoning Kissat does
not have:
- counting certificates;
- Gauss-Jordan elimination;
- linear equations mod p.

The defaults were tuned on that sample. On 78 instances of the 2024 and 2025 competitions from
families never used for tuning, Kissat solves one more: 52 against 51 for 0.4.5 and 48 for 0.4.4.
0.4.5 has the lower PAR-2 there (785 against 818 s) and solves more within 300 s (45 against 37).
On a second such set of 49 instances of the 2017-2023 competitions, built after those defaults
were fixed, 0.4.6 (the same search as 0.4.5) solves 27 against 24 for Kissat. 0.4.8 solves 32
there: 0.4.7 and 0.4.8 add counting certificates that were developed on six instances of that
set. The same certificates refute the 18 mutilated chessboards of the 2018-2025 competitions
(up to 22 x 22) in under 0.1 s each, with proofs that the verified checker cake_lpr accepts in
seconds; Kissat solves 9 of them within 1000 s (see [BENCHMARKS.md](BENCHMARKS.md)).

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

A sample of 168 instances of the SAT Competition 2026 main track (`sets/sc2026.txt`). Setup:
- 1000 s and 12 GB per instance, four at a time, on an Intel i7-7700K running Linux;
- every model was checked;
- every UNSAT answer of popso-sat 0.4.5 was checked with its proof by dpr-trim (63 within
  its 3000 s limit; the other two, the same in 0.4.3, without the limit).

78 instances of the 2024 and 2025 main tracks from 38 families that are in no tuning set
(`sets/fresh.txt`), with the same setup and machine; no proofs.

49 instances of the 2017-2023 main tracks from 21 more families in no other set
(`sets/fresh2.txt`), with the same setup and machine; every UNSAT answer of 0.4.6, 0.4.7 and
0.4.8 checked with its proof. 0.4.6 changes no default, so its search is that of 0.4.5. 0.4.7
and 0.4.8 add pigeonhole certificates on sparse graphs and leave the search unchanged where
they find none, so only the fresh2 column of 0.4.8 is new.

Solved / PAR-2 in seconds:

| set | popso-sat 0.4.8 | popso-sat 0.4.5 and 0.4.6 | popso-sat 0.4.4 | popso-sat 0.4.0 | Kissat 4.0.4 |
|---|---|---|---|---|---|
| sc2026 (168) | | 110 / 773.8 | 110 / 772.5 | 98 / 926.4 | 80 / 1152.3 |
| fresh (78) | | 51 / 785.2 | 48 / 833.5 | | 52 / 818.2 |
| fresh2 (49) | 32 / 790.0 | 27 / 1011.8 | | | 24 / 1132.1 |

**sc2026:** 0.4.5 solves 36 instances that Kissat does not, most of them with counting,
Gauss-Jordan or mod-p reasoning. Kissat solves 6 that 0.4.5 does not. 0.4.5 and 0.4.4 solve
the same instances. At 5000 s (competition
length, on an AMD EPYC 4465P), 0.4.2 solves 130, the 0.4.1 search 125 and Kissat 110.

**fresh:** 0.4.5 solves three more than 0.4.4 (reconf10_22_queen20, rook-51 and rook-52; Kissat
solves neither rook instance) and loses none. Kissat solves 9 instances that 0.4.5 does not,
and 0.4.5 solves 8 that Kissat does not.

**fresh2:** 0.4.6 solves 5 instances that Kissat does not; Kissat solves 2 that 0.4.6 does not
(one of them only with its default seed). 0.4.8 refutes six more in under 0.1 s each, four of
them since 0.4.7 (randomG-n18, randomG-n20, randomG-B-Mix-n18, intervals122, intervals718 and
intervals855: sets of pigeons with one hole too few), and dpr-trim checks each of the six
proofs in at most 1.5 s. The certificates were developed on these six, so they are not an
independent test. One instance that 0.4.6 solved at 949 s runs into the 1000 s limit in the
0.4.7 and 0.4.8 runs, with the same search.

**Mutilated chessboards:** the 18 instances of this family in the SAT Competition main tracks
of 2018 to 2025 (15 x 15 to 22 x 22), 1000 s, Intel Xeon E5-1650 v2: 0.4.8 refutes all 18 in at
most 0.03 s each, Kissat solves 9 and 0.4.7 solves 5. All 18 proofs pass dpr-trim and the
verified checker cake_lpr in under 8 s each. Two of these instances were used to develop the
certificate, so this is not a held-out set.

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
  and cliques, inside larger formulas. Pigeonholes are also found on sparse graphs, where a
  pigeon may use only some of the holes (mutilated chessboards, matchings in bipartite
  graphs): bipartite matching finds a set of pigeons with too few holes, which is refuted by
  elimination on the graph. Such a structure is refuted with polynomially many PR
  clauses (symmetry-style steps, each checked by the solver before it is written) where
  resolution needs exponentially many steps. Without a structure the search is unchanged.
- Gauss-Jordan elimination on XOR constraints. The XORs are taken from complete clause
  encodings. An inconsistent XOR system is refuted before search, with a DRAT proof that sums
  the XORs as chains of extension variables. Otherwise, if the XORs cover enough of the
  formula, a detached copy of the solver with Gauss-Jordan propagation searches besides the
  main one. It writes no proof, and only a model can come back from it. Its share of the
  search effort adapts: it grows while Gauss-Jordan finds a good part of the copy's conflicts,
  and the copy is stopped where Gauss-Jordan adds nothing to unit propagation.
- Bounded variable addition also during search, on literals of variables touched since the last
  round.
- Linear equations mod 3, 5 or 7 hidden in clauses: one-hot domains, plus constraints whose
  allowed tuples form exactly one equation. They are solved by Gaussian elimination over GF(p),
  and the solution is tried as a model.
- Local search for rephasing: ProbSAT with incrementally maintained break values. A DDFW
  clause-weighting walk then starts from ProbSAT's best assignment, only to look for a model.
  Lucky assignments are tried before search.
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
- Memory on the largest formulas is close to Kissat's since 0.4.1. The largest peak on the 2026
  sample is 2.5 GB, against Kissat's 2.4 GB.

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
