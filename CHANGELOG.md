# Changelog

## v0.3.0 — 2026-11-04

Sweeping and definition mining are on by default, with search and scheduling changes measured
on SAT Competition instances. On 36 SAT Competition instances (120 s) popso-sat now solves 21
instead of 18 (Kissat 4.0.4: 22), with PAR-2 111 s instead of 134 s (Kissat 114 s); on the
generated medium set it solves all 25 (PAR-2 7.5 s; Kissat 25, 8.5 s). See [BENCHMARKS.md](BENCHMARKS.md).

- **On by default:** sweeping (backbones and equivalences with Kitten) at a higher effort, with a
  back-off after sweeps that find nothing; semantic definitions (unsat cores) in elimination;
  trail reuse on restarts (decisions that would be taken again are kept); a mode schedule whose
  focused / stable phases grow quadratically.
- **Parity formulas:** elimination no longer merges two XOR constraints into a longer one
  (`--eliminatexorlim`, default 3). On Tseitin, Urquhart and XOR-chain formulas CDCL needs many
  times the conflicts on the merged XORs; the v0.2 regression on XOR chains is gone.
- **Local search:** the ProbSAT walk keeps break values up to date instead of recomputing them
  for every flip (a flip now visits the flipped variable's occurrences once). On dense
  formulas this gives several times more flips for the same effort; two random-like 11-SAT
  competition instances that timed out are now solved in 3 to 4 s (on another machine the
  first walk finds the model).
- **Elimination scheduling:** rounds back off when they eliminate nothing, keep candidates they
  did not get to, and continue while the bound can still grow.
- **Bounded variable addition** (still off by default): at least 1000 new variables per round
  instead of a tenth of the variables (small at-most-one-heavy formulas such as
  battleship-13-13 are solved in seconds), and its matching is charged to its effort budget.
- **Memory:** occurrence lists for elimination in one pool instead of one vector per literal;
  the extension stack grows like the clause arena.

## v0.2.1 — 2026-11-04

- Documentation: BENCHMARKS.md credited a fix of the elimination schedule for faster times on
  two competition instances; that compared times from two different machines and is withdrawn.
  The solver is unchanged from v0.2.0.

## v0.2.0 — 2026-11-04

Pre- and inprocessing: the formula is simplified before and periodically during search. On 36
SAT Competition instances (120 s) popso-sat now solves 18 instead of 15 (Kissat 4.0.4: 22), with
PAR-2 134 s instead of 153 s; on the generated medium set it is about as fast as v0.1.1 (better
on coloring, counters and pigeonhole, worse on XOR chains). See [BENCHMARKS.md](BENCHMARKS.md).

- **Elimination rounds** (in a dense mode without long watches): forward subsumption and
  strengthening; bounded variable elimination with AND, equivalence, XOR and if-then-else gate
  definitions, a growing bound (0, 1, 2, 4, ... 16) and model reconstruction; equivalent
  literal substitution (strongly connected components of the binary implication graph);
  congruence closure on AND, XOR and if-then-else gates (equal gates give equivalences; XOR and
  if-then-else equivalences are proved by case splits in the DRAT proof).
- **Vivification** of learned (tier 1 and 2) and irredundant clauses, with sorted literals so
  that consecutive clauses share decisions, and conflict analysis that keeps only the decisions
  involved; failed literal probing; eager subsumption of recently learned clauses.
- **Phases:** ProbSAT local search on rephasing (walk), lucky assignments tried before search.
- **Kitten**, a small CDCL sub-solver for local sub-formulas (assumptions, unsat cores, learned
  clauses emitted to the DRAT proof), used by *sweeping* (backbones and equivalences in the
  environment of a variable) and *definition mining* for elimination (unsat cores as semantic
  gates). Both are off by default until they are tuned.
- **Off by default** until they show a benefit: bounded variable addition, learned clause
  shrinking, dynamic tier limits.
- **Large formulas:** effort budgets in propagation ticks for every inprocessing pass; garbage
  collection compacts only from the first deleted clause and is deferred until it pays, with
  propagation dropping watches of deleted clauses; lower peak memory (the clause arena grows
  with realloc, vivification and congruence closure use compact temporary structures, the
  model-check copy of the input is stored in chunks); peak resident memory in the statistics.
- **Testing:** a circuit family in the fuzzer (miters of AND/OR/XOR/ITE circuits in varied gate
  forms), a test for Kitten against brute force (models, RUP-checked proofs, unsat cores),
  regression tests for an elimination bug found on a competition instance and for the
  semantic-definition resolvent rule (found by mutation testing).

## v0.1.1 — 2026-11-03

- Fix the build with gcc 13 on Linux (Ubuntu 24.04, the SAT Competition platform): a header
  relied on `<cstdint>` being included transitively, which is only the case with clang on
  macOS. Every header now compiles on its own with gcc, and releases are built and tested
  with gcc 13 on Linux before they are tagged.

## v0.1.0 — 2026-11-03

First version: a correct, complete CDCL solver with the SAT Competition interface. On the
generated medium benchmark set it solves all 25 formulas, close to Kissat 4.0.4 (PAR-2 5.6 s
against 4.4 s, see [BENCHMARKS.md](BENCHMARKS.md)); it has no preprocessing yet.

- **Input:** DIMACS CNF push parser (strict by default, `--relaxed`), streaming input with
  gzip and xz decompression written from the format specifications (~110 MB/s for xz); about
  330 MB/s parsing and 0.55 s from a 96 MB file to search.
- **Search:** two-watched-literal propagation with blocking literals and binary clauses in the
  watch lists; first-UIP learning with recursive minimization; glue (LBD) and glue updates;
  VMTF (focused mode) and EVSIDS (stable mode) with ticks-based mode switching; EMA restarts
  (focused) and reluctant doubling (stable); saved, target and best phases with rephasing;
  three-tier learned clause database with usage aging and a compacting arena GC.
- **Output:** SAT Competition format and exit codes, DRAT proofs (binary or text), internal
  model check before printing, `--time-limit`, `--mem-limit`, `--seed`, signals stop with
  `s UNKNOWN`. `build.sh` / `run.sh` for the competition harness (no CMake needed).
- **Testing:** brute-force oracle and RUP-checked proofs over option variants, ASan/UBSan clean;
  random and structured fuzzing against PySAT reference solvers with delta debugging.
