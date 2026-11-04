# Changelog

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
