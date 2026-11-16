# Benchmarks

Instance sets with known status, the benchmark runner that independently checks every answer,
reference solving, and the correctness gates for popso-sat.  Everything here is Python 3.10+;
`run.py`, `gate.py`, the checkers and the download scripts use only the standard library,
reference solving uses [PySAT](https://pysathq.github.io) (`python-sat`).  The solver itself
never depends on any of this.

```
benchmarks/
  run.py                 benchmark runner: model check, proof check, status check, metrics, results
  gate.py                the correctness gates (sets/gate.txt, strict)
  reference.py           reference solves (PySAT solvers or binaries) -> reference/status.json
  satlib.py              SATLIB download -> <cache>/satlib, sets/satlib_*.txt
  gbd.py                 Global Benchmark Database: metadata, dev-set selection, downloads
  selftest.py            self-test of the tooling (reader, verifier, pydrat, run.py vs injected bugs)
  generators/
    families.py          instance families with known status (by construction where possible)
    generate.py          size table (tiny/small/medium), deterministic seeds, manifest, set files
  instances/             generated tiny (.cnf) and small (.cnf.gz) instances (committed)
    manifest.json        per instance: family, params, status and how it is known, sha256
  sets/                  instance lists for run.py / reference.py (see "Set files")
  reference/
    status.json          reference statuses (solver, version, time, machine) per instance
    gbd_dev_candidates.json   details of the GBD dev-set candidates
  lib/                   paths, DIMACS reader/writer, solver-output parser, model verifier,
                         capped subprocess runner, proof checking, set files
  tools/
    pysat_cli.py         PySAT-backed stand-in implementing popso-sat's CLI contract (+ FAKE_BUG)
    pydrat.py            small pure-Python forward DRAT checker (fallback for drat-trim)
  results/               run.py output (gitignored)
```

## Setup and paths

```sh
python3 -m venv .venv && .venv/bin/pip install -r benchmarks/requirements.txt   # once, main checkout
```

Worktrees share the main checkout's `.venv` (`<main>/.venv/bin/python`).  Large and derived data
also lives in the **main checkout**, so every worktree sees the same files; `lib/paths.py` finds
it as the parent of `git rev-parse --git-common-dir` (override: `PSAT_ROOT`):

| what | where | override |
|---|---|---|
| downloaded / generated-medium instances | `<main>/benchmarks/cache/` (gitignored) | `PSAT_CACHE` |
| reference binaries (drat-trim, later kissat/cadical) | `<main>/benchmarks/tools/build/bin/` (gitignored) | `PSAT_TOOLS_BIN` |
| run results | `<repo>/benchmarks/results/` (gitignored, per checkout) | `PSAT_RESULTS`, `--out-dir` |
| default solver | `<repo>/build/popso-sat` | `--solver` |

Instance paths in set files and result files are relative: `benchmarks/...` (committed, relative
to the repository) or relative to the cache (`satlib/...`, `gbd/...`, `generated/...`).  No
absolute local paths are written anywhere.

**drat-trim** (optional but recommended for UNSAT proofs): it is not built by this tooling.  Put a
`drat-trim` binary into `<main>/benchmarks/tools/build/bin/` (it is one C file:
https://github.com/marijnheule/drat-trim, `make`), and `run.py` uses it automatically.  Until then
UNSAT proofs are checked with `tools/pydrat.py` when they are small (see below).

## The runner: `run.py`

```sh
.venv/bin/python benchmarks/run.py --set gate -j 2 --strict                 # build/popso-sat
.venv/bin/python benchmarks/run.py --solver build/popso-sat --set small -t 30 --tag base --seed 1
.venv/bin/python benchmarks/run.py --solver pysat:cadical195 --set tiny     # PySAT stand-in
.venv/bin/python benchmarks/run.py --solver "benchmarks/tools/pysat_cli.py --solver kissat404" ...
.venv/bin/python benchmarks/run.py --set satlib --list                      # selection only
.venv/bin/python benchmarks/run.py benchmarks/instances/tiny 'some/dir/*.cnf'   # files/globs/dirs
```

Per instance it runs
`<solver> --time-limit=T --mem-limit=M [--seed=S] [--extra ...] --proof=<tmp> <input>`
(templates `--time-arg`, `--mem-arg`, `--seed-arg`, `--proof-arg`; `''` disables one, a proof
template of `'{}'` passes the proof file as 2nd positional argument, as in the SAT Competition),
so any competition-format solver works, e.g. Kissat:
`--solver path/kissat --time-arg='--time={}' --mem-arg='' --proof-arg='{}'`.  `--solver` also
accepts `pysat:<name>`, a quoted command line, a `.py` script, or a bare name of a binary in
`<main>/benchmarks/tools/build/bin`.  Option values that start with `-` need the `=` form
(argparse): `--extra='--deterministic --seed=3'`, `--time-arg='--time={}'`.

**Every answer is checked:**

* **SAT:** the `v` lines are parsed (must end with `0`) and the model is verified against the
  original file with an independent streaming DIMACS reader (`lib/verify.py`): every clause must
  contain a true literal and no variable may be listed with both signs.  Unassigned variables
  are reported (`model_missing`), not counted wrong, if every clause is satisfied anyway.
* **UNSAT:** the solver writes a DRAT proof to a temporary file (deleted afterwards), which is
  checked by drat-trim if present, else by `tools/pydrat.py` for proofs up to `--pydrat-max-mb`
  (10 MB).  The checker has its own time limit (`--proof-time-limit`, default 2T + 30 s) and the
  same memory cap.  Proof states: `verified`, `rejected` (counted **WRONG**), `proof-timeout`,
  `proof-memlimit`, `proof-error`, `missing` (no proof file), `unchecked` (no checker, proof too
  large for pydrat, `--checker none`), `off` (`--no-proof`).
* **Status:** the answer is compared with the expected status from the set file, else from
  `reference/status.json`; a verified model of an instance expected UNSAT, or UNSAT for one
  expected SAT, is WRONG.  Exit codes must be 10 / 20 / 0.

**Classes:** `ok` (verified answer within the time limit), `unsolved` (`s UNKNOWN`, time limit,
answer after the limit), `memlimit` (killed above the cap, or the solver reports running out of
memory), `error` (crash, no `s` line, wrong exit code, garbled output, killed at T + grace although
the time limit was passed to it), `WRONG`.

**Limits.** `-t` (default 60 s; the solver is killed at T + max(5 s, 0.1 T)), `--mem-limit`
(default 2048 MB, passed to the solver and enforced per process by an RSS watchdog at 125%:
`lib/proc.py` samples the process group's RSS with `ps` every 0.5 s and kills the whole group; on
Linux RLIMIT_AS = 2x the cap is set as well; macOS does not enforce RLIMIT_AS, so the watchdog is
what counts there), `-j` (instances in parallel; default 1).

**Inputs.** `.cnf`, `.cnf.gz`, `.cnf.xz`, `.cnf.bz2`.  `--decompress xz` (default, while
popso-sat cannot read `.xz`) hands the solver the plain sibling file (`x.cnf` next to `x.cnf.xz`,
written by `gbd.py download`) or a temporary decompressed copy; `--decompress none` once the xz
reader exists.

**Output.** One line per instance (expected status, class, status, wall time, peak RSS, proof
state), then the summary: solved (SAT/UNSAT), unsolved, memlimit, errors, `WRONG <n>`, **PAR-2**
(mean of the time, 2T for unsolved), **shifted geometric mean** (shift 10 s, unsolved = T), proof
states and per-family solved counts.  Files: `results/<timestamp>_<git-sha>[_tag].json` (meta,
summary, records) and `.csv`; while running, `.jsonl` (meta line plus one fsync'ed line per
finished instance, removed at the end).  After an interruption (Ctrl-C/SIGTERM kill the running
solver and print the command) the same command plus `--resume <that .jsonl>` continues it;
`--redo error,memlimit` re-runs those classes.  The meta records the solver command, its sha256,
git sha (`-dirty` if src/apps/CMakeLists.txt differ), limits, seed, extra arguments, machine.

**Exit code:** 1 if any answer is WRONG.  `--strict`: also on errors and on UNSAT answers without
a verified proof (unless `--allow-unchecked`); `--require-solved`: also on unsolved instances.
`--keep-logs` keeps stdout/stderr/command of WRONG/error runs in `results/<base>.logs/`.

## Gates: `gate.py`

```sh
.venv/bin/python benchmarks/gate.py                               # build/popso-sat
.venv/bin/python benchmarks/gate.py --variant deterministic       # adds --deterministic (for later)
.venv/bin/python benchmarks/gate.py --solver pysat:cadical195     # harness self-test
```

`gate.py` downloads the SATLIB part of `sets/gate.txt` once if needed (18 SATLIB archives, 20 MB;
BMC and QG are the big ones) and runs `run.py --set gate --strict -j 2 --mem-limit 2048 -t 30`.
The gate passes when there is no WRONG answer, no error and every UNSAT proof is verified.  `sets/gate.txt` has 58
instances (31 SAT, 27 UNSAT): 18 tiny and 20 small generated ones covering all families, and 20
small SATLIB instances (uf/uuf 50/100, flat, ais, logistics, blocksworld, pigeon hole, dubois,
pret, aim yes/no, ssa, bf, jnh, ii, qg, bmc).  The instances were picked so that their CaDiCaL
proofs check in pydrat within a few seconds.  The deterministic variant runs the same set with
`--deterministic` (popso-sat does not have that option yet; keep it for v0.6).

Validation (2026-11-03, Apple M4 Pro): the PySAT CaDiCaL 1.9.5 stand-in passes in 17 s at `-j 2`
with all 27 proofs verified by pydrat; the injected defects of `pysat_cli.py` (`FAKE_BUG=flip`,
`unsat`, `sat`, `nomodel`, `badproof`, `exitcode`, `crash`, `hang`, `mem`) are all caught
(WRONG / error / memlimit as expected; `selftest.py` repeats this).  The popso-sat build of the
same day first solved 57 of 58 with all its binary DRAT proofs verified; the 58th, `pret60_25`,
was rejected by its strict parser because of a SATLIB quirk (see below).  With that file
normalized in the cache it passes: 58/58, 27 proofs verified by pydrat, WRONG 0.

## Instance sets

### Set files (`sets/*.txt`)

One instance per line, `<path> [sat|unsat|unknown]  # comment` (`family=<name>` in the comment
sets the family shown in summaries); `@include <set>` includes another set.  `run.py --set NAME`
(repeatable) takes a name in `sets/` or a file path.

| set | instances | content |
|---|---|---|
| `gate` | 58 (31 sat / 27 unsat) | the correctness gate |
| `tiny` | 27 (15 / 12) | generated, committed (`instances/tiny`) |
| `small` | 31 (16 / 15) | generated, committed (`instances/small`) |
| `medium` | 25 (11 / 14) | generated into `<cache>/generated/medium` (`generate.py --tier medium`) |
| `satlib_random` | 380 (200 / 180) | first 20 of every SATLIB uf/uuf group (20..250 variables) |
| `satlib_structured` | 396 (291 / 105) | structured SATLIB families (flat/sw: first 10 per group) |
| `satlib` | 776 | both |
| `dev_candidates` | 120 (60 / 60) | GBD SAT Competition 2022-2025 main-track candidates (see below) |

The complete SATLIB lists (6399 random, 2106 structured) are written to
`<cache>/satlib/all_random.txt` and `all_structured.txt` (`--set <that file>`).

### Generated families (`generators/`)

Deterministic (SHA-256-seeded RNG that only uses `getrandbits`), names
`<family>_<tier>_<params>[-s<seed>]`.  Statuses are known **by construction** wherever possible;
random families get theirs from a reference solve (PySAT CaDiCaL for tiny/small, confirmed by
MiniSat for UNSAT; Kissat for medium), recorded in `instances/manifest.json` with solver and
version.  All tiny and small statuses were cross-checked with CaDiCaL 1.9.5 and Glucose 4.1
(`reference/status.json`): no disagreement.

| family | encoding | status | tiny | small |
|---|---|---|---|---|
| `rand3sat` | uniform random 3-SAT, ratio 4.26 | reference (balanced) | n=50: 3+3 | n=100, 150: 2+2 each |
| `rand5sat` | uniform random 5-SAT, ratio 21.1 | reference | | n=50: 1+1 |
| `php` | pigeonhole PHP(n+1, n), pairwise | UNSAT | n=4, 5 | n=7, 8 |
| `xorsat` | random 3-XORSAT, m = n (direct CNF) | GF(2) elimination | n=20: 1+1 | n=60: 1+1 |
| `xorchain` | two XOR chains, different orders, outputs differ | UNSAT | n=12 | n=30 |
| `tseitin` | Tseitin parity on random d-regular graphs | odd charge UNSAT, even SAT | d=3 n=10 (both) | d=3 n=24, d=4 n=16 (UNSAT), d=4 n=40 (SAT) |
| `coloring` | 3/5-coloring, planted k-partite (SAT) or random G(n, m) (reference) | mixed | n=30 | n=60..150 |
| `queens` | n-queens, pairwise at-most-one | SAT | n=8 | n=20, 40 |
| `sudoku` | 5 published 9x9 puzzles; planted 16x16 | SAT | 5 | 1 |
| `addereq` | miter of two differently built ripple adders; buggy variant | UNSAT / SAT | 8 bit | 64 bit |
| `multeq` | miter a*b vs b*a array multipliers; buggy variant | UNSAT / SAT | 4 bit | 6 (UNSAT), 7 bit (SAT) |
| `counter` | BMC of a counter with enable inputs: reach v in T steps | SAT iff v <= T | T=6 | T=40 |

Regenerate with `generate.py` (tiny + small), `generate.py --tier medium` (cache), check
determinism with `generate.py --check` (compares sha256s with the manifest).  Committed instances
total about 1.7 MB.

**Medium tier** (`generate.py --tier medium` writes it into `<main>/benchmarks/cache/generated/
medium`, 25 instances, 75 MB, mostly queens and sudoku; `sets/medium.txt` and the manifest are committed,
so the expected statuses and sha256s are known without regenerating).  Sizes were calibrated so
that Kissat 4.0.4 (through PySAT) needs roughly 1-20 s; the reference times are in
`reference/status.json`:

| instance | status | how known | vars | clauses | Kissat 4.0.4 |
|---|---|---|---|---|---|
| `coloring_medium_n2000-k3-deg4p4` | sat | construction | 6000 | 21200 | 3.0 s |
| `coloring_medium_n500-k3-deg4p65-s0` | sat | reference | 1500 | 5486 | 0.8 s |
| `coloring_medium_n500-k3-deg4p65-s1` | unsat | reference | 1500 | 5486 | 22.8 s |
| `counter_medium_steps1000-target1001` | unsat | construction | 22011 | 74022 | 7.3 s |
| `counter_medium_steps1000-target990` | sat | construction | 22011 | 74022 | 0.4 s |
| `multeq_medium_n24-bug` | sat | construction | 6624 | 21937 | 0.3 s |
| `multeq_medium_n8-ok` | unsat | construction | 672 | 2193 | 3.5 s |
| `multeq_medium_n9-ok` | unsat | construction | 864 | 2827 | 15.1 s |
| `php_medium_n10` | unsat | construction | 110 | 561 | 1.8 s |
| `queens_medium_n100` | sat | construction | 10000 | 1646800 | 7.0 s |
| `rand3sat_medium_n275-k3-ratio4p26-s0` | sat | reference | 275 | 1172 | 0.9 s |
| `rand3sat_medium_n275-k3-ratio4p26-s1` | sat | reference | 275 | 1172 | 0.2 s |
| `rand3sat_medium_n275-k3-ratio4p26-s3` | unsat | reference | 275 | 1172 | 5.9 s |
| `rand3sat_medium_n275-k3-ratio4p26-s5` | unsat | reference | 275 | 1172 | 11.3 s |
| `rand5sat_medium_n60-k5-ratio21p1-s0` | unsat | reference | 60 | 1266 | 5.5 s |
| `rand5sat_medium_n60-k5-ratio21p1-s1` | sat | reference | 60 | 1266 | 0.4 s |
| `sudoku_medium_N6-holes0p7` | sat | construction | 46656 | 3271493 | 3.9 s |
| `tseitin_medium_n40-d4-odd` | unsat | construction | 80 | 320 | 3.7 s |
| `tseitin_medium_n44-d4-odd` | unsat | construction | 88 | 352 | 9.8 s |
| `tseitin_medium_n80-d3-even` | sat | construction | 120 | 320 | 0.2 s |
| `tseitin_medium_n80-d3-odd` | unsat | construction | 120 | 320 | 1.3 s |
| `xorchain_medium_n40` | unsat | construction | 118 | 314 | 4.1 s |
| `xorchain_medium_n48` | unsat | construction | 142 | 378 | 22.5 s |
| `xorsat_medium_n500-m460-s0` | sat | gf2-elimination | 500 | 1840 | 0.2 s |
| `xorsat_medium_n500-m460-s2` | unsat | gf2-elimination | 500 | 1840 | 5.9 s |

Times: wall seconds through `tools/pysat_cli.py` (PySAT 1.9.dev18 `kissat404`, including Python
parsing, which dominates for queens/sudoku), 2 runs in parallel, Apple M4 Pro, 2026-11-03.  The
random SAT instances and a few construction ones are easier than 1 s; `coloring ... -s1` and
`xorchain_medium_n48` take ~22 s.  The difficulty of xorchain and Tseitin instances depends a lot
on the random order/graph (a 44-input chain took 49 s, so it was replaced by 40 inputs).

### SATLIB (`satlib.py`)

Downloads the archives listed on https://www.cs.ubc.ca/~hoos/SATLIB/benchm.html (uniform random
uf/uuf 20-250, flat graph coloring, sw100, blocksworld, logistics, ais, qg, bmc, and the DIMACS
families aim, lran, jnh, dubois, gcp-large, parity, ii, hanoi, bf, ssa, pigeon-hole, pret, and the
Beijing set; ~200 MB extracted).  Statuses come from the SATLIB descriptions ("all
satisfiable"...), from file names (aim `yes`/`no`), and for qg, bmc, jnh and Beijing (101
instances, no status on the site) from reference solves: CaDiCaL 1.9.5 and Glucose 4.1 agree on
all of them (`reference/status.json`).

Quirks (found by reading every file with `lib/dimacs.py`): the uf/uuf files end with `%` and
`0` lines (the reader stops at `%`); all 8 `pret` files end with a stray `0` line after the last
clause, i.e. an empty 161st/401st clause beyond the header's count, which makes them trivially
UNSAT (popso-sat's strict parser rejects the file: "more clauses than the header's 160");
`dubois100` declares 800 clauses but has 598.  `satlib.py` normalizes these files in the cache
(trailing empty clauses beyond the header dropped, header count corrected, a `c` line says so;
the downloaded archives stay untouched in `satlib/_archives`).

### SAT Competition instances from GBD (`gbd.py`)

```sh
.venv/bin/python benchmarks/gbd.py fetch-meta                       # meta.db, base.db, SC runtimes
.venv/bin/python benchmarks/gbd.py select                           # sets/dev_candidates.txt
.venv/bin/python benchmarks/gbd.py download --set dev_candidates    # <= --max-total-mb (1000)
```

What the Global Benchmark Database offers (checked 2026-11-03): `getdatabase/meta` and
`getdatabase/base` are SQLite files.  `meta.db` has per instance (MD5-like GBD hash): file name,
family, author, track (`main_2022` ... `main_2026`, multi-valued), result (`sat`/`unsat`/
`unknown`), proceedings, and `minisat1m` (solved by MiniSat within a minute).  `base.db` has
size features (variables, clauses, uncompressed bytes, clause-length histogram, ...).  Files are
served as `.cnf.xz` from `/file/<hash>` (a HEAD request gives the compressed size), and
`/getinstances?track=...` returns URL lists.  **GBD has no solver runtimes.**  Runtimes come
from the SAT Competition pages: 2022 and 2023 publish per-instance times of all main-track
solvers (`sc2022-detailed-results.zip`, `sc2023-detailed-results.zip`); 2024 and 2025 publish
none (downloads "tbd" / 404).

Main tracks 2022-2025: 1600 instances, 1462 with a known result (sat 678 / unsat 784).

`select` (deterministic) keeps main-track instances with result sat/unsat, `.cnf.xz` <= 50 MB and
uncompressed <= 300 MB (so a 2 GB memory cap is realistic), at most 4 per family, balanced
SAT/UNSAT: 70% **runtime-filtered** instances from 2022/2023 (the public Kissat of that
competition, `kissat-sc2022-bulky` / `kissat-3.1.0`, needed 10-300 s on the competition machines,
and the competition's verified result agrees with GBD's) and 30% **unfiltered** ones from
2024/2025 (no runtime data; `minisat1m=no`, i.e. not trivial).  The result,
`sets/dev_candidates.txt` (120 instances: 60 SAT / 60 UNSAT, 84 filtered + 36 unfiltered, 56
families, 300 MB xz, about 2.7 GB uncompressed), is a **candidate** list: the final dev set
should be fixed after a reference run on this machine (e.g. Kissat 10-300 s), see
`reference.py`.  `reference/gbd_dev_candidates.json` has the details (family, year, sizes,
competition times).  `download` fetches a set's files in order until a size budget, checks them
with `xz -t` and decompresses them next to the `.xz` with the system `xz` (for now; popso-sat's
xz reader is in progress).  So far only 36 of them (85 MB xz) have been downloaded for testing.

## Faster screens: `tools/screen.py`

A 300 s screen spends most of its time on instances nobody solves (81% of sc2026's CPU time at
1000 s, 86% of fresh's), and an option that is off by default leaves the search of most
instances unchanged. Screens therefore run in up to three steps; release gates and the
BENCHMARKS tables keep the full sets at 1000 s.

1. **Dev subsets** `sets/sc2026_dev.txt` (109 of 168) and `sets/fresh_dev.txt` (57 of 78):
   instances solved by some 1000 s run (ours v0.4.2 / v0.4.3, Kissat 4.0.4), minus those all of
   them solved within 5 s (`screen.py subset`). A screen on them takes about 0.8 h instead of
   1.9 h (sc2026) and 0.5 h instead of 0.9 h (fresh) on the i7 at four jobs. Picked by results, so a
   screen there carries some selection bias; sc2026 stays the held-out set for the gates.
2. **Affected subsets** (`screen.py affected`): both sides run to `--conflicts=N` (default
   20,000); an instance whose conflicts, decisions, propagations, ticks and answer agree is
   unaffected, so its result is the baseline's. Counts, not timings: run it on the M4 while the
   box runs screens. Fingerprints are cached per binary, arguments and limit. --mergepairs
   on fresh_dev: 12 of 57 affected (6 minutes, 2 processes), and they include every instance
   whose result changed in the full screen; the one other change there (goldcrest-and-9, 178
   against 264 s) was box noise: the same search to the last conflict. Raise `--conflicts` for
   changes to passes that run late in the search.
3. **Merge** (`screen.py merge`): the candidate's results on the subset plus the baseline's on
   the rest give a full-set result file for `compare.py` and the usual tables. The baseline is
   a run of the same binary and limits on the same machine; a 1000 s run without proofs
   serves as a 300 s baseline (times up to 300 s are the same).

Options that change the default search everywhere (restarts, phases) affect every instance:
use step 1 only.

## Reference statuses: `reference.py`

```sh
.venv/bin/python benchmarks/reference.py --set tiny --set small --solver cadical195 --solver glucose4
.venv/bin/python benchmarks/reference.py --set satlib_structured --only-unknown -t 120
.venv/bin/python benchmarks/reference.py --set dev_candidates --solver kissat404 -t 300 -j 1
```

Runs PySAT solvers through `tools/pysat_cli.py` (or binaries resolved like `run.py --solver`,
with `--time-arg`), verifies every SAT model, and records per instance and solver: status, time,
time limit, version (e.g. `PySAT 1.9.dev18 cadical195 (CaDiCaL 1.9.5)`), machine and date, plus
a consensus status (`sat` if a model verified, `unsat` if no model and some solver said UNSAT,
`conflict` loudly).  A contradiction with the set file is reported loudly (exit 1).  The file is
rewritten after every instance; recorded pairs are skipped (`--redo` to re-run).

## Stand-in solver: `tools/pysat_cli.py`

Implements popso-sat's CLI contract (PLAN.md) on PySAT: reads `.cnf/.gz/.xz`, prints `s`/`v`
lines, exits 10/20/0, writes text DRAT proofs for solvers with PySAT proof support (CaDiCaL,
Glucose, Lingeling, Maple*), honours `--time-limit` (the solve runs in a worker process because
PySAT's CaDiCaL and Kissat cannot be interrupted from Python) and accepts unknown `--opt=value`
options (e.g. `--deterministic`).  `FAKE_BUG=<kind>` injects defects to test the harness (see its
docstring).

## Proof checker fallback: `tools/pydrat.py`

A forward DRAT checker (RUP, else RAT on the first literal; text and binary DRAT; deletions of
reason clauses ignored as in drat-trim), with drat-trim's output convention.  It checks every
lemma (stricter than drat-trim's backward check, which only checks the lemmas it needs) and is
slow: ~5-20k lemmas/s on gate-sized formulas (CaDiCaL proofs of php 8: 35k lemmas in 3.8 s;
5-SAT n=50 UNSAT: 71k lemmas, > 15 s).  Tested on CaDiCaL and Glucose proofs of all tiny/small
UNSAT instances, truncated and sign-flipped proofs, binary encoding and the time limit.

## Memory and parallelism (shared machine)

* At most `-j 2` for test runs, one runner at a time; every solver, checker and reference process
  is capped at `--mem-limit` (2048 MB by default) by the watchdog.
* Timing runs (A/B) should not share the machine with other heavy jobs; run A and B under the
  same load.
* Large data stays in the main checkout's cache; the disk is not large, so download GBD files in
  budgets (`--max-total-mb`).
