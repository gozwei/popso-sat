# Changelog

## v0.4.0 — 2026-11-06

Counting certificates: pigeonhole, parity and counting formulas are refuted before search, with
proofs in the DPR format. Gauss-Jordan elimination on XOR constraints. Shorter learned clauses,
a larger BVA budget, and focused-mode restarts without bursts. All are on by default.
On a sample of 168 SAT Competition 2026 instances (Intel i7-7700K, Linux, 1000 s): 98 solved,
PAR-2 926 s (0.3.3: 67, 1304 s); all 61 UNSAT answers were verified with their proofs. On the
Apple M4 Pro (120 s, run in alternation with 0.3.4 on a shared machine): unsat26 22 solved
(0.3.4: 22), tune 25 (25), held-out validation 21 (20). See [BENCHMARKS.md](BENCHMARKS.md).

- **Counting certificates** (`--counting`, on by default):
  - Before search (and before BVA / BVE, which re-encode the at-most-one cliques), the solver
    looks for a pigeonhole system (PHP, functional PHP, clique formulas), a parity system
    (perfect matching of an odd complete graph), Count^3, clique-colouring or a relativized
    pigeonhole over the whole formula, and for pigeonhole systems inside larger formulas
    (graph colouring with a clique larger than the number of colours, register allocation). A
    sign map handles shuffled polarities.
  - An embedded pigeonhole is refuted in isolation: a separate solver refutes the subsystem,
    and the proof deletes the other clauses on its variables before the sub-proof.
  - A structure found is refuted with symmetry-style PR clauses (2 literals, 4-literal
    witnesses) plus RUP units: polynomially many lines where resolution needs exponentially
    many steps.
  - Every PR clause is checked by the solver before it is written. A failed check writes
    nothing and abandons the structure. Inputs with duplicate literals or tautologies are left
    alone (dpr-trim would read a different formula).
  - Without a structure the search is unchanged; the pass costs a median of 0.000 s and at most
    0.8 s on 265 instances.
  - sc2026 (1000 s): 27 of the 168 instances are refuted this way, in at most 2.5 s; 0.3.3
    solved 2 of them. The families: chnl, count, clique-coloring, clique formulas, coloring,
    graph colouring, exam scheduling, fpga routing, register allocation, sudoku-php and
    relativized pigeonhole. The homer instances (independent pigeonholes), which 0.3.4 solves
    with BVA in 20-127 s (M4, 300 s runs), take 0.01 s.
  - Proofs: PR lines are written in both the text and the binary format. Check them with
    dpr-trim (-L, then cake_lpr for a verified check); drat-trim rejects them. All 27 sc2026
    refutations pass the competition chain (dpr-trim -L, then the verified cake_lpr): proofs of
    0.01-3.2 MB, checked in 0.1 s to 1 h (exam_90_80: dpr-trim 2729 s, cake_lpr 886 s).
- **Gauss-Jordan elimination** (`--gauss`, on by default):
  - XOR constraints are taken from complete clause encodings of up to 6 variables, also where up
    to a quarter of an encoding is subsumed by shorter clauses.
  - An inconsistent XOR system is refuted before search (`--gaussproof`), with a DRAT proof
    that sums the XORs as chains of extension variables: lights-out and Tseitin formulas
    (urquhart3_25bis 4.1 s → 0.01 s).
  - Otherwise, if the XORs cover a tenth of the clauses (`--gaussmin`), a detached copy of the
    solver with Gauss-Jordan propagation searches besides the main one. It writes no proof,
    and only a model can come back from it. Its share of the search effort adapts
    (`--gaussadapt`): it doubles while Gauss-Jordan finds a tenth of the copy's conflicts,
    halves below 1%, and the copy stops below 1/64.
  - Results: mdp-28-10-sat not solved in 120 s → 0.03 s; on sc2026, two satisfiable lights-out
    instances (0.03 s), par32-4 and par32-4-c (25 and 6 s), two-trees-1023v (0.01 s) and
    mod2-rand3bip (96 → 0.01 s).
- **Shorter learned clauses** (`--shrink=2` by default): learned clauses are shrunk to block
  UIPs, including lower-level reason literals that are implied.
  - Learned clauses had been up to 3x longer than Kissat's where clauses are long
    (battleship-14-26 157 -> 43 literals, station-repacking 72 -> 23).
  - Propagation is faster with shorter clauses: station-repacking 41k -> 113k conflicts/s
    (Kissat 59k), 3.2M -> 9.4M propagations/s (Kissat 9.7M).
- **Focused-mode restarts** (`--restartgrow=1` by default): the minimum interval between restarts
  grows with the decimal logarithm of the restart count. Restarts no longer come in bursts
  (3.5-10 conflicts per restart before, 9-15 now). Paired M4 screening at 120 s: one more
  instance on each small set.
- **BVA budget** (`--bvaticks` 100M floor; `--bvavars` no cap): BVA's budget counted no binary
  clauses and its variables were capped at a tenth of the formula's. On binary-heavy formulas
  the trial stopped at 0.3% where Kissat's factoring removes more than half the clauses.
  rpoc_xits_09 (bioinformatics, sc2026): BVA now removes 104k clauses and adds 29k, and the
  instance is refuted in 10 s (not solved in 1000 s before).
- **Robustness:**
  - Running out of memory gives `s UNKNOWN` everywhere: setup, parsing, the xz dictionary,
    model output (written through a fixed buffer), and the first exception thrown (macOS
    libc++abi allocated its exception state then). Tested with allocation-failure injection
    and heap limits (benchmarks/fuzz/oomfuzz.py), and with `ulimit -v` on Linux.
  - `--mem-limit` counts the peak resident size of the process and stops at 7/8 of the limit,
    also inside elimination rounds.
  - All-options fuzzing (benchmarks/fuzz/all_options.txt): 301,555 formulas plus 16,748 under
    ASan + UBSan, no wrong answer, crash or rejected proof.
- **Probing:** `--probeuip` (off) learns the first UIP of a failed probe.
- **Benchmarks:** run.py and fuzz.py check proofs with dpr-trim when it is built.

## v0.3.4 — 2026-11-05

Bounded variable addition on by default, with a trial that keeps it to the formulas it helps;
proof output that never claims unsatisfiability with an incomplete proof; and a held-out
benchmark set of 168 SAT Competition 2026 instances.
On the Apple M4 Pro (120 s): unsat26 22 solved, PAR-2 56.2 s (0.3.3: 21, 63.3; Kissat 4.0.4:
22, 52.9); tune 25, 47.3 s (23, 61.6; Kissat 26, 45.5); held-out validation unchanged (21, the
same search as 0.3.3). See [BENCHMARKS.md](BENCHMARKS.md).

- **BVA trial rounds** (`--bvamin`, default 200 per mille; BVA now on by default):
  - Before replacing anything, BVA runs its matching once without changes. It only marks the
    clauses a replacement would remove, and sums the reduction.
  - The replacements are made only when that reduction reaches a fifth of the irredundant
    clauses.
  - BVA pays off on formulas dominated by at-most-one cliques (battleship, stb argumentation,
    pigeonhole-like counting), where it removes 35–65% of the clauses. On large formulas where
    it removes a few percent, it only perturbed the search (spg: 2 variables added, 8 → 82 s).
  - A declined trial leaves the run exactly as with BVA off.
  - Results:
    - Tuning sets: battleship-13-13 timeout → 4 s, stb DS-ST timeout → 15 s.
    - The 32 validation instances: none passes the trial.
    - The 16 of 168 SC2026 instances that pass (M4, 300 s): 4 → 8 solved, PAR-2 457.7 → 319.0 s.
- **Proof output:**
  - A failing proof write (for example a full disk) no longer aborts the solver. The proof is
    marked failed and the solver goes on.
  - The proof file is flushed and closed before the answer is printed. If anything failed, an
    unsatisfiable result is reported as `s UNKNOWN`; satisfiable answers stand, since their
    models are checked.
  - Exceptions inside the search print `s UNKNOWN` instead of terminating.
  - `run.sh` creates the proof directory if it is missing.
  - Proofs were checked with the verified chains used by the SAT Competition (dpr-trim with
    cake_lpr, and gratgen with gratchk) as well as drat-trim, all VERIFIED. `build.sh` builds
    without CMake in Ubuntu 24.04 (g++ 13) and in the organizers' current image (g++ 15).
- **Benchmarks:**
  - `benchmarks/gbd.py heldout` writes `sets/sc2026.txt`: 168 instances of the SAT Competition
    2026 main track from 87 families.
  - The sample is deterministic and not filtered by any solver's runtime, and it excludes the
    families tuned on.
  - `compare.py --per-family`.
- **Opt-in:** `--restartgrow`. The minimum interval between focused-mode restarts grows with
  the logarithm of the restart count. With a fixed interval of one conflict, restarts came in
  bursts (3.5–10 conflicts per restart, against 9–19 in Kissat).
- **Statistics:** BVA trials and the rounds they allowed; `-v -v` prints each trial's estimate.

## v0.3.3 — 2026-11-05

Equivalences from random simulation, and congruence closure to a fixpoint in one call.
On the idle Apple M4 Pro (120 s): unsat26 21 solved, PAR-2 63.3 s (0.3.2: 21, 64.9; Kissat
4.0.4: 22, 52.9); tune 23, 61.6 s (23, 63.2; Kissat 26, 45.5); held-out validation 21, 104.6 s
(21, 103.2; Kissat 24, 83.9), with one unsatisfiable instance more and one satisfiable fewer.
See [BENCHMARKS.md](BENCHMARKS.md).

- **Simulation equivalences** (new, on by default, `--simeq`): AND gates and XOR constraints of
  3 to 5 variables are extracted and evaluated on 512 random input vectors; variables with
  equal or complementary signatures, and variables constant in every vector, are candidates.
  They are proven bottom-up by Kitten on windows of their fan-in cones (depth `--simeqdepth`,
  default 16) that include the binary clauses of the pairs proven so far, so the windows stay
  small where two copies of a circuit meet; the proofs go to the DRAT output as in sweeping.
  Sweeping finds equivalences only inside one variable's environment and congruence closure
  only between gates with identical inputs; simulation finds functional equivalences between
  distant parts of a circuit, as in a miter of two implementations. beempgsol2b1 (BEEM model
  checking) is solved in 1 to 4 s instead of 13 to 16 s (Kissat 4.0.4: 9 s). If-then-else
  gates are supported but off (`--simeqite`: more equivalences on pipeline instances, but
  slower overall).
- **Congruence closure** within one call: a union-find over literals, re-hashing only the gates
  whose inputs were merged, instead of matching gates on their inputs once per call with
  substitution in between (chains of gates in two copies of a circuit merged one level per
  call, up to 16 calls per round). manol-pipe-f7nidw: congruence 6.6 -> 1.4 s, substitution
  2.4 -> 0.5 s. `--congruenceclosure=0` restores the earlier matching.
- **Statistics:** a simulation line, Kitten solves and ticks of sweeping, and with `-v -v` a
  line per congruence round.

## v0.3.2 — 2026-11-05

Sweeping rework, adaptive sweep environments, and new inprocessing techniques (opt-in until
they gain in A/B runs). On 26 unsatisfiable competition instances (idle Apple M4 Pro, 120 s)
0.3.2 solves 21 instead of 20 with a 12% lower PAR-2 (Kissat 4.0.4: 22); on the 29-instance
tuning set both versions solve 23 (Kissat 26); on the 32 held-out validation instances 0.3.2
solves 21 and 0.3.0 22 (the difference is one satisfiable instance), Kissat 24. See
[BENCHMARKS.md](BENCHMARKS.md); benchmark tables now come from an idle machine (the Linux
machine of earlier tables is shared, and its times varied by a factor of 1.3 between sessions).

- **Sweeping** checks equivalences within classes of all environment literals, refined by the
  models Kitten finds (with literal flips and random phases), instead of pairs with the swept
  variable only (the candidate scheme of Kissat's sweeping). A variable proven equivalent
  leaves the later candidate classes of the round (before, equivalences were proven again and
  their binary clauses added again).
- **Sweep environments grow** (on by default, `--sweepgrow`): after a full cycle over the
  variables that found less than one unit or equivalence per 100 swept variables, the
  environment limits double (variables, clauses) and the depth grows by one, at most three
  times (`--sweepgrowmax`). Two hardware-verification instances of the unsatisfiable A/B set
  that need large environments (beempgsol2b1, 6s186_Iter20) are now solved within 120 s.
- **New, off by default:** unhiding (time stamps on the binary implication graph: failed
  literals, transitive reduction, hidden tautologies and hidden literals; `--unhide`),
  vivification deleting irredundant clauses implied by the other irredundant clauses
  (`--vivifyasym`), substitution right after sweeping (`--sweepsubst`), vivification
  instantiation and implied deletion (`--vivifyinst`, `--vivifyimplied`), tier-3 vivification
  (`--vivifytier3`), shrinking with implied lower-level literals (`--shrink=2`), chronological
  backtracking (`--chrono`), BVA 3-hop tie-breaking (`--bvahops`), BVA in every elimination
  round (`--bvaevery`), BVA variables protected from elimination (`--bvaprotect`), BVA before
  or after the first round's eliminations (`--bvafirst`) and its budget floor (`--bvaticks`).
  New test sets: unsat26 (unsatisfiable A/B set) and a held-out validation set. BVA itself
  stays off: with sweep growth it gained on both tuning sets but lost 6 of 32 held-out
  instances.
- **Speed:** the decision heap stores a copy of the score (same order, faster sifting);
  congruence closure filters gate candidates before sorting (ncc: 2.3 -> 0.55 s per call).
- **Fixes:** BVA checks its budget within a matching step (on formulas with few variables and
  many clauses one step overshot it: DivS_862_11 spent 1.1 s in BVA finding nothing, now
  0.04 s). A SIGTERM delivered twice (GNU timeout signals the process and its process group)
  no longer makes the solver exit without its answer line; only a second Ctrl-C does.
- **Statistics:** wall time per pass ("c profile" lines with `-v`); the sweeping line shows the
  current environment limits and growth level.

## v0.3.1 — 2026-11-04

- Documentation only: BENCHMARKS.md and the README add a held-out validation set (32 competition
  instances from 32 families, not used for tuning, [benchmarks/sets/validation.txt](benchmarks/sets/validation.txt)).
  On it popso-sat 0.3 solves 17 and Kissat 4.0.4 23 (120 s), so the near-parity on the 36
  tuning instances overstated where popso-sat stands. The solver is unchanged from v0.3.0.

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
