# Changelog

## v0.4.5 — 2026-11-16

Bounded variable addition (BVA) runs when its trial round removes at least 18% of the clauses,
down from 20% (`--bvamin=180`). New options for tier policy and debugging, all off.

On the Intel i7-7700K (Linux, 1000 s, four instances at a time):

| | 0.4.5 | 0.4.4 | Kissat 4.0.4 |
|---|---|---|---|
| sc2026, solved of 168 (SAT / UNSAT) | 110 (45 / 65) | 110 (45 / 65) | 80 (35 / 45) |
| sc2026, PAR-2 (s) | 773.8 | 772.5 | 1152.3 |
| fresh, solved of 78 (SAT / UNSAT) | 51 (31 / 20) | 48 (30 / 18) | 52 (32 / 20) |
| fresh, solved within 300 s | 45 | 45 | 37 |
| fresh, PAR-2 (s) | 785.2 | 833.5 | 818.2 |

0.4.5 loses no instance to 0.4.4 on either set, and its fresh PAR-2 is now below Kissat's. All
65 UNSAT proofs on sc2026 were written; 63 verified within dpr-trim's 3000 s limit; the other
two are the AES proofs of 0.4.3 and 0.4.4. See [BENCHMARKS.md](BENCHMARKS.md).

- **BVA threshold** (`--bvamin=180`, was 200): before BVA rewrites the formula, a trial round
  measures how many clauses it would remove. At 200 per mille, reconf10_22_queen20 was declined
  at 199.96. With 180, three fresh instances are solved that 0.4.4 does not solve:
  reconf10_22_queen20 (SAT, 709 s), and rook-51 and rook-52 (UNSAT, 751 and 749 s), which Kissat
  4.0.4 does not solve within 1000 s. On sc2026, BVA now also runs on snw_16_9_preOpt (SAT),
  which slows it from 196 to 315 s.
- **New options, off by default:**
  - `--dynamictiers=2`: tier limits per search mode, each from the glue of the clauses used in
    that mode;
  - `--tier1keep=0`: tier1 membership follows the current glue and limit instead of keeping
    tier1 clauses for good. With `--dynamictiers=2 --tier1age=31`, conflicts were about 15%
    cheaper, but runs needed more of them (sc2026 dev subset, 300 s: 81 against 86).
  - `--dumpsimplified=N` (debugging): writes the irredundant formula at the first root-level
    decision after N - 1 conflicts as DIMACS and stops, so other solvers can be run on our
    simplified formula.

## v0.4.4 — 2026-11-16

Elimination rounds merge clause pairs that differ in one sign, on by default. This finds the
compact form of truth-table encodings. New options for longer elimination before search,
repeated substitution, sweep order and BVA matching, all off.

On the Intel i7-7700K (Linux, 1000 s, four instances at a time):

| | 0.4.4 | 0.4.3 | Kissat 4.0.4 |
|---|---|---|---|
| sc2026, solved of 168 (SAT / UNSAT) | 110 (45 / 65) | 109 (44 / 65) | 80 (35 / 45) |
| sc2026, PAR-2 (s) | 772.5 | 784.1 | 1152.3 |
| fresh, solved of 78 (SAT / UNSAT) | 48 (30 / 18) | 47 (29 / 18) | 52 (32 / 20) |
| fresh, solved within 300 s | 45 | 44 | 37 |
| fresh, PAR-2 (s) | 833.5 | 858.7 | 818.2 |

0.4.4 loses no instance to 0.4.3 on either set. All 65 UNSAT proofs on sc2026 were written; 63
verified within dpr-trim's 3000 s limit; the other two are the AES proofs of 0.4.3, which were
verified without the limit. See [BENCHMARKS.md](BENCHMARKS.md).

- **Clause pair merging** (`--mergepairs=1`, on): at the start of each elimination round,
  irredundant clauses over the same variables whose signs differ in exactly one place are
  replaced by their resolvent. Clauses are grouped by size, largest first, and by variable set.
  The resolvents join the next size down, so a full truth table collapses step by step.
  - circuit_32in32out_with_64gates (fresh, SAT): 64 gates, each written as its 16,256 forbidden
    assignments. 921,795 merges in the first round leave 38,563 irredundant clauses. Solved in
    61 s on the i7 (0.4.3: unsolved at 1000 s; Kissat 98 s).
  - sc2026: QuasiGroup-4-12_c18 is solved again (435 s). Within 300 s, as-p31-l12-o9-56 and
    sum_of_3_cubes_50_bits_91 are new; bench_1278 goes from 18 to 131 s.
- **New options, off by default:**
  - `--eliminateextend`, `--eliminateextendmax`: the first elimination round runs past its
    budget, one budget-sized chunk at a time, while the last chunk eliminated enough
    (goldcrest-xor-11: 4.7k to 258k variables eliminated before search);
  - `--substituterounds`: substitution passes in a row while each finds equivalences;
  - `--sweeporder`: the order of the swept variables;
  - `--bvalitcap`, `--bvarealtarget`, `--bvaretries`, `--bvarequeue`: BVA matching budget and
    order (mod4block_3vars_7gates: the BVA trial removes 39k clauses instead of declining).
- **Development:** `benchmarks/tools/screen.py` runs a candidate option first on the instances
  it changes (`affected`: compare short runs with and without it) and on two dev subsets of
  sc2026 and fresh, before the full sets.

## v0.4.3 — 2026-11-15

Elimination before search keeps multiplier circuits intact, and bounded variable addition (BVA)
may run past its budget while it is productive. Both are on by default. New options for
truth-table encodings and ternary clause pairs, all off.

On the 78 instances of the held-out fresh set (2024 and 2025 main tracks, families never used for
tuning; Intel i7-7700K, Linux, 1000 s), all three solvers ran on the same machine:

| | 0.4.3 | 0.4.2 | Kissat 4.0.4 |
|---|---|---|---|
| solved (SAT / UNSAT) | 47 (29 / 18) | 44 (29 / 15) | 52 (32 / 20) |
| solved within 300 s | 44 | 41 | 37 |
| PAR-2 (s) | 859 | 935 | 818 |

0.4.3 gains three instances and loses none. Kissat is still ahead at 1000 s on these families.
On the 168 SAT Competition 2026 instances, 0.4.3 solves 109 (0.4.2 110, Kissat 4.0.4 80): the only
difference to 0.4.2 is QuasiGroup-4-12_c18, which flips with the search order. All 65 UNSAT
proofs were verified. See [BENCHMARKS.md](BENCHMARKS.md).

- **First-round gate limit** (`--eliminategatelim1=3`, `--eliminategatekinds1=4`, on): in the
  elimination round before search, eliminations by an ITE definition may produce resolvents of
  at most 3 literals. Eliminating multiplexers with long resolvents hid the structure of
  multiplier circuits.
  - gm24sparrc and gm28sparrc (multiplier verification, UNSAT) are refuted in 1 and 3 s. 0.4.2
    does not solve them in 1000 s; Kissat takes 9 and 15 s.
  - Applied to all definition kinds, the limit loses asconhash H7 and others on sc2026. Hence
    the default mask of ITE definitions only.
- **BVA extension** (`--bvaextend=8`, `--bvaextendticks=40000`, `--bvaextendreal=1`, on): a BVA
  round may run up to 8 times its budget while each further eighth removes a clause per 40,000
  ticks. This applies to trial rounds and to the real round after a trial.
  - korf-17: 112-160 s on three seeds before, 36-45 s now (Apple M4 Pro).
  - aes_equiv_encry_3_rounds: 601 to 340 s. post-cbmc-aes-ee-r2: 175 to 96 s (i7, sc2026 run).
  - **Proof checking cost:** the proofs are smaller but check slower. dpr-trim checks the
    post-cbmc-aes-ee-r2 proof (221 MB, 272k PR lemmas in the core) in 2,043 s, against 194 s for
    0.4.2's proof (401 MB). `--bvaextend=1 --bvaextendreal=0` restores the 0.4.2 behaviour.
- **New options, off by default:**
  - `--mergepairs`: in elimination rounds, irredundant clauses over the same variables that
    differ in one sign are replaced by their resolvent (truth-table encodings);
  - `--congruencetern`: binary resolvents of ternary clause pairs (a b c) (a b -c) before each
    congruence call;
  - `--eliminateclslim1`: a resolvent size limit for the first elimination round;
  - `--eliminatefloor`: the first elimination round's effort floor.

## v0.4.2 — 2026-11-14

Two new defaults: a model walk that backs off while it is far from a model, and variable
renumbering for memory locality. Propagation skips runs of watches with a true blocking literal,
with an unchanged search. New options for learned-clause tiers, decision orders on circuits and
BVA budgets, all off.

On the 168 SAT Competition 2026 instances (Intel i7-7700K, Linux, 1000 s, every UNSAT answer
checked with its proof):

| | 0.4.2 | 0.4.0 | Kissat 4.0.4 |
|---|---|---|---|
| solved (SAT / UNSAT) | 110 (45 / 65) | 98 (37 / 61) | 80 (35 / 45) |
| PAR-2 (s) | 775 | 926 | 1152 |

On 78 instances of the 2024 and 2025 main tracks from families never used for tuning (Intel Xeon
E5-1650 v2, Linux, 1000 s), 0.4.2 solves 43 and Kissat 4.0.4 solves 49. The lead on sc2026 does
not carry over to these families; see [BENCHMARKS.md](BENCHMARKS.md).

- **Model walk** (`--walkmodel=2`, on): the DDFW walk that looks for models (`--walkmode=3`)
  backs off while far from a model. After k walks in a row whose best assignment leaves more
  than about sqrt(clauses) clauses falsified, it skips the next 2^k - 1 calls.
  - sc2026 (300 s, i7): 93 solved against 92; T92 is solved again.
- **Renumbering** (`--renumber=1`, on): where the input numbering looks random, variables are
  renumbered breadth-first over the clauses so that neighbours sit close in memory. The decision
  order, proofs and models keep the input numbering.
  - sc2026 (300 s): 93 against 92 on the i7, 104 against 103 on the EPYC.
- **Propagation** skips runs of watches whose blocking literal is true in a tight loop, with
  an unchanged search. `--propstats` prints watch and blocker counts.
- **At competition length:** all of sc2026 at 5000 s on the AMD EPYC 4465P: 130 solved
  (55 / 75), PAR-2 2650. The 0.4.1 search solves 125 (2848) and Kissat 4.0.4 110 (3893).
- **New options, off by default:**
  - learned-clause tiers: `--tier1limit`, `--tier1limitage`, `--tier1revive`,
    `--tier1keepglue`, and `--tierstats` (statistics only);
  - learned binary clauses: `--binstats` (statistics only) and `--binreduce` (transitive
    reduction);
  - decision orders for circuits: `--stablereorder`, `--queuescores`; circuit elimination:
    `--eliminatecircuit`;
  - `--vivifytier1`: tier-1 vivification in a pass of its own;
  - `--bvaextend` and `--bvaextendticks` also apply to the plain BVA order: a trial round may
    run past its budget while it is productive.

## v0.4.1 — 2026-11-08

BVA during search, a solver for linear equations mod p, congruence closure over XOR and ITE gates,
changes to vivification and sweeping, and a walk that looks for models, all on by default. Faster
propagation and inprocessing, lower memory use and faster-checking proofs, all with an unchanged
search.

On the 168 SAT Competition 2026 instances (AMD EPYC 4465P, Linux, 1000 s), 0.4.1, 0.4.0 and Kissat
4.0.4 ran side by side:

| | 0.4.1 | 0.4.0 | Kissat 4.0.4 |
|---|---|---|---|
| solved (SAT / UNSAT) | 108 (43 / 65) | 101 (38 / 63) | 82 (35 / 47) |
| PAR-2 (s) | 783 | 896 | 1132 |

All 65 of 0.4.1's UNSAT answers were verified with their proofs. See [BENCHMARKS.md](BENCHMARKS.md).

- **BVA during search** (`--bvasearch`, on): elimination rounds after the first run BVA again,
  on literals of touched variables and least frequent first, when the first round added
  variables. Elimination keeps BVA variables unless removing one adds no clause.
  - sc2026 (300 s): 87 solved against 84.
  - The three schooltt UNSAT instances, which only Kissat solved before, take 39–142 s.
- **Linear equations mod p** (`--linmod`, on):
  - It finds exactly-one domains of 3, 5 or 7 values, and constraints whose allowed tuples are
    exactly one equation mod p.
  - It solves the system by Gaussian elimination over GF(p) and tries the solution as a model.
  - The four linear-equations instances of sc2026 (unsolved by v0.4.0 and Kissat 4.0.4 at
    1000 s) take 0.01 s, as do all 20 known instances of the family.
  - Elsewhere it finds no equations: median cost 0.4 ms, at most 0.6 s.
- **Congruence closure over XOR and ITE gates** (`--congruencegates`, on), and duplicate binary
  clause removal (`--dedup`, on).
  - linked_list: 29 → 19 s (M4).
  - T92: 150 → 138 s.
- **Vivification** deletes the clauses that the conflicting clause subsumes (`--vivifysubsume`)
  and decides literals by occurrence counts (`--vivifysort`). Both are on.
- **Sweeping** (`--sweepknown`, `--sweepphase`, `--sweepqueue`, on):
  - it skips pairs whose binary clauses are already in the formula;
  - it keeps Kitten's phases and queue between calls;
  - minandmaxor128: sweep time −41%.
  - sc2026 (300 s): 84 solved against 81, including jkkk-one-one-11-38 (Kissat-only before).
- **XOR substitution reversal** (`--xorsub`, on): xor_op_n40_d3 is refuted in 0.4 s.
- **Elimination growth cap** (`--eliminategrowth=100` above 10M irredundant literals): cabp k290
  peak memory 3.5 → 1.4 GB.
- **Walk for models** (`--walkmode=3`, on): the ProbSAT walk still sets the phases. Then a DDFW
  clause-weighting walk (Ishtaiwi et al. 2005; Chowdhury, Codel and Heule 2023) runs from its
  best assignment, only to look for a model.
  - sc2026 at 300 s on the EPYC: 103 solved against 101.
  - schooltt-5-7-11 (SAT) solves in 4 s.
  - UNSAT instances are about 3% slower.
- **Speed, with an identical search:**
  - Propagation:
    - the assignment is inlined;
    - analysis uses radix sorts;
    - backtracking is cheaper;
    - the watch lists share one pool (watch memory −28 to −47%).
  - Inprocessing: Kitten, sweeping, the walk, the parser, the Gauss-Jordan refutation check,
    XOR / ITE extraction, congruence classes and substitution.
  - On the M4: −5% user time on 15 instances each for the propagation and the inprocessing
    changes; start-up −16%.
  - On the i7, the software prefetches cost time (one of them about 20%), so they are now
    compiled only on 64-bit ARM. The propagation prefetch is also behind `--prefetch`, off.
- **Memory, with an identical search:**
  - the model-check copy of the input is compressed (velev 204 → 92 MB);
  - the watch pool is compacted at restarts and after elimination;
  - the walk reads clauses in place;
  - XOR rows are stored by size;
  - per-variable arrays grow by an eighth when BVA adds variables.
  - Peak bytes in use: velev 1456 → 1203 MB, as-p147 1650 → 1327 MB, T92 3016 → 2804 MB.
  - `--reportmem` shows the heap in use.
- **Proofs** (a checker timeout counts as unsolved):
  - Counting-certificate proofs delete the clauses their PR steps do not need. dpr-trim time:
    exam_90_80 1031 → 248 s, miles1500 683 → 177 s, chnl-030x091 21.9 → 0.9 s.
  - Root-level strengthening no longer writes an add / delete pair: constraints_17's proof is
    77% smaller and dpr-trim needs 2.7× less memory.
  - Substitution deletes each old clause right after its rewritten copy.
- **Limits:** the time limit and SIGINT / SIGTERM are honoured inside every inprocessing pass, and
  the solver stops within about 0.4 s. Before, an inprocessing pass could run on: satcoin went
  10.5 s past a 300 s limit.
- **New options, off by default:**
  - `--renumber`: internal variable renumbering for memory locality; proofs and models keep the
    input numbering.
  - `--walkmode`: DDFW clause-weighting walks.
  - `--queueorder`: initial decision order.
  - `--eliminateheap`, `--eliminatecomplete`, `--eliminatelongskip`, `--eliminatetouched`.
  - `--chrono=2`, `--chronounits`, `--randec`.
  - `--bvasched`, `--bvaextend`, `--subsumerel`, `--bvavarsrel`.
  - `--tier1age`: deletes tier-1 clauses left unused.
  - `--stopfault` (testing).
- **Determinism:** ties in three sorts are broken deterministically, so the Linux box and the Mac
  run the same search.

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
