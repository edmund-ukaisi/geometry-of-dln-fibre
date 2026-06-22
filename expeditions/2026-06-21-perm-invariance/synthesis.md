# synthesis.md — `perm-invariance` (controller's internal integrative ground)

Recovery substrate (recover from `brief + priorities + threads + synthesis`). Flush every tick. In-repo only.

## Quest (one line)
Prove `(C,θ)` permutation-invariance (Cor 5.10) — `cCodim`/`numTop` depend only on the multiset of `d` —
via a zero-cited combinatorial route (not the equivariant-cohomology Thm 5.5).

## State (2026-06-21 — SETUP)
- Branch `expedition/perm-invariance` off `dev` (= rlct-payoff merged, PR #5 / merge `52995d1`). Green
  baseline 3679 jobs, 0-sorry, axiom-clean (tree identical to dev; `.lake` valid).
- Controller in the (legacy-named) `voigt-discharge` worktree (main checkout is the live aoyagi session) ⟹
  serial Lean-writers. **No build yet — sizing pass FIRST (P0).**
- Worktree hygiene: removed merged-stale `c-theta`/`ext-codimension`; the rest of the sprawl is other live
  sessions' (aoyagi-*, agent-*, fm/fm-2, d1-scope[uncommitted], semantic-audit, /tmp) — left for the operator.

## LANDED (consumable)
`Core.CTheta` (cCodim/numTop/codimForm/kostantPartitions, cCodim_rankShift) · QIP Thm 6.1 (monotone d) ·
explicit Thm 7.10 (CThetaValue/Explicit) · CCodimZeroMono/Strict (dim-monotonicity) · the geometric (C,θ)
bridges (SigmaComponents/ThetaComponentCount/CThetaGeometric).

## Hard piece / suspicion
The heart is `cCodim d = cCodim (sort d)` for ALL `d` (the QIP/explicit forms are monotone-`d`-only). The
roadmap flags Cor 5.10 "a genuine lift, NOT free," derived in the paper via equivariant cohomology (Thm 5.5).
The sizing pass must find/confirm the independent combinatorial route (codimForm/Kostant symmetry under
permuting `d`) and whether it avoids Thm 5.5.

## Carried meta-lessons (from voigt-discharge + rlct-payoff)
Size hard pieces before building · serial Lean-writers (controller-in-worktree) · decorrelated Codex/pen-and-paper
on hard/at-risk steps · green-gate + AUDIT + name=content every result · flush synthesis every tick · controller
stays executive (delegate object-level).

## Next action
Dispatch the sizing pass (thread 01, pen-and-paper, decorrelated Codex) → re-scope the ladder → build.

## 2026-06-22 — SIZING VERDICT (thread 01): NO short zero-cited route to full Cor 5.10 → SCOPE FORK
Permutation invariance is TRUE (re-confirmed exactly: (1,2,3) perms → (C,θ)=(2,1); (1,2,2,3) → (2,2); single
adjacent-swap 0/3868 fails; non-monotone-sort 0/1345). But the route analysis (exact algebra; Codex endpoint
was down) gives a genuine scope-surprise:
- **(a) adjacent-transposition (zero-cited): TRUE but it is an OPEN PROBLEM.** No value-preserving Kostant
  bijection (cardinalities differ 2932/3868 — the paper's own line-1122 obstruction), no bounded surgery
  (edit radius unbounded, grows with |d|) ⟹ a large min-argument tide, HARDER than the landed
  CCodimZeroMono+Strict pair. AND a purely combinatorial proof of the underlying q-series identity is
  "an open problem the authors say they lack" — so this route = NEW RESEARCH, not formalising known math.
- **(b) reduce-to-sort: not independent** — its content is (a) or (d) (the paper's Thm 6.1 itself uses Cor 5.10
  for non-monotone d; circular).
- **(c) full Kostant bijection: REFUTED** (cardinalities differ). EXCEPTION: **order-reversal `[a,b]↦[N−b,N−a]`
  IS a clean codimForm-preserving bijection (0/11795)** ⟹ `(C,θ)(d)=(C,θ)(reverse d)` is a CHEAP zero-cited
  lemma (order-2 subgroup only).
- **(d) Thm 5.5 Pochhammer product: CERTIFIED, short to the headline, but CITED.** `Q^r_d = P_r ∑_s (−1)^s
  q^{C(s,2)} P_s P_{d−r−s}`; `∏_i P_{d_i−r−s}` is manifestly multiset-symmetric ⟹ one-line Cor 5.10. But its
  DERIVATION is equivariant-cohomology (Mathlib-absent) — a Cited layer (like Aoyagi / Lemma 4.6).

**SCOPE FORK (operator decision — the brief's sanctioned scope-surprise close):**
(A) CITE Thm 5.5 (named interface, ethos-consistent) → full Cor 5.10 Cited + order-reversal + geometric transfer
    zero-cited. Short, honest. [RECOMMENDED — zero-cited is an open problem the authors lack.]
(B) Attempt zero-cited route (a) — NEW research (combinatorial proof the authors don't have); high-risk, multi-week.
(C) Scope down: land order-reversal + geometric transfer zero-cited; roadmap full Cor 5.10 (no cite-interface).
Order-reversal fragment is landable zero-cited bedrock regardless. SURFACED to operator.

## 2026-06-22 — AMBITIOUS RE-SCOPE (operator: "what is your ambitious suggestion")
Operator asked for the ambitious version. DECISION: do NOT cite Thm 5.5 by default — SWING for the OPEN
PROBLEM (a zero-cited combinatorial proof of Cor 5.10, which the authors lack), with a graceful Cited fallback.
Prize if it cracks: the WHOLE combinatorial side zero-cited + general (all d) — Poincaré series closed form,
explicit (C,θ) for all d (extends monotone-only Thm 7.10), Cor 5.10 as a one-line corollary; + a new
math contribution. Our EDGE: the strict-cert corner-pair rigidity (minimisers = corner pairs only; 256521/256521).

Two-pronged DECORRELATED bounded probe LAUNCHED (background):
- **thread 02 (probe-direct):** corner-pair rigidity → manifestly-symmetric closed form for (C,θ) on all d;
  and/or a MIN-LEVEL adjacent-transposition map (weaker than the refuted full Kostant bijection).
- **thread 03 (probe-qseries):** combinatorial/bijective proof of the Thm 5.5 identity (or its lowest-degree
  term θ q^C) — sign-reversing involution / LGV lattice paths / q-Vandermonde / recursion.
Each: exact-arithmetic-verified, Codex-decorrelated, bounded, honest verdict (crack/partial/obstruct).

DECISION RULE: either prong yields a Lean-targetable proof ⟹ formaliser tide for general (C,θ) + Cor 5.10
(zero-cited, the big win). Both stall ⟹ fallback = cite Thm 5.5 as a named interface (like Aoyagi/Lemma 4.6)
+ derive Cor 5.10 + LAND the order-reversal fragment (0/11795, codimForm-preserving bijection) zero-cited.
Order-reversal is bedrock either way. AWAITING the two probe verdicts.

## 2026-06-22 — Q-SERIES VERDICT (thread 03): CRACKED, zero-cited, but a ~6–8 file q-series sub-library
probe-qseries cracked the FULL route, exact-verified (findings.md committed 092d8a6):
  perm-inv ⟸ L0 ⟸ L1 (C,θ)-extraction [CLEAN: Pm coeffs ≥0 ⟹ no cancellation; min-deg=cCodim, coeff=numTop]
  ⟸ L2/Thm5.5 ⟸ S1–S4 chain ⟸ S0=Thm5.6(5gon) ⟸ PEEL induction on N.
- **RECORD CORRECTED:** thread-01's "open problem" is WRONG. Thm 5.6 = RWY 2018 (arXiv:1608.02030), the
  paper's OWN cite [RWY]. PEEL (q-Vandermonde + N=1 Durfee, induction on N) reproves it self-contained,
  equioriented-only (RWY's general Thm 1.7 NOT needed). What the authors lack is only the DIRECT-Kostant-
  bijection form (|M⁺_d|≠|M⁺_σd|, 2932 vs 3868 — blocks any value-preserving bijection); the q-series route
  sidesteps that by proving the generating-function identity and reading off (C,θ).
- **COST:** q-Pochhammer/q-binomial/q-Vandermonde/Durfee ALL absent from Mathlib v4.29 → must BUILD a
  Core.QSeries sub-library. ~6–8 files, ~2–3 wk. Load-bearing: PEEL local transfer identity. Most-likely-
  break: S3 PowerSeries q-binomial inversion / the transfer's q-Vandermonde.

## DECISION SPECTRUM (forming — awaiting probe-direct's size comparison)
- (A) FULL zero-cited q-series: ~6–8 files/~2–3wk. Delivers Cor 5.10 + Poincaré series + general (C,θ) for
  ALL d (extends monotone-only forms) + an UPSTREAMABLE q-series sub-library (Mathlib lacks all of it). Max ambition.
- (A') CITE RWY 2018 for Thm 5.6 (one published hard link, honest named interface like Aoyagi/Lemma 4.6),
  build the rest zero-cited: ~4–5 files (still needs q-series primitives + S1–S4 chain + L1). Saves the PEEL bulk.
- (C) CITE Thm 5.5 directly: ~1 file, Cor 5.10 one-liner. Cheapest, cites most.
- direct route (thread 02): sizing said HARD (no bijection, unbounded radius, harder than landed CCodim pair);
  probe-direct unproductive so far — likely NOT shorter. AWAITING its verdict to confirm.
- order-reversal fragment (0/11795): zero-cited bedrock, land regardless.

## 2026-06-22 — ROUTE DECIDED (operator): FULL ZERO-CITED q-series
Operator chose (A) full zero-cited. Direct route OBSTRUCTED-as-shorter (thread 02: ≥2500 LoC global swap
map, open form). BUILD the Core.QSeries sub-library + reprove RWY's Thm 5.6 via PEEL, zero-cited. Brief
re-scoped (closing criterion + the M1–M6 ladder + scope). Build ~6–8 files, ~2–3 wk, serial Lean-writers.

PLAN (bottom-up, serial Lean):
- PRE: pin PEEL local transfer identity symbolically (q-Vandermonde × N=1 Durfee) — pen-and-paper, parallel.
- M1 Core.QSeries primitives (P/Pm/Pmult/Qseries + Pm coeffs≥0, const-term 1) — FIRST tide (critical path).
- M2 classical q-facts (q-binomial inverse/S3, q-Vandermonde, N=1 Durfee).
- M3 PEEL/Thm 5.6 (bulk; needs the transfer pin).
- M4 S1–S4 chain → Thm 5.5 (S1 reuses LANDED codimForm_update_corner).
- M5 L1 extraction (clean). M6 cCodim/numTop symmetry → Cor 5.10 (all r via rankShift) + geometric transfer.
- order-reversal fragment (independent, ~1 file) — slot in when convenient.

NOW: dispatch (a) transfer-pin pen-and-paper [parallel, no Lean], (b) M1 primitives formaliser [serial Lean].

## 2026-06-22 — M3 DE-RISKED: transfer PINNED (thread 04), M2 SHRINKS
pin-transfer pinned the PEEL local transfer identity (findings homed to threads/04; scratch committed 6eb7705).
KEY CORRECTION: transfer = N nested applications of the SINGLE N=1 Durfee identity (D) + an arithmetic
exponent-split (E) — NOT q-Vandermonde×Durfee (corrects thread-03 §4). Recommended Lean target = staged
single-induction on m (one invariant), one Durfee per step. Subtle step = terminal staged↔flat reindexing
(de-risked: x_j≤s_j is free given ∑x=d). Exact-verified (28 (b;d) incl wide/non-monotone, 0 mismatch).
IMPACT: M3 (PEEL) needs ONLY (D) Durfee as classical input. M2 re-scoped: (D) Durfee [M3] + the S3
q-binomial inverse [M4, possibly AVOIDABLE by own induction]; q-Vandermonde likely NOT needed at all.
GIT NOTE: findings.md + this flush written to disk; commit DEFERRED to the post-M1 coordinated pass
(fm-qseries-m1 is mid-tide in the shared worktree — avoid racing its build/commit).

## 2026-06-22 — M1 LANDED + a worktree-homing INCIDENT (resolved) + operating-mode shift
- **M1 LANDED:** Core.QSeries primitives green/axiom-clean ([propext,Classical.choice,Quot.sound] verified
  by me), fidelity-PASS, card SHA-pinned 9d5002c. Commit 9d5002c (+ d3da019 SHA pin). The q-series foundation.
- **INCIDENT:** the M1 formaliser (background subagent) launched with cwd = the repo MAIN checkout (a DIFFERENT
  live session, expedition/aoyagi-full), NOT my voigt-discharge worktree. Its relative Write/Edit wrote
  QSeries.lean + an aggregator import + a stray expedition dir into the AOYAGI tree; it built the aoyagi
  aggregate (3704 jobs ≠ my 3681). RESOLVED: rescued the content, re-verified green/axiom-clean on MY branch,
  surgically restored the aoyagi tree (reverted exactly my +2 aggregator lines after re-checking the diff;
  removed my stray files). Aoyagi's own work untouched; nothing leaked to their commits.
- **ROOT CAUSE:** harness launches subagents at the repo's primary (main) worktree regardless of my cwd;
  relative tool-writes go there. EnterWorktree is a no-op (I'm already cwd-rooted in voigt-discharge).
- **OPERATING MODE (decided):** the controller writes the q-series Lean tides HIMSELF in voigt-discharge with
  ABSOLUTE paths (provably safe). Pen-and-paper seats remain (they write via bash `cd`, unaffected) for
  decorrelated MATH + strategy scoping; Codex for decorrelation. Trades formaliser-fleet parallelism for zero
  risk to the live aoyagi session. Slower/serial but safe. (Operator offered the alternative of guarded
  formaliser worktrees if speed is wanted.)
- **NEXT:** M2 = N=1 Durfee identity. scope-durfee (pen-and-paper, thread 06) scoping the Lean route +
  Mathlib support first; then I write the Lean.

## 2026-06-22 — EXECUTION MODE: guarded formaliser worktrees (operator-approved)
Delegation verdict: isolated subagents = filesystem-safe but BROKEN checkout (iso-probe at bd11537 lacked
the committed M1 — unreliable); non-isolated = pollute the aoyagi tree. So neither default works. Operator
chose GUARDED formaliser worktrees:
- I pre-create a dedicated build worktree `.claude/worktrees/perm-build` on branch `pi-build` off
  perm-invariance HEAD (VERIFIED M1 + M2-partial present — unlike the broken isolation checkout).
- Formalisers use ONLY ABSOLUTE paths under perm-build for all Read/Write/Edit; build via `cd perm-build/lean`;
  commit to `pi-build`; SELF-CHECK `git -C <main> status` clean (no leak to aoyagi) before reporting.
- I MERGE pi-build → perm-invariance in voigt-discharge + green-gate; I POST-VERIFY the aoyagi tree clean
  after each tide. A relative-path slip → transient aoyagi stray file (detected + surgically cleaned).
- M1 (9d5002c) + M2-partial (032ea0d) banked. M2 to be COMPLETED by the first guarded formaliser:
  B_term, A_sum_desc, B_sum_desc (the reindex), rhs_desc, the durfee induction (domain-cancel 1-X^{b+1}).

## 2026-06-22 — M2 LANDED (the Durfee identity), inline + contention-free
`Core.QSeriesDurfee.durfee : P a * P b = ∑_{r=0}^{min a b} X^{(a-r)(b-r)} P(a-r) P r P(b-r)` over ℤ⟦X⟧ —
green, 0-sorry, axiom-clean ([propext,Classical.choice,Quot.sound]). Commit 9d408a3 (card pinned ca8ab05).
Route B (induction on b; unit-cancellation of 1-X^{b+1} via PowerSeries.isUnit_iff_constantCoeff). The hard
B_sum_desc reindex (Finset.sum_range_succ' peel-and-shift) landed first try — the thread-06 certificate held.
EXECUTION: written INLINE in voigt-discharge (warm .lake) — zero new-worktree Mathlib recompile, zero
contention with aoyagi, zero aoyagi-pollution. (The guarded-worktree approach was abandoned: fresh worktrees
recompile Mathlib unless cache-get, which contends with the live aoyagi sessions; inline is contention-free.)
v4.29 gotchas banked in the M2 card: linear_combination + PowerSeries.Inverse need explicit imports;
ℤ⟦X⟧ no auto IsLeftCancelMulZero (cancel via unit); le_or_lt absent (use by_cases).
NEXT: M3 = PEEL / Thm 5.6 (the bulk) — uses the LANDED durfee (M2) as its only classical input (thread 04 pin).

## 2026-06-22 — M3b CRUX CRACKED (peelPart_cover_sum + peelPart_mem), inline zero-cited
The hardest M3b step — the kostantAt-merge cover-reindex (spec thread-07's "most likely to break") — is
LANDED green/no-sorry inline: `peelPart_cover_sum` (two Finset.sum_bij reindexes via the additive
`peelPart_eq`: castSucc non-last + last-column correction), and `peelPart_mem` (peel maps kostantAll d into
kostantAll d', kostantAt transferring by the cover-reindex). Foundation done: peelPart + peelPart_last/_castSucc
/_eq/_support/_cover_sum/_mem all green. Operator chose GRIND ON (full zero-cited, vote of confidence).
EXECUTION: inline only (fresh worktrees re-clone all of mathlib = too heavy; confirmed + aborted perm-m3b).
REMAINING M3b: the per-fibre weight collapse (codimForm split + Pm split + inner-sum = transferRHS_eq) +
the fiberwise sum + induction on N → fivegon (Thm 5.6). Then M4 (chain → Thm 5.5) + M6 (Cor 5.10 via the M5
bridge + M6-prep). All Lean targets = the exact-verified pen-and-paper certificates (thread 03/04/07).
Landed this session: M2, M3a, M5/L1+bridge, M6-prep, M3b-foundation+crux.

## 2026-06-22 — M3b codimForm-split: GRANULAR STATE (for compaction-recovery)
codimForm-split route (thread-08 cert 665f3d9, A/R/L decomposition via LANDED codimBil/codimForm_add/
codimForm_congr_onbox). TARGET: codimForm(N+1)(extendℤ m) = codimForm N (extendℤ(peelPart m)) + Δ,
Δ = ∑_{0≤a<u≤N+1} (extendℤ m) a N · (extendℤ m) u (N+1).
LANDED in QSeriesFivegon.lean (all green, committed ≤61d9228 + later):
  - extendℤ_add (extendℤ additive); peelLower/peelCorr defs; peelPart_eq_add (peelPart m = peelLower m + peelCorr m);
  - extendℤ_peelCorr_off (peelCorr-extendℤ zero off col N); codimBil_peelCorr_left (codimBil N (extendℤ peelCorr) A = 0 — peel-side Step C).
REMAINING codimForm-split:
  - peel side: codimForm N (extendℤ(peelPart m)) = codimForm N A + codimBil N A R  [rw peelPart_eq_add, extendℤ_add, codimForm_add; codimBil N R A=0 via codimBil_peelCorr_left; codimForm N R = codimBil N R R=0 same]. A=extendℤ(peelLower m), R=extendℤ(peelCorr m).
  - big side: def peelLast (Fin(N+2)², col N+1) + L=extendℤ peelLast; codimForm(N+1)(extendℤ m)=codimForm(N+1)(A+L) via codimForm_congr_onbox (THE flagged risk: the on-box Fin-index/castSucc identity extendℤ m = extendℤ(peelLower m)+L on box-(N+1)); then codimForm_add; L vanishing (analogue of codimBil_peelCorr_left at level N+1); Step D codimForm(N+1) A = codimForm N A (A bound N; v=N+1 terms vanish — ℤ-Icc top-peel via insert/sum_subset).
  - Step E: Δ = codimBil(N+1) A L − codimBil N A R = the j=N+1 slice = explicit ∑_{a<u} m_{a,N}m_{u,N+1}.

## 2026-06-22 — codimForm SPLIT LANDED (commit a340e01), codimForm-split DONE except Step E
`codimForm_split` PROVED sorry-free + axiom-clean [propext, Classical.choice, Quot.sound] in
QSeriesFivegon.lean: `codimForm (N+1) (extendℤ m) = codimForm N (extendℤ (peelPart m)) + (codimBil
(N+1) A L − codimBil N A R)`, A=extendℤ(peelLower m), R=extendℤ(peelCorr m), L=extendℤ(peelLast m).
Landed lemmas (all green): codimForm_peel_lhs (peel side), codimForm_peel_rhs (Step A big side, the
flagged on-box castSucc/Fin.last identity — done via codimForm_congr_onbox + split_ifs/congr), 
extendℤ_peelLower_col, extendℤ_peelLast_off, codimBil_peelLast_left (Step C), sum_Icc_peel_top
(private ℤ-Icc top-drop helper), codimForm_peelLower_level (Step D, inside-out 4-fold sum-peel calc),
codimForm_big (big-side assembly). peelLast def + peelPart_mem + fivegonSum_fiberwise also landed.
QSeriesFivegon NOT yet in DLNFibre.lean aggregator (WIP — add when fivegon proven).

REMAINING for fivegon (Thm 5.6):
  - Step E (explicit Δ): DONE (commit c35d2f3). codimForm_split_explicit: codimForm(N+1)(extendℤ m)
    = codimForm N(extendℤ(peelPart m)) + ∑_{i∈Icc 1(↑N+1)}∑_{u∈Icc i(↑N+1)} extendℤ m (i-1)↑N · extendℤ m u(↑N+1)
    [i-form, a=i-1]. delta_nonneg (Δ≥0). Helpers: extendℤ_peelLast_at/_peelLower_at/_peelCorr_at (col evals),
    codimBil_peelCorr_collapse/_peelLast_collapse (v-sum picks live col), codimBil_diff_eq_delta (peel+drop), sum_Icc_peel_top.
  - THE BIJECTION (thread-07 piece 1): DONE (commit 0ce9200). fibre_sum_reindex: ∑_{m∈(kostantAll d).filter(peelPart·=m')} F m
    = ∑_{x∈admissibleXs m' (d last)} F(rebuild m' x), via Finset.sum_bij' (lastCol ⇄ rebuild). Axiom-clean.
    Landed: lastCol/rebuild/boundX/admissibleXs (defs); lastCol_rebuild + rebuild_lastCol (inverses) +
    peelPart_rebuild (peel recovers m'); lastCol_mem_admissibleXs (fwd maps_to) + rebuild_mem_kostantAll
    (bwd maps_to, THE crux — old-vertex kostant via peelPart_rebuild+peelPart_cover_sum, new via ∑x=d_last).
  - codimForm_rebuild [LANDED, commit after 0ce9200]: codimForm(N+1)(extendℤ(rebuild m' x)) = codimForm N(extendℤ m')
    + Δ(rebuild m' x). Pmult_succ [LANDED]: Pmult d = Pmult(d∘castSucc)·P(d last).

## 2026-06-22 — PIECE 3+4 fully SCOPED (next focused grind, ~150 lines). Bijection (piece 1) DONE.
Per-fibre collapse target: ∑_{m∈(kostantAll d).filter(peelPart·=m')} X^{codimForm(N+1)(extendℤ m).toNat}·Pm(N+1)m
  = X^{codimForm N(extendℤ m').toNat}·Pm N m'·P(d last). Steps:
  S1. fibre_sum_reindex [LANDED] with F m = X^{codimForm(N+1)(extendℤ m).toNat}·Pm(N+1)m → ∑_{x∈admissibleXs m'(d last)} F(rebuild m' x).
  S2. per x: codimForm_rebuild [LANDED] → exponent = codimForm N(extendℤ m') + Δ(rebuild). toNat split:
      X^{(A+Δ).toNat} = X^{A.toNat}·X^{Δ.toNat} via Nat-add-of-toNat (codimForm_extendℤ_nonneg [QSeriesExtraction] + delta_nonneg [LANDED]).
  S3. Pm FACTORIZATIONS (Finset.prod splits of upperPairs by column j; define lowerPm m' = ∏_{p∈upperPairs N, p.2≠last N} P(m' p)):
      (a) Pm N m' = (∏_{I':Fin(N+1)} P(m'(I',last N)))·lowerPm m'  [split upperPairs N by p.2 = last N; all I'≤last N].
      (b) Pm(N+1)(rebuild m' x) = (∏_{I:Fin(N+2)} P(x I))·(∏_{I':Fin(N+1)} P(m'(I',last N) − x I'.castSucc))·lowerPm m'
          [split upperPairs(N+1) 3-way: col N+1 (=x), col N (=b−x), col ≤N-1 (=m' lower); rebuild evals via Fin.lastCases].
  S4. Δ(rebuild m' x) eval → ∑_{a<u}(b_a−x_a)x_u form (b_a=m'(⟨a⟩,last N), x via extendℤ(rebuild) entry evals: col N+1 = x ⟨u⟩, col N = b−x). Then inner sum
      ∑_{x∈admissibleXs} X^{Δ.toNat}·(∏P(b−x)·∏P(x)) = transferRHS b (d last) [b=List.ofFn(fun i=>m'(i,last N))], via induction MIRRORING
      transferRHS recursion (peel x_0; Δ per-step split Δ=(b_0−x_0)(d−x_0)+Δ', pure ring). transferRHS_eq [LANDED]: = P(d last)·(b.map P).prod.
      (b.map P).prod = ∏_{i} P(m'(i,last N)) [List.prod_ofFn / List bridge — thread-07 secondary risk]. lowerPm cancels: collapse = P(d last)·Pm N m'.
  S5. induction on N (peel Fin.last): base N=0 (single interval, codimForm 0=0, Pm 0 = P(d 0)); step uses fivegonSum_fiberwise [LANDED] +
      per-fibre collapse + IH + Pmult_succ → fivegonSum d = Pmult d (= the 5gon, corner-free single sum). Then aggregate QSeriesFivegon into DLNFibre.lean.
  THEN M4 (S1-S4 chain → Thm 5.5) + M6 (Cor 5.10 via cCodim_eq_of_Qseries_eq/numTop_eq_of_Qseries_eq [M5, LANDED] + Pmult_sub_comp_perm [M6-prep, LANDED]).

## 2026-06-22 (cont.) — S2 + S3 + S4-entry-evals LANDED. Per-fibre collapse: assembly + inner-sum induction REMAIN.
LANDED this run (all green, axiom-clean, committed): prod_lastCol, lowerPm, Pm_eq_colN_mul_lower (S3a),
rebuild_castSucc, prod_lower_reindex, rebuild_last, Pm_rebuild_factor (S3b: Pm(N+1)(rebuild)=(∏P x)·(∏P(b−x))·lowerPm),
X_pow_toNat_add (S2: X^{(A+Δ).toNat}=X^{A.toNat}·X^{Δ.toNat}, A,Δ≥0), extendℤ_rebuild_colN (=↑(b−x)), extendℤ_rebuild_colNp1 (=↑x).
[convert handles Fin.mk proof-irrel — Lean4 defeq.]
REMAINING per-fibre collapse (two pieces):
  (P) ASSEMBLY (perfibre_reduces, ~40 lines): fibre_sum_reindex [LANDED] + per-x: F(rebuild x) = X^{codimForm(N+1)(extendℤ rebuild).toNat}·Pm(N+1)(rebuild)
      = [codimForm_rebuild + X_pow_toNat_add (Δ≥0 by delta_nonneg(rebuild), c(m')≥0 by codimForm_extendℤ_nonneg)] X^{c(m').toNat}·X^{Δ.toNat}·Pm(N+1)(rebuild)
      = [Pm_rebuild_factor] X^{c(m').toNat}·X^{Δ.toNat}·(∏P x)·(∏P(b−x))·lowerPm; factor out X^{c(m').toNat}·lowerPm (Finset.mul_sum) →
      = X^{c(m').toNat}·lowerPm·innerSum, innerSum := ∑_{x∈admissibleXs} X^{Δ(rebuild x).toNat}·(∏_I P(x I))·(∏_{I'} P(b_{I'}−x_{I'.castSucc})).
  (P) DONE [commit after edbfac8]: perfibre_reduces — ∑_{fibre} X^{codim(N+1)(extendℤ m).toNat}·Pm(N+1)m = X^{codim N(extendℤ m').toNat}·lowerPm m'·innerSum m' d_last.
      innerSum m' dlast := ∑_{x∈admissibleXs m' dlast} X^{Δ(rebuild x).toNat}·(∏_I P(x I))·(∏_{I'} P(m'(I',last N)−x I'.castSucc)) [DEF landed].
  (Q) innerSum m' dlast = transferRHS (List.ofFn (fun i=>m'(i,last N))) dlast [THE hard induction, ~100 lines, ONLY remaining per-fibre gap].
      TOOLS: Mathlib `Finset.piAntidiag (s) (n)` = {f:ι→μ | supp⊆s, ∑_s f = n} with `piAntidiag_cons (hi:i∉s) (n)` recursion (Mathlib/Algebra/Order/Antidiag/Pi.lean).
      ROUTE: (a) Δ(rebuild x).toNat = natΔ via colN/colNp1 evals INSIDE a sum_congr (Fin proofs need the Icc range hyps — fold into the proof, not standalone); natΔ = ∑_{a<u}(b_a−x_a)x_u.
      (b) bridge admissibleXs (piFinset(range(boundX+1)).filter(∑=d)) ↔ peelable form; induct on N (generalize m',dlast), peel x_0 via piAntidiag_cons (bound x_0≤b_0 from boundX,
      x_0≤d from residual → range = min b_0 d, matching transferRHS); Δ per-step split Δ=(b_0−x_0)(d−x_0)+Δ' (pure ring, thread-04); durfee per step → IH.
      transferRHS_eq [LANDED] = P(d_last)·(b.map P).prod; listOfFn_col_prod [LANDED] → ∏P(b); lowerPm·∏P(b)=Pm N m' [S3a, Pm_eq_colN_mul_lower].
  Final per-fibre (P)+(Q)+S3a: X^{c(m').toNat}·lowerPm·transferRHS = X^{c(m').toNat}·lowerPm·P(d_last)·∏P(b) = X^{c(m').toNat}·P(d_last)·Pm N m'.
SESSION 2026-06-22 banked (all green, axiom-clean, pushed, ~26 lemmas): codimForm split (a340e01), Step E/explicit Δ (c35d2f3),
the ENTIRE last-column bijection (0ce9200 — flagged crux), codimForm_rebuild, Pmult_succ, listOfFn_col_prod, S3a, S3b, S2, S4 entry evals.
ALL of fivegon's content EXCEPT the inner-sum induction (Q) + outer induction (S5). Then M4 (Thm 5.5), M6 (Cor 5.10).
Operator: GRIND ON, full zero-cited, structure survives compaction. Inline only (worktrees too heavy — subagents launch at PRIMARY checkout, fresh worktrees re-clone mathlib).

## 2026-06-22 — HEADLINE LANDED: Cor 5.10 (combinatorial) DONE to bedrock; expedition central question ANSWERED
Zero-cited combinatorial permutation-invariance of (C,θ). LANDED + reviewer-SOUND + axiom-clean [propext, Classical.choice, Quot.sound], full library green (3693 jobs):
- `thm55` (QSeriesThm55) = Thm 5.5 (paper eq:Fd_formula): `Qseries d r = P r · ∑_{s∈range(minDim d−r+1)} altP s · Pmult(dminus d (r+s))`, `altP s=(−1)^s X^{C(s,2)} P s`. Built S1' (Qseries_corner_shift, QSeriesShift) + S2 (Pmult_eq_sum_corner) + range-gap + S3 (thm55_zero, sum_triangle_reindex) + ORTH (orth, QSeriesOrth — single-var induction on LANDED P_mul_one_sub_succ, NO q-binomial library).
- `cCodim_comp_perm`/`numTop_comp_perm` (CThetaPermInvariance) = Cor 5.10. Via Qseries_comp_perm (thm55 + LANDED Pmult_sub_comp_perm) → LANDED M5 bridge cCodim_eq_of_Qseries_eq/numTop_eq_of_Qseries_eq.
Reviewer (independent numeric to order 16 + decorrelated Codex): Thm 5.5 ↔ paper verbatim (Example 5.9 codim 3/7, θ=2 matched); Cor 5.10 NON-VACUOUS (e.g. (2,3,2)→(C,θ)=(4,2) const across all perms while TOTAL #components differs 2 vs 3), full intended domain (r≤min d, both Kostant sets nonempty — forced by cCodim/numTop's def, not over-restrictive); proof uses NO Kostant-set bijection (paper warns none exists) — invariance purely from the symmetric closed form. Named honestly: combinatorial cCodim/numTop, NOT rlct (rlct=½codim stays Cited Aoyagi).
PROCESS: built as a proper expedition (controller delegating tides, NOT solo) — formaliser (fivegon M3b tide, then M4→M6 tide), penpaper-s3 (S3 de-risk cert — no q-library needed), reviewer (fivegon SOUND + Thm5.5/Cor5.10 SOUND). Worktree note: controller-in-worktree ⟹ teammate isolation collapses to shared worktree (serial, no mathlib re-clone) — the earlier "inline only" was an over-cautious misjudgment.
REMAINING (post-headline): (a) GEOMETRIC TRANSFER — ~2-lemma capstone: geomCodim_comp_perm + ncard_topComponents_comp_perm, composing LANDED cCodim_eq_inf_geomCodim (CThetaGeometric) + numTop_eq_ncard_topComponents (CCodimZeroStrict, unconditional) with the comp_perm → the variety's actual (C,θ) perm-invariant. (b) order-reversal fragment (#5, zero-cited bedrock). Then close-out.
