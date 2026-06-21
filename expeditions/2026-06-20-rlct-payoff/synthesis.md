# synthesis.md — `rlct-payoff` (controller's internal integrative ground)

Recovery substrate (recover from `brief.md + priorities.md + threads.md + synthesis.md`). Flushed every
tick. In-repo only; never `~/.claude` global memory.

## The quest (one line)
Formalise the RLCT payoff `rlct = (C/2, θ)` ("DLNs are mildly singular") via the geometry of `Σ^r` —
the rank-`r` product locus — with `C` (codim) LANDED and `θ` (= #top-dim components) to build.

## State (2026-06-20 — SETUP)
- Branch `expedition/rlct-payoff` off `dev` (= voigt-discharge merged, PR #4 / merge `859f80c`). Green
  baseline 3012 jobs, 0-sorry, axiom-clean (tree identical to the merged voigt head; `.lake` valid).
- Controller in the (legacy-named) `voigt-discharge` worktree ⟹ teammate isolation collapses ⟹ serial
  Lean-writers, parallel doc/recon seats.
- **No build yet** — sizing recon FIRST (P0).

## Dependency DAG (provisional, re-scoped by the recon)
```
LANDED (dev): Voigt codim C (per-orbit codimRep=orbitLinearCodim) · CTheta combinatorial (C,θ) ·
              CThetaGeometric (cCodim=inf geom codim) · OrbitClosure (Ō_M irred/prime, Thm 3.8) · dim theory
                                   │
  G1 Σ^r-as-variety ──► G2 Σ^r=⋃Ō_M ──► G3 components=maximal Ō_M ──► θ1 top-dim=min-codim ──► θ2 numTop=θ
                                   │                                          (consumes Voigt codim)
  D1 Rep_d/mult/fibres ──► D2 square-Frobenius loss ──► D3 loss-geom = Σ^r ──┐
                                                                              ├──► R2 rlct=(C/2,θ)
  R1 rlct definition / interface  (SLT machinery — FEASIBILITY UNKNOWN) ──────┘     (≤½codim Cited)
```

## Hard pieces / suspicions (to confirm via recon)
1. **G2 `Σ^r = ⋃ Ō_M`** — the structural stratification (corner-rank ≤ r ⟺ union of orbit closures over
   the Kostant partitions with corner ≤ r). The genuinely-hard new geometry.
2. **G3 components = maximal `Ō_M`** — hinges on Mathlib's `irreducibleComponents` API actually covering
   "components of a finite union of irreducible closeds = the maximal ones".
3. **R1 rlct definition** — does Mathlib have ANY real-log-canonical-threshold / SLT scaffolding? If not,
   Phase R is either a from-scratch analytic sub-library (SCOPE-SURPRISE → surface) or a Cited/interfaced
   rlct object (the `≤½codim` bound is already Cited). The recon must answer this decisively.

## Carried meta-lessons (from voigt-discharge — see lessons.md)
- SIZE hard pieces before building (repeatedly saved sub-libraries: L4a, L5, the Σ^r-route).
- Serial Lean-writers (controller-in-worktree); file-scoped `git add` + `git pull --rebase` before push.
- A stuck step deferred twice → fresh decisive tide + a decorrelated Codex consult on the EXACT step
  (the `hA` matrix-Kähler unblock).
- Controller stays executive: delegate object-level to seats; green-gate + AUDIT + hardener every gate;
  flush synthesis every tick.

## Next action
Dispatch the sizing recon (thread 01 scout Mathlib-coverage ∥ thread 02 pen-and-paper math-sizing) →
re-scope the ladder → surface only if a scope-surprise (Phase R sub-library) fires.

## 2026-06-20 — SIZING RECON CLOSED (threads 01+02, Codex-convergent) → re-scoped

**Phases G/θ/D BOUNDED (build, zero-cited, ~5–6 modules); Phase R = Cited interface.**
- G1 mostly LANDED (`Core.Setup`: `productRankLocus`/`productRankLocusLE`=`Σ̄^r`={rk≤r}/`mult`/`fibre`).
  Link lemma `mult = submult` corner (~10 LoC).
- G2 `Σ̄^r = ⋃_{corner≤r} Ō_M` — the hard structural piece (~300–500 LoC); both inclusions from LANDED
  Gabriel + `orbitRankLocus`. Gating piece (pen-and-paper): the set-level membership `A ∈ Ō_{rankPattern A}`.
- G3 components = maximal `Ō_M` — Mathlib `irreducibleComponents` / `Ideal.minimalPrimes.equivIrreducibleComponents`
  / `mem_of_subset_sUnion_irreducibleComponents`; `height = ⨅ minimalPrimes` by `rfl`. (~250–400 LoC.)
- θ: `numTop = θ` via min-codim ⟹ component (consumes LANDED Voigt/CThetaGeometric). Needs strict-mono of
  `codimRep`/`Ideal.height` under proper irreducible inclusion (check `Core.AffineDomainDimension`).
- D: D1 LANDED; D2 loss ~100–200; D3 codim identity ~200–400 (scope to codim, avoid k=ℂ bundle).
- **R: Mathlib has ZERO rlct/SLT/lct/zeta/Watanabe. INTERFACE `rlct = C/2` against a `Cited` `RlctInterface`
  (~50–150 LoC). NOT a from-scratch build (multi-month).**

**TWO CORRECTIONS (recon, vs source — Codex-convergent):**
1. **`θ` ≠ rlct multiplicity** (paper line 1934: no simple relation between rlcm `m²{S̃/m}(1−{S̃/m})` and θ=k).
   DROPPED the "(C/2,θ) = complete learning coefficient" framing. θ = geometric invariant; payoff = `rlct=C/2`
   (Cited) + θ (geometric), two results. Brief re-scoped.
2. `Σ̄^r = {rk ≤ r}` (engine's `productRankLocusLE`; paper's `≥` at line 758 is a typo).

**Architecture risk (flagged both seats):** the point↔`PrimeSpectrum` transport of `codimRep`=`Ideal.height`
under the coordinate change — the voigt-flagged no-Mathlib-lemma. Spike it FIRST in the G build.

**(2,2,2) r=0 (exact, cross-checked):** 6 corner-0 orbits, codimForm {4,3,5,4,5,8}; **3 irreducible
components** (codim 4,3,4); **C=3, θ=1** — matches `cCodim_d222_zero=3` / `numTop_d222_zero=1` + paper Ex 4.3.
((2,3,2): C=4, θ=2.)

**Next:** dispatch Phase G build (thread 03): G1 link + set-level Gabriel membership + G2 stratification,
starting with the spec-transport/`minimalPrimes(⨅)` spike. Then G3 + θ, then D, then R-interface.
Surface to operator only at completion or a genuine blocker; the Phase-R Cited-interface framing (given the
θ-correction) is the natural mid-point to re-confirm with the operator.

## 2026-06-20 — G2 LANDED (the Σ̄^r stratification — structural foundation)
`Core.SigmaStratification.productRankLocusLE_eq_iUnion_orbitRankLocus`: `Σ̄^r = ⋃_{(mult M).rank ≤ r} orbitRankLocus M`.
Green (3013 jobs), 0-sorry, axiom-clean, `[Field k]` only, reviewer PASS. Bricks for G3: `corner_rankPattern_eq_rank`
(G1), `exists_orbitRankLocus_mem_rankPattern_eq` (Gabriel membership), `orbitRankLocus_eq_of_rankPattern_eq`
(rank-pattern collapse → the finite distinct orbit-closure family). Commits c0cae1a/517d8e8/63c3568.
**Next: G3** (thread 04) — irreducible components of `Σ̄^r` = maximal `Ō_M` (Mathlib `irreducibleComponents` +
`mem_of_subset_sUnion_irreducibleComponents`, consuming G2's union + collapse), then top-dim = min-codim ⟹
`θ = numTop` (consumes LANDED Voigt codim). START with the spec-transport/`minimalPrimes(⨅)` spike (flagged risk).

## 2026-06-21 — G3 LANDED (components = maximal Ō_M); θ-A landed; θ-count remaining
`Core.SigmaComponents`: irreducible components of `Σ̄^r` = maximal `Ō_M` (`minimalPrimes_sigmaIdeal_eq`,
`irreducibleComponents_sigmaIdeal_equiv`); spike `minimalPrimes_sInf_of_finite_of_isPrime` (general, prime
avoidance) — architecture CLEAN (PrimeSpectrum/⨅ route, no point-space union algebra). θ-A
`orbitRankLocus_minCodim_mem_minimalPrimes` (top-dim ⟹ component, strict-mono height). Green (3014 jobs),
0-sorry, axiom-clean, reviewer PASS-with-notes. Commits 99eafe0/d59862e. Closes CThetaGeometric roadmap step (ii).
- **θ-count remaining** (thread 05, ~150–250 LoC, scoped by G3): `numTop = θ = #top-dim components` — the
  Kostant-partition ↔ component count-bijection (surjectivity via Kostant reps + injectivity + min-height↔
  min-codimForm restricted to minimisers; the height=codimForm transport is LANDED). Then Phase D, then R-interface.
- **ENV FLAG: Codex non-functional in this worktree** (codex doctor/exec timeout, exit 143/144). Decorrelated-
  Codex discipline degraded → use the reviewer for decorrelation until Codex returns. Flagged to operator.

## 2026-06-21 — θ-count PARTIAL (bijection + injectivity landed; count gated on 2 bricks)
`Core.ThetaComponentCount`: `numTop_eq_ncard_topComponents_of` (count headline, GATED) +
`bijOn_partitionIdeal_topComponents_of` (the bijection, gated) + `partition_eq_of_rankPattern_realizerD_eq`
(injectivity, UNCONDITIONAL) + the realizer-over-d infra. Green (3015 jobs), 0-sorry, axiom-clean,
reviewer PASS-with-notes. Commits e782f76/b913ecf. (2,2,2)r=0 → 1 top component; (2,3,2)/r=1 → 2 (pen-and-paper).
- **θ-count GATING (2 bricks, ~120–180 LoC, pen-and-paper (★)-certified — the next build):**
  (i) corner-monotonicity of `cCodim` (constructive interval-merge ⟹ top-dim component sits at corner exactly r);
  (ii) Gabriel→`kostantPartition` recovery in the `extendℤ` encoding. Discharge these ⟹ θ=numTop UNCONDITIONAL.
- Then Phase D (DLN loss + codim identity), then Phase R (Cited rlct interface).

## STATUS SNAPSHOT (for re-ground)
Phase G COMPLETE: G2 stratification ✓, G3 components=maximal Ō_M ✓, θ-A top-dim⟹component ✓.
θ-count: bijection+injectivity ✓, count gated on 2 bricks. Remaining: θ-bricks → D → R(Cited).
ENV: Codex down env-wide (decorrelate via reviewer). [IsAlgClosed k][CharZero k] on the geometric headlines.

## 2026-06-21 — θ-count reduced to ONE inequality (Brick 2 landed; Brick 1 → cCodim·0 mono)
`Core.CCodimCornerMono`: **Brick 2 LANDED** (`gabrielPartition`, `orbitRankLocus_realizerD_gabrielPartition`
— Gabriel→Kostant recovery, unconditional). **Brick 1 REDUCED**: `numTop_eq_ncard_topComponents_of_dimMono`
proves `θ=numTop` GIVEN `hMono`/`hMonoStrict` = dimension-monotonicity of `cCodim·0` (`cCodim e 0 ≤/< cCodim
e' 0` for `e ≤/< e'`). Both old geometric hyps discharge from this one CTheta inequality (via rank-shift
`cCodim d t = cCodim (d−t) 0`). Green (3016 jobs), 0-sorry, axiom-clean, reviewer PASS. Commits 3b8110c..2120900.
- **REMAINING (thread 07, ~120–160 LoC): `cCodim_zero_mono`/`_strict`** via the SHORTEST-interval split at an
  over-covered vertex (verified 199/199 never raises codimForm; merge-up route DEAD; strict single-vertex FALSE,
  strict ALL-vertex holds). `codimForm` = type-A Ext-pairing form `∑_{a<c≤b+1, b<e} m̄[a,b]m̄[c,e]`; split delta =
  ∑ coeff(B)m̄(B), positive-coeff B = shorter intervals covering k (absent when I shortest ⟹ delta≤0). Discharge
  ⟹ θ=numTop UNCONDITIONAL. Then Phase D, then R-interface.
- Correction: (2,3,2) θ=2 is at r=0 (not r=1; r=1 → numTop=1). ENV: Codex still flaky for formaliser/me.

## 2026-06-21 — θ-count WEAK mono LANDED (thread 07); strict = last θ gap
`Core.CCodimZeroMono.cCodim_zero_mono` (`e ≤ e' ⟹ cCodim e 0 ≤ cCodim e' 0`) FULL, sorry-free, axiom-clean
(~1569 LoC; crux delta-sign `codimForm_splitMove`/`splitCoeff_pos_imp` via the LANDED `codimBil` machinery;
four atomic shortest-split moves incl. endpoint cases). Discharges `hMono` ⟹ `hLowerBound` UNCONDITIONAL.
Headline `numTop_eq_ncard_topComponents_of_strict` now needs ONLY `hMonoStrict`. Green (3017 jobs). HEAD 7ee71b3.
- **LAST θ GAP (thread 08): `cCodim_zero_strict`** (all-vertex strict). A single shortest-split can be FLAT
  (splitting [0,N] has no negative term), so strict doesn't localise to one step. Route (teammate-identified,
  certified 200/200): the **+1-step invariant `cCodim e 0 < cCodim (e+1) 0`**, then `e ≤ e+1 ≤ e'` + weak mono ⟹
  all-vertex strict. Discharge ⟹ `numTop = #top-dim components` FULLY UNCONDITIONAL. Then Phase D, then R-interface.
- **IN-FLIGHT (thread-07-spawned, uncertain status):** `reviewer07` (weak-mono AUDIT), `strict-cert` (pen-and-paper
  for the +1-step route). Integrate when they report; else re-dispatch fresh.
- **ENV: Codex STILL broken for build agents** (exit 124 timeout from the worktree, even at 70s) despite operator's
  "fixed" — only the reviewer's codex worked partially. Decorrelation = reviewer + exhaustive enumeration. FLAG to operator.

## STATUS SNAPSHOT (re-ground)
Phase G COMPLETE (G2 stratification, G3 components=maximal Ō_M, θ-A). θ-count: bijection+injectivity+Gabriel
recovery+weak cCodim mono ✓ → ONE strict inequality (`cCodim_zero_strict`, route known) from `θ=numTop`
unconditional. Then D (loss+codim identity), then R (Cited rlct interface). [IsAlgClosed][CharZero] on geom headlines.

## 2026-06-21 — CORRECTION: θ strict step is a HARD OPEN combinatorial problem (not "route known")
Thread-07-spawned decorrelated pen-and-paper (`strict-cert`) RETRACTED its `+1`-step "flat-chain" route:
the sketch is FLAWED (bounds only the all-singletons partition of e', not an arbitrary minimiser). Honest state:
- **WEAK `cCodim_zero_mono`: LANDED** (sorry-free, axiom-clean; reviewer07 AUDIT = PASS-with-notes). Solid.
- **STRICT `cCodim_zero_strict` (`hMonoStrict`): PROOF OPEN, genuinely hard.** Statement TRUE (252/252 exhaustive,
  N≤2 exhaustive + N≤4 sampled) but NO short proof: no closed-form lower bound (product/cut-sum/adjacent-min/
  transversal-chain all fail); single-VERTEX strict is FALSE; the `cCodim≥1` floor does NOT bridge to the `+1`.
- **HONEST LANDING (decorrelated recommendation):** keep `numTop_eq_ncard_topComponents_of_strict` with
  `hMonoStrict` as the SINGLE named explicit hypothesis ("all-vertex strict `+1`, exhaustively certified, proof
  open") — a real strict-improvement over thread-05's two opaque geometric hyps (now: one combinatorial, weak
  half discharged). Full unconditionality needs a DEDICATED effort (new invariant / minimiser strict-step chain),
  NOT a quick patch — roadmap it; do not ship a strict lemma backed by the retracted sketch.
- **Phase D (loss + codim identity) and Phase R (Cited rlct interface) do NOT depend on `hMonoStrict`** — they can
  proceed; the strict gap is isolated to θ's full-unconditionality.
- Orphaned thread-07 seats now idle (delta-cert/strict-cert/reviewer07) — stand down at close.

## 2026-06-21 — Phase D/R DESIGNED (thread 09); r=0 RLCT payoff ~1 module; Codex intermittently back
Design (Codex-convergent, findings in thread 09): **r=0 is load-bearing + nearly free** — `fibre d 0 =
productRankLocusLE d 0 = Σ̄^0` ⟹ `codim(fibre 0) = cCodim d 0 = C` (no bundle shift). Loss `K^DLN_B =
‖mult A − B‖²_F` over ℝ; zero-set = fibre. **Cited boundary (name=content):** a `Cited`-tagged
`RlctInterface` axiomatising ONLY Aoyagi's `rlct(K^DLN_B) = codim(fibre)/2` (stops at codim(fibre)/2 ⟹ R2 is
real transport); payoff `rlct(K^DLN_0) = C/2` carries `I : RlctInterface` in its type + `via_aoyagi` in its
name (no bare `rlct_eq_half_codim`). FIELD: loss over ℝ, geometric C over ℂ (alg-closed) — the interface
bridges real-rlct↔complex-codim (Aoyagi-Cited); the one subtlety to handle cleanly. (2,2,2) r=0: C=3, rlct=3/2.
- **DISPATCHED thread 10:** the r=0 payoff build (D2 loss + D3(r=0) codim=C + R1 interface + R2 rlct=C/2),
  ~200–410 LoC, one `DLNFibre.DLN` module. General-r shift (Lemma 4.6) roadmapped.
- **CODEX update:** intermittently back — the thread-09 pen-and-paper's bounded `codex exec` completed (exit 0);
  only `codex doctor` reliably times out. Decorrelation discipline partly restored.

## 2026-06-21 — ★ DESTINATION DELIVERED ★ rlct(K^DLN_0) = C/2 (thread 10)
`DLNFibre.DLN.RlctPayoff` (green 3676 jobs, 0-sorry, axiom-clean `[propext, Classical.choice, Quot.sound]`,
reviewer FIDELITY OK): `lossDLN` (square-Frobenius, ℝ) · `zeroLocus_lossDLN_eq_fibre` ·
`fibre_zero_eq_productRankLocusLE_zero` · **`codimRepCanonical_fibre_zero_eq_cCodim`** (codim(fibre 0)=C,
zero-cited; bridge (b) Kostant↔orbit-codim-min PROVED IN FULL — better than the design's "Deferred") ·
`RlctInterface` (Cited `cited_aoyagi_dln`, a carried hypothesis NOT a global axiom) · **`rlct_lossDLN_zero_eq_half_cCodim_via_aoyagi`**
(rlct(K^DLN_0)=C/2, name=content: `I : RlctInterface` in the type + `via_aoyagi`). (2,2,2): rlct=3/2. Commits d3650f4/f52430d.

## EXPEDITION DELIVERABLE (close-pending)
1. **Σ^r geometry** (zero-cited): stratification `Σ̄^r = ⋃ Ō_M` + irreducible components = maximal Ō_M
   (`Core.SigmaStratification`/`Core.SigmaComponents`) — closes the CThetaGeometric roadmap.
2. **θ = #top-dimensional components** (`Core.ThetaComponentCount`) — MODULO one named, exhaustively-certified
   open hypothesis `hMonoStrict` (the strict cCodim inequality). Weak half + bijection + Gabriel recovery LANDED.
3. **The destination `rlct(K^DLN_0) = C/2`** (`DLNFibre.DLN.RlctPayoff`) — Cited Aoyagi interface, name=content,
   C the zero-cited geometric codimension. "DLNs are mildly singular," r=0.

## HONEST OPEN (roadmap — operator decision: close-and-roadmap vs dedicated effort)
- **(A) θ-strict `cCodim_zero_strict`:** hard-open combinatorial (statement exhaustively true 252/252; NO short
  proof — no closed-form LB, obvious routes fail; single-vertex strict FALSE). Needs a dedicated effort. θ is
  currently the honest "weak + one named open hypothesis" (a real strict-improvement over thread-05's 2 opaque hyps).
- **(B) general-r rlct:** the Lemma 4.6 bundle shift `codim(fibre B) = C + r(d_0+d_N−r)` — genuinely separate;
  the r=0 (zero-product) case is the load-bearing destination + is delivered.
- rlct DEFINITION is honestly Cited (Aoyagi interface), per project policy — NOT a from-scratch SLT sub-library.

## CLOSE: propose PR `expedition/rlct-payoff → dev` (operator-gated, signal-and-wait). Stand seats down at close.

## 2026-06-21 — operator: PUSH GENERAL-r payoff (before close)
Target: `rlct(K^DLN_B) = (C_r + r(d_0+d_N−r))/2` for general rank-r B, via the bundle shift
`codim(fibre B) = codim(Σ̄^r) + r(d_0+d_N−r)` (= dim of the rank-r determinantal variety; Lemma 4.6).
RISK: the shift's fibre-dim drop may hit the SAME no-Chevalley-fibre-dim wall as voigt-discharge L2b★
(Mathlib lacks fibre-dim) — voigt dodged it via route-c (Jacobian⟹trdeg). SIZING FIRST (thread 11,
pen-and-paper): is there a zero-cited route for the shift, or is Cite-Lemma-4.6-named the honest move
(consistent with the Aoyagi rlct interface)? Then build D3-general + R2-general `rlct=(C+shift)/2`.
(2,2,2)/r=1: codim Σ̄^1=1, shift 3, fibre codim 4, rlct=2.

## 2026-06-21 — general-r sizing (thread 11): bundle shift = fibre-dim WALL ⟹ CITE Lemma 4.6 (Codex-convergent)
The shift `codim(fibre B) = codim(Σ̄^r) + r(d_0+d_N−r)` is NOT zero-cited-provable (same wall as voigt L2b★: for
B≠0 the fibre is not GL-stable / not an orbit closure / not one inner orbit; the bundle dim-formula IS the missing
Chevalley fibre-dim). Honest split:
- **Brick A `codim Σ̄^r = cCodim d r` (general r): PROVE zero-cited** — Σ̄^r GL-stable; landed orbit-closure machinery
  (sigmaIdeal d r, minimal-primes=maximal Ō_M, Voigt, cCodim_rankShift) is general in r; uses WEAK monotonicity only
  ⟹ INDEPENDENT of the open θ-strict gap (`hMonoStrict`).
- **Brick B the shift: CITE Lemma 4.6** (`lem:rank_vs_fibers`, main.tex:844-858) via a named `BundleShiftInterface`
  (separate from the Aoyagi `RlctInterface`). Honest Cited boundary, like Aoyagi.
- **R2-general `rlct(K^DLN_B) = (cCodim d r + r(d_0+d_N−r))/2 via_aoyagi`**: pure transport (the landed
  `cited_aoyagi_dln` is ALREADY general in r) gated on Brick A + Brick B.
Checks: (2,2,2) r=1 → codim Σ̄^1=1, shift 3, fibre codim 4, rlct=2; r=2 → shift 4, codim 4; (2,2,1) r=1 → shift 2,
codim 2 (confirms d_0+d_N form). ~80–150 LoC, 1 DLN module. DISPATCHED thread 12.

## 2026-06-21 — ★ GENERAL-r DESTINATION DELIVERED ★ (thread 12)
`DLNFibre.DLN.RlctPayoffGeneral` (green 3677 jobs, 0-sorry, axiom-clean, reviewer FIDELITY OK):
- **Brick A `codimRepCanonical_productRankLocusLE_eq_cCodim`** (`codim Σ̄^r = cCodim d r`, general r): PROVED
  zero-cited, WEAK-monotonicity-only (independent of the open θ-strict gap) — new general-r geometric content.
- **Brick B `BundleShiftInterface`** (Cited Lemma 4.6, named carried hypothesis).
- **R2-general `rlct_lossDLN_eq_half_cCodim_add_shift_via_aoyagi`**: `rlct(K^DLN_B) = (cCodim d r +
  r(d_0+d_N−r))/2` for general rank-r B, name=content (I,J interfaces explicit, via_aoyagi). (2,2,2) r=1: rlct=2.
Commits 933e424/e39a1a7.

## EXPEDITION DELIVERABLE — FULL DESTINATION (close-pending)
1. **Σ^r geometry** (zero-cited): `Σ̄^r = ⋃ Ō_M` + components = maximal Ō_M.
2. **θ = #top-dim components** — MODULO the one named, exhaustively-certified open `hMonoStrict`.
3. **`rlct(K^DLN_B) = (C_r + r(d_0+d_N−r))/2` for GENERAL rank-r B** ("DLNs are mildly singular") — geometric
   C_r zero-cited; the rlct value Cited (Aoyagi) + the bundle shift Cited (Lemma 4.6), both honest named interfaces.
**Cited boundary (all named, name=content):** Aoyagi rlct value; Lemma 4.6 bundle shift. **Open (roadmap):**
θ-strict `hMonoStrict` (hard-open combinatorial). **CLOSE: propose PR `expedition/rlct-payoff → dev` (operator-gated).**
