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
