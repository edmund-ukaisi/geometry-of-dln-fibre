# Critical-path sorry-map — general-`L` `aoyagi_learning_coefficient`

**Thread:** `genm-critpathmap` (scout, read-only). **Date:** 2026-07-08.
**Mission:** map the COMPLETE remaining-sorry dependency tree for a sorry-free general-`L,M`
`aoyagi_learning_coefficient`, and decide whether closing `hstep2` is *sufficient* for D1 #120.

Method: standalone `sorry` tokens (ground truth) + the `deepest_point_reduction` /
`product_reduction` proof terms + the import graph. No build run; every leaf named below is a live
`sorry` in a proof term (not a stale comment). All paths are relative to
`lean/DLNFibre/DLN/RLCT/`.

---

## Decisive verdict

**Closing `hstep2` is NOT sufficient for D1 #120.** `hstep2` closes only the D1 "=" side
(`Skeleton:1131`). The D1 "≤" side (`Skeleton:1177`) is a **separate wall** needing an unbuilt
general-`L` IFT-chart-at-`v` producer (`hchart` + `hCore`), which exists only at `L = 2`.

Within `deepest_gauge_construction`'s `L ≥ 3` branch, `hstep2` **is** the only open obligation
(the other `sorry`s that branch used to carry are discharged — see §Q1).

---

## The tree (what a sorry-free general-`L` headline needs)

```
aoyagi_learning_coefficient (Skeleton.lean:1725)  = deepest_point_reduction ▸ product_reduction
│                                                   (does NOT reference aoyagiTheta_eq)
├─ product_reduction (Skeleton:1142)
│   └─ deepest_regular_core_normal_form (Skeleton:1131)  ── D1 "=" (deepest-point normal form)
│        filler chain (front-pivot): aoyagi_learning_coefficient_frontPivot
│        (DeepestNormalFormFrontPivot:125)
│          → deepest_normal_form_of_value_frontPivot (:91)
│          → deepest_regular_core_reduces_frontPivot (:62)
│          → deepest_gauge_squeeze_exists_frontPivot (:46)
│          → deepest_gauge_chart_construct (DeepestL2Wiring:1067)
│          → deepest_gauge_construction (:704, L≥3 arm)
│        ├─ [LEAF] hstep2  ......................... DeepestL2Wiring:1060
│        ├─ hRValue = R1 value (r1_resolution_general + hbox)
│        │    └─ hbox = RouteMBoxThresholdFinite M  (routeMBoxThresholdFinite_sjResolution:950)
│        │         └─ [LEAF] sjJointResolution ..... RouteMSJResolution:803
│        ├─ hGne (reduced-core germ ≠0) ............ minor leaf, not yet wired ∀L
│        └─ hJfront/htop (WLOG) ................... BUILT sorry-free (HeadlineRowColPermWLOG)
│
└─ deepest_point_reduction (Skeleton:1187)   [le_antisymm; ≥ half = le_iInf₂ of the leaf below]
    └─ rlctAt_deepest_le_of_optimal (Skeleton:1177)  ── D1 "≤" (fibre monotonicity)
         engine deepest_le_of_optimal_chart (D1ChartProducer:100) needs
         ├─ hDeepest = the "=" normal form   (SHARED → hstep2)
         └─ [UNCOVERED] hchart (IFT residual chart AT v) + hCore + hcmp
```

`deepest_point_reduction` (Skeleton:1187-1197) is `le_antisymm`: the `≤` is `iInf₂_le`
(`deepestPoint ∈ optimalSet`, PROVEN); the `≥` is `le_iInf₂ (rlctAt_deepest_le_of_optimal …)`. So
the ≥-leg is genuinely required — no shortcut.

---

## Q1 — is `hstep2` the ONLY open obligation in `deepest_gauge_construction`'s `L ≥ 3` branch?

**YES.** `hstep2` (`DeepestL2Wiring:1060`) is the only `sorry` in `DeepestL2Wiring.lean`. The
route-first comments about "four named obligations / hinterface / folded core" are **stale**:

- `hinterface` (L≥3, @903–921) is discharged from `hInterior` (bundle
  `deepestPoint_frame_pivot_triangular_exists`).
- The "REMAINING GAP π̃ / PIN1" comment (@818–824) is discharged by the `hTilde` block (@825–877),
  which proves ContDiff + invertible strict-deriv via `deepestEFull_deriv`.
- `hstep1` (@961–1051) is sorry-free (Params→flat MP transport + `rlctAtOn_squeeze`).

All lemmas the L≥3 arm calls are sorry-free: `deepestSplit`, `deepestSplit_mp_basepoint`,
`deepestPoint_frame_pivot_triangular_exists`, `deepest_coreAbsorb_exists`, `deepestEFull_deriv`
/`_contdiff`/`_base`, `contDiff_schurCutoffShift`, `contDiff_coreShearHomeo_symm`,
`hasStrictFDerivAt_coreShearHomeo_symm_zero`, `contDiff_regStraightenOf2`,
`hasStrictFDerivAt_regStraightenOf2_gen`, `deepest_regAbsorb_exists`, `deepest_loss_squeeze`,
`deepest_gauge_construction_L2`. So closing `hstep2` ⟹ `deepest_gauge_construction` is clean.

---

## Q2 — headline structure

`aoyagi_learning_coefficient` (`Skeleton:1725`) proof term = `deepest_point_reduction ▸
product_reduction`. It does **not** reference `aoyagiTheta_eq` (`Skeleton:1707`) — θ is genuinely
secondary, off the coefficient-value path. Two direct sorry-leaves: `Skeleton:1131` (via
`product_reduction`) and `Skeleton:1177` (via `deepest_point_reduction`).

---

## Ranked OPEN leaves on the critical path

1. **`hstep2`** — `DeepestL2Wiring.lean:1060`. The gauge diffeo gap (L≥3). *Covered* by the in-flight
   hderiv0 / hC / hcd tides (`hderiv0b`, `hcfinish` = hC lemmas 2–6, the held `hcd`). Serves the
   "=" side only.
2. **`sjJointResolution`** — `RouteMSJResolution.lean:803`. The R1-UPPER (S,J) joint-resolution CoV.
   The **sole** R1 leaf: `routeMBoxThresholdFinite_sjResolution` (:950) =
   `of_step(sjResolutionStep_proof)(sjBase1_freeMatrix)`, and both `sjBoundaryPeel` (:688) and
   `sjBase1_freeMatrix` (:912) are sorry-free. Discharges `hbox`, hence `r1_resolution_general`'s
   value. *Covered* by the in-flight R1-UPPER (FrontPeelStep / `sjJointResolution`) tide.
3. **`Skeleton:1131`** `deepest_regular_core_normal_form` — the "=" ASSEMBLY sorry: wire the
   front-pivot capstone + discharge `hGne`. *Covered* by the skeleton-assembly tide.
4. **`Skeleton:1177`** `rlctAt_deepest_le_of_optimal` — the "≤" ASSEMBLY sorry. Its engine's extra
   inputs are the uncovered gap below.
5. `hGne` (reduced-core germ-nonvanishing) — minor; dischargeable (reduced core is a nonzero
   polynomial ⟹ a.e. ≠0, cf. banked `eDeepRank0Unit_ae_pos`), not yet wired ∀L.

The `"="`-side front-pivot chain and WLOG hub (`HeadlineRowColPermWLOG`, `HeadlineColPermWLOG`,
`DeepestNormalFormWiring`, `DeepestFrontGauge`, `DeepestNormalFormFrontPivotL2`) are all sorry-free.

---

## ⚠️ UNCOVERED GAP (no in-flight tide addresses it)

**The general-`L` D1 ≥-leg IFT-chart-at-`v` producer** — `hchart :
rlctAt (dlnLoss H B) v = rlctAtOn (∑ s² + ∑ q²) (0, t0)` plus `hCore` (leading-form comparison),
consumed by `deepest_le_of_optimal_chart` (`D1ChartProducer:100`).

- Every D1-≥ chart producer is **L=2-only**: `dln_hchart_residual` (`D1HChartResidual:343`) is
  stated with `H 2` / `nRegL2` / `jacFlatL2`; the `GeneralVChartL2` structure is L=2; **all**
  `D1*.lean` carry `H : Fin 3`.
- `lean/CLAUDE.md`'s "L2 D1 two-peel `hrank₂`" note flags even the L=2 realization as a genuine
  new-module wall (needs b1 = a producer variant exposing `HasFDerivAt (q(0,·))`; b2 = a
  network-free `rank(L) = rank T − nReg` module; b3 = the `(a,b)` extraction). The general-`L`
  analog is unbuilt.
- `hstep2` does NOT touch it: `hstep2` is the deepest-point grouped diffeo; `hchart` is a
  `v`-parameterized residual chart. Related machinery ("(a) is the SAME constant-rank chart
  machinery as #44", per the `Skeleton:1177` docstring), but a distinct theorem no in-flight tide
  produces.

**This is the thing to not miss.** Treating "D1 #120 = `hstep2`" understates D1 by exactly this
producer.

---

## OFF-path / DEAD (do not chase)

- **`aoyagiTheta_eq`** (`Skeleton:1707`) — θ component-count, secondary; not in the coefficient-value
  proof term.
- **`deepest_gauge_squeeze_exists`** (`DeepestGaugeChart:357`) — DEAD stub, superseded by the
  `_frontPivot` route. Only the general-`B` `deepest_regular_core_reduces` (`DeepestGaugeChart:539`)
  calls it, and the headline uses the front-pivot chain instead. **Wiring note:** when filling
  `Skeleton:1131`, route via `..._frontPivot`, NOT the general-`B` reduce (else you re-import this
  sorry).
- **R1-UPPER legacy alt-route sorries** — all NOT imported by
  `r1_resolution_general` / `routeMLayerCover_hfin` (confirmed by import check + AxCheck's "do not
  leak" note for RouteMRecursion/RouteMSchur):
  - `RouteMInteriorLDUContract.lean` — 124, 130, 145, 153, 165, 192, 199, 212, 222 (9 sorries)
  - `RouteMRecursion.lean:257`
  - `RouteMSchur.lean:429`
  - `RouteMSchurGeneral.lean:144`
  - `RouteMLayerCoverGE.lean:133`
- **`resolution_charts`** (`Skeleton:1234`) — the R1 chart-**existence** rung. The headline needs only
  the R1 **value** (`r1_resolution_general` gives `rlctAtOn(dlnLoss M 0) 0 = ofReal(lambdaCore M)`),
  so this rung is likely bypassed / redundant on the value path. Verify before spending on it.

---

## Full standalone-`sorry` inventory (20 total)

| File | Lines | Status |
|---|---|---|
| `Skeleton.lean` | 1131 | ON-PATH ("=" assembly) |
| `Skeleton.lean` | 1177 | ON-PATH ("≤" assembly; needs uncovered `hchart`) |
| `Skeleton.lean` | 1234 | likely BYPASSED (R1 chart-existence rung) |
| `Skeleton.lean` | 1707 | OFF-PATH (θ, secondary) |
| `DeepestL2Wiring.lean` | 1060 | ON-PATH (`hstep2`, "=" gauge diffeo) |
| `RouteMSJResolution.lean` | 803 | ON-PATH (`sjJointResolution`, sole R1 leaf) |
| `DeepestGaugeChart.lean` | 357 | DEAD stub (superseded by `_frontPivot`) |
| `RouteMInteriorLDUContract.lean` | 124,130,145,153,165,192,199,212,222 | DEAD (alt-route) |
| `RouteMRecursion.lean` | 257 | DEAD (alt-route) |
| `RouteMSchur.lean` | 429 | DEAD (alt-route) |
| `RouteMSchurGeneral.lean` | 144 | DEAD (alt-route) |
| `RouteMLayerCoverGE.lean` | 133 | DEAD (alt-route) |

---

## Reflection

- **Most likely to advance the expedition:** `sjJointResolution` (R1) — a clean single leaf that
  discharges all of `hbox` through the sorry-free arity induction; the R1 machinery around it is
  complete.
- **Most likely to break / the surprise:** the D1 ≥-leg — not one leaf but a missing general-`L`
  module (chart-at-`v` + `hCore`), with only an L=2 realization that was itself flagged as a
  new-module wall.
- **Next computation that would clarify:** (i) a force-recompiled `#print axioms` on
  `deepest_point_reduction` vs `product_reduction`, confirming the two Skeleton leaves are the only
  `sorryAx` sources of the headline today; (ii) a scoping pass on whether the general-`L` ≥-leg
  chart can be obtained by re-parameterizing the existing gauge-slice machinery at a general `v`
  (re-thread) versus a from-scratch build — this decides whether the uncovered gap is a re-thread or
  a genuine new tide.
