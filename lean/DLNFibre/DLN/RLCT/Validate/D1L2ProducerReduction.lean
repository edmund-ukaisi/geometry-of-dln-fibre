import DLNFibre.DLN.RLCT.Validate.D1IFTResidualProducer
import DLNFibre.DLN.RLCT.Validate.D1HChartResidual
import DLNFibre.DLN.RLCT.Validate.DeepestFrontGauge
import DLNFibre.DLN.RLCT.Validate.R1ResolutionInterfaceL2

/-!
# `DLNFibre.DLN.RLCT.Validate.D1L2ProducerReduction` — the general-`v` D1 `≥`-leg reduction (L = 2)

The finite-atlas re-architecture of the D1 `≥`-leg at L = 2, wired as far as the banked producers
honestly reach. This module does NOT close the leaf; it turns the bare per-point obligation into a
LEGIBLE reduction whose remaining debt is one precisely-named per-`v` fact — the **residual-core
domination** — with the (fully banked, sorry-free) FIRST selected-minor peel produced INSIDE the
proof.

## What is banked (consumed, not re-proved) and why the first peel is UNCONDITIONAL

The finite-atlas route (`genm-d1reduce` cert) replaces the abstract-IFT/splitting chart — whose
`hRform` germ-factorization is FALSE at a middle-stratum `v` — with a **selected-minor IFT atlas**:
at every optimal `v` (`prod H v = B`, `rank B = r`), the flat Jacobian `jacFlatL2` has rank `≥ nReg`
(the load-bearing coverage invariant `rank(∏A) ≥ r`, banked as `nReg_le_jacFlatL2_rank`), so an
invertible `nReg × nReg` minor ALWAYS exists (`exists_jacFlatL2_minor`, sorry-free). Around it, the
ordinary pointwise IFT chart (`dln_hchart_residual`, sorry-free, clean-three) brings the loss into
the post-chart sum-of-squares form

    rlctAt H (dlnLoss H B) v = rlctAtOn (fun p => (∑ i, p.1 i ^ 2) + (∑ i, q p i ^ 2)) (0, t0),

with a GLOBAL `C¹` residual `q` on `(Fin nReg → ℝ) × (Fin (flatDim H − nReg) → ℝ)`. This is the
`nReg`-block of the split, valid at EVERY optimal `v` (no rank-`r`-exactness, no deepest-gauge
chart, no Morse-Bott lemma). The quasi-split engine `rlct_quasiSplit_ge` (via
`rlctAt_ge_nReg_add_slice_of_residual`) then delivers the `hAtV` half

    nReg/2 + rlctAtOn R t0 ≤ rlctAt H (dlnLoss H B) v,   R t := ∑ i, q (0, t) i ^ 2

from `q`'s smoothness + the residual being a.e.-nonzero near `t0`.

## The precisely-named residual (NOT wall-laundering)

`deepest_le_of_optimal_via_L2_ge` (banked) closes `rlctAt deepest ≤ rlctAt v` from `hDeepest`
(deepest-side value, `= nReg/2 + coreDeepest`) + the `hAtV` half +
`hCore : coreDeepest ≤ rlctAtOn R t0`. The FIRST peel produces `hAtV`; the SOLE remaining per-`v`
content is the **residual-core domination** `coreDeepest ≤ rlctAtOn R t0` (that the first-peel slice
residual has RLCT `≥` the deepest core) and the slice non-vanishing `hRne`.

The reduction below states this as the hypothesis `hDom`, quantified over EVERY first-peel residual
`(q, t0)` (any chart output must satisfy it) — the genuine per-`v` mathematical content, NOT a
disguised chart existence. `hchart`/`ContDiff` are the chart's OWN facts, PRODUCED inside the proof;
`hDom` is only asked to supply the residual value comparison + non-vanishing. Its honest discharge
is Aoyagi's Theorem-4 homogeneity comparison applied through the SECOND selected-minor peel + the
degraded-core R1 value (`D1SecondPeel*` + `D1ChartProducerL2Build`, square-widths so far), which is
the tracked residual content, not built here.

Scope L = 2 (`H : Fin 3 → ℕ`); general `H` and general optimal `v`. The general-L Skeleton sorry
`rlctAt_deepest_le_of_optimal` stays #120-walled — NOT touched. This file does NOT edit
`Skeleton.lean` (single-writer) nor `HeadlineL2Assembly.lean`'s leaf (which stays correctly-stated).
-/

open MeasureTheory
open scoped ENNReal Topology
namespace DLNFibre.DLN.RLCT

/-- **The general-`v` D1 `≥`-leg reduction at L = 2 (first-peel wired, residual isolated).**

At a general optimal `v` (`prod H v = B`, `rank B = r`), given:
  * `hDeepest` — the deepest-side value equality `rlctAt deepest = nReg/2 + coreDeepest` (banked #44
    at L = 2 via `deepest_regular_core_normal_form_L2_front`; here a hypothesis so the reduction is
    `deepest`-agnostic);
  * `hDom` — the **residual-core domination**: for EVERY first-peel residual `(q, t0)` on the flat
    product slice (any output of the selected-minor IFT chart `dln_hchart_residual` — the hypothesis
    is fed the chart's own `ContDiff`/`hchart` facts), the slice residual `R t = ∑ q(0,t) i ²` is
    a.e.-nonzero near `t0` AND `coreDeepest ≤ rlctAtOn R t0`,

the deepest point has `≤` local RLCT than `v`. The FIRST selected-minor peel (the `nReg`-block,
UNCONDITIONAL via `exists_jacFlatL2_minor` + `dln_hchart_residual`) is produced INSIDE the proof and
feeds the `hAtV` half through `rlctAt_ge_nReg_add_slice_of_residual`; then
`deepest_le_of_optimal_via_L2_ge` closes with `hDeepest` + `hDom`. `nReg = nRegL2 H r`. -/
theorem d1ge_L2_of_firstPeel_dominates
    (H : Fin (2 + 1) → ℕ) (r : ℕ) (B : Matrix (Fin (H 0)) (Fin (H (Fin.last 2))) ℝ)
    (deepest v : Params H) (coreDeepest : ℝ≥0∞)
    (hopt : prod H v = B) (hB : B.rank = r)
    (hDeepest : rlctAt H (dlnLoss H B) deepest = (nRegL2 H r : ℝ≥0∞) / 2 + coreDeepest)
    (hDom : ∀ (q : (Fin (nRegL2 H r) → ℝ) × (Fin (flatDim H - nRegL2 H r) → ℝ)
              → EuclideanSpace ℝ (Fin (H 0 * H 2)))
          (t0 : Fin (flatDim H - nRegL2 H r) → ℝ),
        ContDiff ℝ 1 q →
        rlctAt H (dlnLoss H B) v
            = rlctAtOn (fun p : (Fin (nRegL2 H r) → ℝ) × (Fin (flatDim H - nRegL2 H r) → ℝ) =>
                (∑ i, p.1 i ^ 2) + (∑ i, q p i ^ 2)) ((0 : Fin (nRegL2 H r) → ℝ), t0) →
        (∃ U ∈ 𝓝 t0, ∀ᵐ z ∂(volume.restrict U),
            (∑ i, q ((0 : Fin (nRegL2 H r) → ℝ), z) i ^ 2) ≠ 0)
          ∧ coreDeepest
              ≤ rlctAtOn (fun t : Fin (flatDim H - nRegL2 H r) → ℝ =>
                  ∑ i, q ((0 : Fin (nRegL2 H r) → ℝ), t) i ^ 2) t0) :
    rlctAt H (dlnLoss H B) deepest ≤ rlctAt H (dlnLoss H B) v := by
  -- FIRST peel: the invertible `nReg`-minor of the flat Jacobian
  -- (coverage `nReg ≤ jacFlatL2.rank`).
  obtain ⟨er, ec, her, hec, hminor⟩ := exists_jacFlatL2_minor H r v B hopt hB
  -- the selected-minor IFT chart: the post-chart sum-of-squares form with a global `C¹` residual.
  obtain ⟨q, t0, hqCD, hchart⟩ :=
    dln_hchart_residual (m := nRegL2 H r) (ec := ec) hopt hB her hec hminor
  -- the residual-core domination + non-vanishing at this residual (the isolated per-`v` content).
  obtain ⟨hRne, hCore⟩ := hDom q t0 hqCD hchart
  -- the `hAtV` half from the `C¹` first-peel residual (quasi-split engine; no bare chart data).
  have hAtV : (nRegL2 H r : ℝ≥0∞) / 2
        + rlctAtOn (fun t : Fin (flatDim H - nRegL2 H r) → ℝ =>
            ∑ i, q ((0 : Fin (nRegL2 H r) → ℝ), t) i ^ 2) t0
      ≤ rlctAt H (dlnLoss H B) v :=
    rlctAt_ge_nReg_add_slice_of_residual (m := nRegL2 H r) H B v q hqCD t0 hchart hRne
  -- close: deepest value + `hAtV` + `hCore` through the banked arithmetic wiring.
  exact deepest_le_of_optimal_via_L2_ge (B := B) H r (rlctAt H (dlnLoss H B) deepest)
    (rlctAt H (dlnLoss H B) v) (nRegL2 H r) coreDeepest
    (rlctAtOn (fun t : Fin (flatDim H - nRegL2 H r) → ℝ =>
      ∑ i, q ((0 : Fin (nRegL2 H r) → ℝ), t) i ^ 2) t0)
    hDeepest hAtV hCore

/-- **The LEAF-2-shaped reduction (drop-in for `HeadlineL2Assembly`).** At the front-pivoted `B`
(`htop`/`hcolfront` supplied by the headline column/row WLOG), for the constructed `deepestPoint`,
the D1 per-point `≥`-leg reduces to the SAME residual-core domination `hDom` — with the deepest-side
value `hDeepest` produced INSIDE from the banked `deepest_regular_core_normal_form_L2_front` (#44 at
L = 2) fed the banked R1 value `r1_resolution_interface_L2_generic`. So `coreDeepest =
ofReal(lambdaCore (H − r))` (the general-`H`, NOT square, deepest core value), and the ONLY
remaining per-`v` input is `hDom`. Matching the exact `HeadlineL2Assembly` `hD1ge_L2` slot, this is
the drop-in that closes LEAF 2 once the residual-domination producer (the SECOND selected-minor
peel + degraded-core R1 value — the tracked analytic content) lands. `nReg = nRegL2 H r`. -/
theorem d1ge_L2_deepestPoint_of_firstPeel_dominates
    (H : Fin (2 + 1) → ℕ) (r : ℕ) (B : Matrix (Fin (H 0)) (Fin (H (Fin.last 2))) ℝ)
    (hB : B.rank = r) (hr : ∀ s : Fin (2 + 1), r ≤ H s) (hL : 1 ≤ 2)
    (hpos : ∀ s : Fin (2 + 1), r < H s)
    (htop : (B.submatrix (Fin.castLE (hr 0) : Fin r → Fin (H 0))
        (id : Fin (H (Fin.last 2)) → Fin (H (Fin.last 2)))).rank = r)
    (hcolfront : (B.submatrix (id : Fin (H 0) → Fin (H 0))
        (Fin.castLE (hr (Fin.last 2)) : Fin r → Fin (H (Fin.last 2)))).rank = r)
    (v : Params H) (hopt : prod H v = B)
    (hDom : ∀ (q : (Fin (nRegL2 H r) → ℝ) × (Fin (flatDim H - nRegL2 H r) → ℝ)
              → EuclideanSpace ℝ (Fin (H 0 * H 2)))
          (t0 : Fin (flatDim H - nRegL2 H r) → ℝ),
        ContDiff ℝ 1 q →
        rlctAt H (dlnLoss H B) v
            = rlctAtOn (fun p : (Fin (nRegL2 H r) → ℝ) × (Fin (flatDim H - nRegL2 H r) → ℝ) =>
                (∑ i, p.1 i ^ 2) + (∑ i, q p i ^ 2)) ((0 : Fin (nRegL2 H r) → ℝ), t0) →
        (∃ U ∈ 𝓝 t0, ∀ᵐ z ∂(volume.restrict U),
            (∑ i, q ((0 : Fin (nRegL2 H r) → ℝ), z) i ^ 2) ≠ 0)
          ∧ ENNReal.ofReal (lambdaCore (fun s => H s - r) : ℝ)
              ≤ rlctAtOn (fun t : Fin (flatDim H - nRegL2 H r) → ℝ =>
                  ∑ i, q ((0 : Fin (nRegL2 H r) → ℝ), t) i ^ 2) t0) :
    rlctAt H (dlnLoss H B) (deepestPoint H r B hB hr hL)
      ≤ rlctAt H (dlnLoss H B) v := by
  -- the deepest-side value: #44-at-L2 (front-pivot) fed the banked R1 value at `M = H − r`.
  have hDeepest : rlctAt H (dlnLoss H B) (deepestPoint H r B hB hr hL)
      = (nRegL2 H r : ℝ≥0∞) / 2 + ENNReal.ofReal (lambdaCore (fun s => H s - r) : ℝ) :=
    deepest_regular_core_normal_form_L2_front H r B hB hr hL (le_refl 2) hpos htop hcolfront
      (by norm_num)
      (r1_resolution_interface_L2_generic (le_refl 2) (by norm_num) (fun s => H s - r)
        (fun s => Nat.sub_pos_of_lt (hpos s)))
  exact d1ge_L2_of_firstPeel_dominates H r B (deepestPoint H r B hB hr hL) v
    (ENNReal.ofReal (lambdaCore (fun s => H s - r) : ℝ)) hopt hB hDeepest hDom

end DLNFibre.DLN.RLCT
