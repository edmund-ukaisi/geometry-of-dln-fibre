import DLNFibre.DLN.RLCT.Validate.D1HChartResidualC2
import DLNFibre.DLN.RLCT.Validate.D1RectSecondPeel
import DLNFibre.DLN.RLCT.Validate.D1IFTResidualProducer
import DLNFibre.DLN.RLCT.Validate.DeepestMinRlct

/-!
# `DLNFibre.DLN.RLCT.Validate.D1RectHDomProducer` — the two-peel D1 `≥` at a general `H`, general `v`

The RECTANGULAR two-peel D1 per-point `≥`-leg producer, assembling the pieces this thread built:
  * `dln_hchart_residual_c2` (item 5): the FIRST-peel `C²` residual `q` with slice-vanishing
    `q (0, t0) = 0` — the reviewer-flagged `C²` gap, closed.
  * `hCoreRect_of_slice_data` (item 2 rect + the second peel): the case-(B) `hCore` at the RECTANGULAR
    deepest widths `M = H − r`, via the CROSS-paired `extraCountRect`.

The FIRST peel's `hAtV` half (`rlctAt_ge_nReg_add_slice_of_residual`) + the second-peel `hCore`
combine through `deepest_le_of_optimal_via_L2_ge`. The result reduces the D1 `≥`-leg at a general
optimal `v` to exactly THREE precisely-named per-`v` geometric gates (NOT laundered — they are the
genuine middle-stratum content the chart-unwind + R1 supply):

  1. **`hrank₂`** — the second-peel Jacobian RANK bound `extraCountRect M0 M2 a b ≤ rank(jacResid h t0)`
     for the first-peel slice residual `h = q (0,·)` at its basepoint. The DLN Jacobian excess IS this
     cross-paired count (decorrelated-certified: `rank D = (r+b)H0 + (r+a)H2 − (r+a)(r+b)`); the OPEN
     part is tying that excess to the BUMP-globalised residual's Jacobian via the chart-unwind.
  2. **`hInterface`** (R1 at `M'`) — the degraded-core residual has RLCT `ofReal(lambdaCore M')`, i.e.
     the R₂-to-`M'`-core identification. R1's VALUE is banked (`r1ResolutionInterface_L2`); the OPEN
     part is that the second-peel residual IS the `M'`-core.
  3. **`(a, b, hslicerank …)`** — the middle-stratum layer-rank rises `(a, b)` at `v` (with
     `a ≤ M0`, `a + b ≤ M1`, `b ≤ M2`, and `hRne` slice non-vanishing).

## Honest status

This is a REDUCTION, not a closure: it wires the two banked-here peels + the value arithmetic, leaving
the THREE named geometric gates. It sharpens the prior `D1L2ProducerReduction` residual (a single
`hDom` over the C¹ residual) into a two-peel C² chain whose remaining debt is these three named per-`v`
facts. Their honest discharge is the middle-stratum chart-unwind (`hrank₂` + `(a,b)` extraction) and
the R1 degraded-core identification (`hInterface`) at a general `v` — the genuine analytic residual,
NOT built here and NOT laundered as a disguised chart existence.

Scope L = 2 (`H : Fin 3 → ℕ`), deepest reduced widths `M = H − r`.
-/

open MeasureTheory
open scoped ENNReal Topology
namespace DLNFibre.DLN.RLCT

/-- The C² first-peel slice residual `h := q (0,·)` is `C²` (composition of the `C²` `q` with the
affine slice inclusion `t ↦ (0, t)`). -/
theorem contDiff_slice_of_contDiff {m N n : ℕ}
    (q : (Fin m → ℝ) × (Fin N → ℝ) → EuclideanSpace ℝ (Fin n)) (hq : ContDiff ℝ 2 q) :
    ContDiff ℝ 2 (fun t : Fin N → ℝ => q ((0 : Fin m → ℝ), t)) :=
  hq.comp (contDiff_const.prodMk contDiff_id)

/-- **The rectangular two-peel D1 per-point `≥`-leg at a general optimal `v`.** At `v` optimal
(`prod H v = B`, `rank B = r`), with the deepest-side value `hDeepest` (Route-A form, `coreDeepest =
ofReal(lambdaCore (H − r))`), the middle-stratum layer-rank data `(a, b)` (`a ≤ M0`, `a+b ≤ M1`,
`b ≤ M2` for `M = H − r`), the second-peel RANK bound `hrank₂`, the slice non-vanishing `hRne`, and
the R1 degraded-core interface `hInterface`, the deepest point has `≤` local RLCT than `v`.

The FIRST peel (`dln_hchart_residual_c2`, `C²` + slice-vanishing) is built INSIDE; its `hAtV` half
(`rlctAt_ge_nReg_add_slice_of_residual`, `C¹`-downgraded) + the second-peel `hCore`
(`hCoreRect_of_slice_data`) close through `deepest_le_of_optimal_via_L2_ge`. `M = fun s => H s − r`,
`extra = extraCountRect (M 0) (M 2) a b` (cross-paired). -/
theorem d1ge_L2_rect_two_peel
    (H : Fin (2 + 1) → ℕ) (r : ℕ) (B : Matrix (Fin (H 0)) (Fin (H (Fin.last 2))) ℝ)
    (deepest v : Params H) (a b : ℕ)
    (hopt : prod H v = B) (hB : B.rank = r)
    (ha : a ≤ H 0 - r) (hab : a + b ≤ H 1 - r) (hb : b ≤ H 2 - r)
    (hDeepest : rlctAt H (dlnLoss H B) deepest
        = (nRegL2 H r : ℝ≥0∞) / 2 + ENNReal.ofReal (lambdaCore (fun s => H s - r) : ℝ))
    -- the second-peel RANK bound on the first-peel slice residual (at ANY such residual `q`, `t0`)
    (hrank₂ : ∀ (q : (Fin (nRegL2 H r) → ℝ) × (Fin (flatDim H - nRegL2 H r) → ℝ)
                → EuclideanSpace ℝ (Fin (H 0 * H 2)))
          (t0 : Fin (flatDim H - nRegL2 H r) → ℝ),
        ContDiff ℝ 2 q → q ((0 : Fin (nRegL2 H r) → ℝ), t0) = 0 →
        rlctAt H (dlnLoss H B) v
            = rlctAtOn (fun p : (Fin (nRegL2 H r) → ℝ) × (Fin (flatDim H - nRegL2 H r) → ℝ) =>
                (∑ i, p.1 i ^ 2) + (∑ i, q p i ^ 2)) ((0 : Fin (nRegL2 H r) → ℝ), t0) →
        extraCountRect (H 0 - r) (H 2 - r) a b
          ≤ (jacResid (fun t : Fin (flatDim H - nRegL2 H r) → ℝ =>
              q ((0 : Fin (nRegL2 H r) → ℝ), t)) t0).rank)
    -- slice non-vanishing (the `hAtV` half's a.e.-nonzero input)
    (hRne : ∀ (q : (Fin (nRegL2 H r) → ℝ) × (Fin (flatDim H - nRegL2 H r) → ℝ)
                → EuclideanSpace ℝ (Fin (H 0 * H 2)))
          (t0 : Fin (flatDim H - nRegL2 H r) → ℝ),
        ContDiff ℝ 2 q → q ((0 : Fin (nRegL2 H r) → ℝ), t0) = 0 →
        rlctAt H (dlnLoss H B) v
            = rlctAtOn (fun p : (Fin (nRegL2 H r) → ℝ) × (Fin (flatDim H - nRegL2 H r) → ℝ) =>
                (∑ i, p.1 i ^ 2) + (∑ i, q p i ^ 2)) ((0 : Fin (nRegL2 H r) → ℝ), t0) →
        ∃ U ∈ 𝓝 t0, ∀ᵐ z ∂(volume.restrict U),
          (∑ i, q ((0 : Fin (nRegL2 H r) → ℝ), z) i ^ 2) ≠ 0)
    -- the R1 degraded-core interface at `M' = MprimeRect (H − r) a b`, on the BUILT second-peel residual
    (hInterface : ∀ (q : (Fin (nRegL2 H r) → ℝ) × (Fin (flatDim H - nRegL2 H r) → ℝ)
                → EuclideanSpace ℝ (Fin (H 0 * H 2)))
          (t0 : Fin (flatDim H - nRegL2 H r) → ℝ),
        ContDiff ℝ 2 q → q ((0 : Fin (nRegL2 H r) → ℝ), t0) = 0 →
        rlctAt H (dlnLoss H B) v
            = rlctAtOn (fun p : (Fin (nRegL2 H r) → ℝ) × (Fin (flatDim H - nRegL2 H r) → ℝ) =>
                (∑ i, p.1 i ^ 2) + (∑ i, q p i ^ 2)) ((0 : Fin (nRegL2 H r) → ℝ), t0) →
        ∀ (q₂ : (Fin (extraCountRect (H 0 - r) (H 2 - r) a b) → ℝ)
              × (Fin ((flatDim H - nRegL2 H r) - extraCountRect (H 0 - r) (H 2 - r) a b) → ℝ)
              → EuclideanSpace ℝ (Fin (H 0 * H 2)))
            (t0₂ : Fin ((flatDim H - nRegL2 H r) - extraCountRect (H 0 - r) (H 2 - r) a b) → ℝ),
          (rlctAtOn (fun t : Fin (flatDim H - nRegL2 H r) → ℝ =>
              ∑ i, q ((0 : Fin (nRegL2 H r) → ℝ), t) i ^ 2) t0
              = rlctAtOn (fun p : (Fin (extraCountRect (H 0 - r) (H 2 - r) a b) → ℝ)
                    × (Fin ((flatDim H - nRegL2 H r) - extraCountRect (H 0 - r) (H 2 - r) a b) → ℝ) =>
                  (∑ i, p.1 i ^ 2) + (∑ i, q₂ p i ^ 2))
                  ((0 : Fin (extraCountRect (H 0 - r) (H 2 - r) a b) → ℝ), t0₂)) →
          (∃ U ∈ 𝓝 t0₂, ∀ᵐ z ∂(volume.restrict U),
              (∑ i, q₂ ((0 : Fin (extraCountRect (H 0 - r) (H 2 - r) a b) → ℝ), z) i ^ 2) ≠ 0)
            ∧ rlctAtOn (fun t : Fin ((flatDim H - nRegL2 H r)
                  - extraCountRect (H 0 - r) (H 2 - r) a b) → ℝ =>
                ∑ i, q₂ ((0 : Fin (extraCountRect (H 0 - r) (H 2 - r) a b) → ℝ), t) i ^ 2) t0₂
              = ENNReal.ofReal (lambdaCore (MprimeRect (fun s => H s - r) a b) : ℝ)) :
    rlctAt H (dlnLoss H B) deepest ≤ rlctAt H (dlnLoss H B) v := by
  -- FIRST peel: the invertible `nReg`-minor of the flat Jacobian.
  obtain ⟨er, ec, her, hec, hminor⟩ := exists_jacFlatL2_minor H r v B hopt hB
  -- the C² first-peel chart: `q` global `C²`, slice-vanishing, the post-chart sum-of-squares form.
  obtain ⟨q, t0, hqCD, hq0, hchart⟩ :=
    dln_hchart_residual_c2 (m := nRegL2 H r) (ec := ec) hopt hB her hec hminor
  -- the slice residual `h = q (0,·)`, `C²`, vanishing at `t0`.
  set h : (Fin (flatDim H - nRegL2 H r) → ℝ) → EuclideanSpace ℝ (Fin (H 0 * H 2)) :=
    fun t => q ((0 : Fin (nRegL2 H r) → ℝ), t) with hhdef
  have hhCD : ContDiff ℝ 2 h := contDiff_slice_of_contDiff q hqCD
  have hh0 : h t0 = 0 := hq0
  -- the per-`v` geometric inputs, instantiated at this concrete first-peel `q`.
  have hRne' := hRne q t0 hqCD hq0 hchart
  have hrank' := hrank₂ q t0 hqCD hq0 hchart
  have hInterface' := hInterface q t0 hqCD hq0 hchart
  -- the `hAtV` half from the (C¹-downgraded) first-peel residual.
  have hAtV : (nRegL2 H r : ℝ≥0∞) / 2
        + rlctAtOn (fun t : Fin (flatDim H - nRegL2 H r) → ℝ =>
            ∑ i, q ((0 : Fin (nRegL2 H r) → ℝ), t) i ^ 2) t0
      ≤ rlctAt H (dlnLoss H B) v :=
    rlctAt_ge_nReg_add_slice_of_residual (m := nRegL2 H r) H B v q
      (hqCD.of_le (by exact_mod_cast (one_le_two : (1 : ℕ) ≤ 2))) t0 hchart hRne'
  -- the second-peel `hCore` at the RECTANGULAR deepest widths `M = H − r`.
  have hCore : ENNReal.ofReal (lambdaCore (fun s => H s - r) : ℝ)
      ≤ rlctAtOn (fun t : Fin (flatDim H - nRegL2 H r) → ℝ =>
          ∑ i, q ((0 : Fin (nRegL2 H r) → ℝ), t) i ^ 2) t0 :=
    hCoreRect_of_slice_data (fun s => H s - r) a b ha hab hb h t0 hhCD hh0 hrank' hInterface'
  -- close through the arithmetic combine.
  exact deepest_le_of_optimal_via_L2_ge (B := B) H r
    (rlctAt H (dlnLoss H B) deepest) (rlctAt H (dlnLoss H B) v) (nRegL2 H r)
    (ENNReal.ofReal (lambdaCore (fun s => H s - r) : ℝ))
    (rlctAtOn (fun t : Fin (flatDim H - nRegL2 H r) → ℝ =>
      ∑ i, q ((0 : Fin (nRegL2 H r) → ℝ), t) i ^ 2) t0)
    hDeepest hAtV hCore

end DLNFibre.DLN.RLCT
