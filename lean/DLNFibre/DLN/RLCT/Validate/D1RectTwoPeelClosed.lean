import DLNFibre.DLN.RLCT.Validate.D1RectHrankClose
import DLNFibre.DLN.RLCT.Validate.D1RectHDomProducer
import DLNFibre.DLN.RLCT.Validate.D1ResidualRankIdentity

/-!
# `D1RectTwoPeelClosed` — the two-peel D1 `≥`-leg with `hrank₂` DISCHARGED (b3 wired in)

`d1ge_L2_rect_two_peel` (`D1RectHDomProducer`) leaves THREE named per-`v` gates: `hrank₂` (the
second-peel Jacobian rank), `hRne` (slice non-vanishing), `hInterface` (R1 degraded core). This
module discharges **`hrank₂`** by re-threading the producer through the DERIVATIVE-exposing first
peel (`residJacobian_rank_eq`, which carries the residual-Jacobian rank of its OWN `q`) and the b3
count (`jacFlatL2_rank_sub_nReg_eq_extraCountRect`).

The layer-rank rises are FIXED to their true values `a = frontRise = rank(v⁰)−r`,
`b = backRise = rank(v¹)−r`; the honest-subtraction constraints `a ≤ H0−r`, `a+b ≤ H1−r`
(Sylvester), `b ≤ H2−r` are derived here (`r_le_layer_ranks`, `layer_ranks_sylvester`, width
bounds). What remains open is `hRne` + `hInterface` (the two OTHER named gates), still taken as
hypotheses (instantiated at the re-threaded producer's `q`).

Scope L = 2 (`H : Fin 3 → ℕ`), deepest reduced widths `M = H − r`.
-/

open Matrix Module MeasureTheory
open scoped ENNReal Topology
namespace DLNFibre.DLN.RLCT

/-- **The two-peel D1 `≥`-leg with `hrank₂` closed by b3.** At an optimal `v` (`prod v = B`,
`rank B = r`), the deepest point has `≤` local RLCT than `v`, using the b3-discharged rank count at
the middle-stratum rises `(frontRise, backRise)`. The FIRST peel is re-threaded through
`residJacobian_rank_eq` (derivative-exposing), so the residual-Jacobian rank of its `q` is exactly
`jacFlatL2.rank − nReg = extraCountRect` (b3 + Sylvester). Still consumes `hRne` (slice
non-vanishing) and `hInterface` (R1 degraded core) at the re-threaded `q`. -/
theorem d1ge_L2_rect_two_peel_hrank_closed
    (H : Fin (2 + 1) → ℕ) (r : ℕ) (B : Matrix (Fin (H 0)) (Fin (H (Fin.last 2))) ℝ)
    (deepest v : Params H)
    (hopt : prod H v = B) (hB : B.rank = r)
    (hDeepest : rlctAt H (dlnLoss H B) deepest
        = (nRegL2 H r : ℝ≥0∞) / 2 + ENNReal.ofReal (lambdaCore (fun s => H s - r) : ℝ))
    -- slice non-vanishing (the `hAtV` half's a.e.-nonzero input), at the FIXED rises
    (hRne : ∀ (q : (Fin (nRegL2 H r) → ℝ) × (Fin (flatDim H - nRegL2 H r) → ℝ)
                → EuclideanSpace ℝ (Fin (H 0 * H 2)))
          (t0 : Fin (flatDim H - nRegL2 H r) → ℝ),
        ContDiff ℝ 2 q → q ((0 : Fin (nRegL2 H r) → ℝ), t0) = 0 →
        rlctAt H (dlnLoss H B) v
            = rlctAtOn (fun p : (Fin (nRegL2 H r) → ℝ) × (Fin (flatDim H - nRegL2 H r) → ℝ) =>
                (∑ i, p.1 i ^ 2) + (∑ i, q p i ^ 2)) ((0 : Fin (nRegL2 H r) → ℝ), t0) →
        ∃ U ∈ 𝓝 t0, ∀ᵐ z ∂(volume.restrict U),
          (∑ i, q ((0 : Fin (nRegL2 H r) → ℝ), z) i ^ 2) ≠ 0)
    -- the R1 degraded-core interface at `M' = MprimeRect (H − r) (frontRise) (backRise)`
    (hInterface : ∀ (q : (Fin (nRegL2 H r) → ℝ) × (Fin (flatDim H - nRegL2 H r) → ℝ)
                → EuclideanSpace ℝ (Fin (H 0 * H 2)))
          (t0 : Fin (flatDim H - nRegL2 H r) → ℝ),
        ContDiff ℝ 2 q → q ((0 : Fin (nRegL2 H r) → ℝ), t0) = 0 →
        rlctAt H (dlnLoss H B) v
            = rlctAtOn (fun p : (Fin (nRegL2 H r) → ℝ) × (Fin (flatDim H - nRegL2 H r) → ℝ) =>
                (∑ i, p.1 i ^ 2) + (∑ i, q p i ^ 2)) ((0 : Fin (nRegL2 H r) → ℝ), t0) →
        ∀ (q₂ : (Fin (extraCountRect (H 0 - r) (H 2 - r) (frontRise H r v) (backRise H r v)) → ℝ)
              × (Fin ((flatDim H - nRegL2 H r)
                  - extraCountRect (H 0 - r) (H 2 - r) (frontRise H r v) (backRise H r v)) → ℝ)
              → EuclideanSpace ℝ (Fin (H 0 * H 2)))
            (t0₂ : Fin ((flatDim H - nRegL2 H r)
                - extraCountRect (H 0 - r) (H 2 - r) (frontRise H r v) (backRise H r v)) → ℝ),
          (rlctAtOn (fun t : Fin (flatDim H - nRegL2 H r) → ℝ =>
              ∑ i, q ((0 : Fin (nRegL2 H r) → ℝ), t) i ^ 2) t0
            = rlctAtOn (fun p :
                  (Fin (extraCountRect (H 0 - r) (H 2 - r) (frontRise H r v) (backRise H r v)) → ℝ)
                  × (Fin ((flatDim H - nRegL2 H r)
                      - extraCountRect (H 0 - r) (H 2 - r) (frontRise H r v) (backRise H r v)) → ℝ)
                  =>
                (∑ i, p.1 i ^ 2) + (∑ i, q₂ p i ^ 2))
                ((0 : Fin (extraCountRect (H 0 - r) (H 2 - r) (frontRise H r v)
                    (backRise H r v)) → ℝ), t0₂)) →
          (∃ U ∈ 𝓝 t0₂, ∀ᵐ z ∂(volume.restrict U),
              (∑ i, q₂ ((0 : Fin (extraCountRect (H 0 - r) (H 2 - r) (frontRise H r v)
                  (backRise H r v)) → ℝ), z) i ^ 2) ≠ 0)
            ∧ rlctAtOn (fun t : Fin ((flatDim H - nRegL2 H r)
                  - extraCountRect (H 0 - r) (H 2 - r) (frontRise H r v) (backRise H r v)) → ℝ =>
                ∑ i, q₂ ((0 : Fin (extraCountRect (H 0 - r) (H 2 - r) (frontRise H r v)
                    (backRise H r v)) → ℝ), t) i ^ 2) t0₂
              = ENNReal.ofReal
                (lambdaCore
                  (MprimeRect (fun s => H s - r) (frontRise H r v) (backRise H r v)) : ℝ)) :
    rlctAt H (dlnLoss H B) deepest ≤ rlctAt H (dlnLoss H B) v := by
  -- the honest-subtraction constraints on the FIXED rises, from `v` at a valid stratum.
  have hrankprod : (prod H v).rank = r := by rw [hopt, hB]
  obtain ⟨hr0, hr1⟩ := r_le_layer_ranks H r v hrankprod
  have hsyl := layer_ranks_sylvester H r v hrankprod
  have hb0H0 : (layer0 H v).rank ≤ H 0 := Matrix.rank_le_height _
  have hb1H2 : (layer1 H v).rank ≤ H 2 := Matrix.rank_le_width _
  have ha : frontRise H r v ≤ H 0 - r := by rw [frontRise]; omega
  have hab : frontRise H r v + backRise H r v ≤ H 1 - r := by rw [frontRise, backRise]; omega
  have hb : backRise H r v ≤ H 2 - r := by rw [backRise]; omega
  -- FIRST peel: the invertible `nReg`-minor + the DERIVATIVE-exposing residual `q` (its
  -- residual-Jacobian rank is exactly `jacFlatL2.rank − nReg` = `extraCountRect`, by b3).
  obtain ⟨er, ec, her, hec, hminor⟩ := exists_jacFlatL2_minor H r v B hopt hB
  obtain ⟨q, t0, hqCD, hq0, hchart, hrankeq⟩ :=
    residJacobian_rank_eq (m := nRegL2 H r) (er := er) (ec := ec) hopt hB her hec hminor
  -- the slice residual `h = q (0,·)`, `C²`, vanishing at `t0`.
  set h : (Fin (flatDim H - nRegL2 H r) → ℝ) → EuclideanSpace ℝ (Fin (H 0 * H 2)) :=
    fun t => q ((0 : Fin (nRegL2 H r) → ℝ), t) with hhdef
  have hhCD : ContDiff ℝ 2 h := contDiff_slice_of_contDiff q hqCD
  have hh0 : h t0 = 0 := hq0
  -- `hrank'`: `extraCountRect ≤ rank(jacResid h t0)`, from the rank identity + b3 arithmetic.
  have hrank' : extraCountRect (H 0 - r) (H 2 - r) (frontRise H r v) (backRise H r v)
      ≤ (jacResid h t0).rank := by
    rw [hhdef, hrankeq, ← jacFlatL2_rank_sub_nReg_eq_extraCountRect H r v B hopt hB]
  -- the per-`v` geometric inputs at THIS concrete first-peel `q`.
  have hRne' := hRne q t0 hqCD hq0 hchart
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
    hCoreRect_of_slice_data (fun s => H s - r) (frontRise H r v) (backRise H r v)
      ha hab hb h t0 hhCD hh0 hrank' hInterface'
  -- close through the arithmetic combine.
  exact deepest_le_of_optimal_via_L2_ge (B := B) H r
    (rlctAt H (dlnLoss H B) deepest) (rlctAt H (dlnLoss H B) v) (nRegL2 H r)
    (ENNReal.ofReal (lambdaCore (fun s => H s - r) : ℝ))
    (rlctAtOn (fun t : Fin (flatDim H - nRegL2 H r) → ℝ =>
      ∑ i, q ((0 : Fin (nRegL2 H r) → ℝ), t) i ^ 2) t0)
    hDeepest hAtV hCore

end DLNFibre.DLN.RLCT
