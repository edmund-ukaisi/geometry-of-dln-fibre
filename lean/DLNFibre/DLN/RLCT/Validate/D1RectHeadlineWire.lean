import DLNFibre.DLN.RLCT.Validate.D1RectTwoPeelClosed
import DLNFibre.DLN.RLCT.Validate.DeepestFrontGauge

/-!
# `D1RectHeadlineWire` — the ∀-`v` LEAF-2 reduction (hrank₂ closed; hRne / hInterface residual)

Wires the b3-discharged two-peel producer (`d1ge_L2_rect_two_peel_hrank_closed`) into the headline
LEAF-2 shape

    ∀ v ∈ optimalSet H B, rlctAt (deepestPoint …) ≤ rlctAt v.

The deepest-side value `hDeepest` is v-INDEPENDENT (the same `deepestPoint`), supplied by
`deepest_regular_core_normal_form_L2_front` (banked #44). With `hrank₂` DISCHARGED by b3, the
remaining per-`v` debt is exactly the TWO analytic gates `hRne` (slice non-vanishing) and
`hInterface` (R1 degraded-core identification of the rectangular second-peel residual), stated at
the concrete first-peel `q` — NOT core-geometry, and each a separate analytic build.

Scope L = 2. This makes the LEAF-2 residual precise: the only open content is `hRne`/`hInterface`.
-/

open MeasureTheory
open scoped ENNReal Topology
namespace DLNFibre.DLN.RLCT

variable {L : ℕ}

/-- **The LEAF-2 ∀-`v` reduction with `hrank₂` closed.** Given the banked deepest-side value
`hDeepest` (at the fixed `deepestPoint`) and the two per-`v` analytic gates `hRne` (slice
non-vanishing) and `hInterface` (R1 degraded core, at the true middle-stratum rises
`(frontRise, backRise)`), the headline LEAF-2 goal holds. `hrank₂` is DISCHARGED internally by b3
(via `d1ge_L2_rect_two_peel_hrank_closed`). -/
theorem hD1ge_L2_rect_of_gates
    (H : Fin (2 + 1) → ℕ) (r : ℕ) (B : Matrix (Fin (H 0)) (Fin (H (Fin.last 2))) ℝ)
    (hB : B.rank = r) (deepest : Params H)
    (hDeepest : rlctAt H (dlnLoss H B) deepest
        = (nRegL2 H r : ℝ≥0∞) / 2 + ENNReal.ofReal (lambdaCore (fun s => H s - r) : ℝ))
    (hRne : ∀ (v : Params H), prod H v = B →
      ∀ (q : (Fin (nRegL2 H r) → ℝ) × (Fin (flatDim H - nRegL2 H r) → ℝ)
            → EuclideanSpace ℝ (Fin (H 0 * H 2)))
        (t0 : Fin (flatDim H - nRegL2 H r) → ℝ),
        ContDiff ℝ 2 q → q ((0 : Fin (nRegL2 H r) → ℝ), t0) = 0 →
        rlctAt H (dlnLoss H B) v
            = rlctAtOn (fun p : (Fin (nRegL2 H r) → ℝ) × (Fin (flatDim H - nRegL2 H r) → ℝ) =>
                (∑ i, p.1 i ^ 2) + (∑ i, q p i ^ 2)) ((0 : Fin (nRegL2 H r) → ℝ), t0) →
        ∃ U ∈ 𝓝 t0, ∀ᵐ z ∂(volume.restrict U),
          (∑ i, q ((0 : Fin (nRegL2 H r) → ℝ), z) i ^ 2) ≠ 0)
    (hInterface : ∀ (v : Params H), prod H v = B →
      ∀ (q : (Fin (nRegL2 H r) → ℝ) × (Fin (flatDim H - nRegL2 H r) → ℝ)
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
    ∀ v ∈ optimalSet H B, rlctAt H (dlnLoss H B) deepest ≤ rlctAt H (dlnLoss H B) v := by
  intro v hv
  have hopt : prod H v = B := hv
  exact d1ge_L2_rect_two_peel_hrank_closed H r B deepest v hopt hB hDeepest
    (hRne v hopt) (hInterface v hopt)

end DLNFibre.DLN.RLCT
