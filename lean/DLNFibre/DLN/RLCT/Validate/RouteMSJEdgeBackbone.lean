import DLNFibre.DLN.RLCT.Validate.RouteMSJEdgeFubini

set_option linter.style.longLine false

/-!
# `RouteMSJEdgeBackbone` — the edge wrapper (half-A: `∫_box coupledBox ≤ EDGEREDUCED`)

Thread `genm-tideD` (edge dispatch arm, b=1 a<u brick). The **edge wrapper** on top of the leaf
(`coupledInner_slice_le`, `RouteMSJEdgeFubini`) — the reduction `∫_box coupledBox ≤ EDGEREDUCED`, built
from the banked primitives + the frame a.e.-positivity as hypotheses. `hFrontReduce`-independent (it defines
EDGEREDUCED, which satred's edge descent then targets).

## The `P⁻¹`-free continuous form (measurability enabler)

The schur-shear (`freedSchurLoss_shear_eq`) already removed `P⁻¹` from the corank term. The remaining pivot
term `frobSq(P·Q̃ₚ)` also loses `P⁻¹` ON `{IsUnit P}`: `P·Q̃ₚ = P·Q_inl + P·P⁻¹·B₁₂·Q_inr = P·Q_inl +
B₁₂·Q_inr` (`P·P⁻¹ = 1`). So the sheared freed loss equals an INVERSE-FREE, jointly-continuous function of
`(x, D)` on `{IsUnit P}` — the a.e.-measurability route (à la `chartInner_schurShearFree_eq`'s `hF'meas`),
sidestepping matrix-inverse measurability entirely.
-/

namespace DLNFibre.DLN.RLCT

open Matrix MeasureTheory
open scoped BigOperators ENNReal

/-- **The `P⁻¹`-free continuous form of the sheared freed loss (on `{IsUnit P}`).** For an invertible pivot
`P = of x.1.1`, the schur-sheared freed loss is inverse-free:

    freedSchurLoss x (D − schurShift x) Q
      = frobSq(P·Q_inl + B₁₂·Q_inr) + frobSq(C·Q_inl + D·Q_inr)

(`Q_inl = Q.submatrix Sum.inl id`, `Q_inr = Q.submatrix Sum.inr id`, `B₁₂ = of x.1.2`, `C = of x.2`).
Composes `freedSchurLoss_shear_eq` (corank term already `P⁻¹`-free) with `P·Q̃ₚ = P·Q_inl + B₁₂·Q_inr`
(`P·P⁻¹ = 1` on `IsUnit P`, `mul_nonsing_inv`). Both frobSq arguments are now polynomial in `(x, D)` —
continuous, hence measurable without the matrix-inverse. -/
theorem freedSchurLoss_shear_isUnit_eq {u a b n : ℕ} (x : SJOuter u a b) (D : Fin a → Fin b → ℝ)
    (Q : Matrix (Fin u ⊕ Fin b) (Fin n) ℝ) (hP : IsUnit (Matrix.of x.1.1)) :
    freedSchurLoss x (D - schurShift x) Q
      = frobSq (Matrix.of x.1.1 * Q.submatrix Sum.inl id + Matrix.of x.1.2 * Q.submatrix Sum.inr id)
        + frobSq (Matrix.of x.2 * Q.submatrix Sum.inl id + Matrix.of D * Q.submatrix Sum.inr id) := by
  rw [freedSchurLoss_shear_eq]
  congr 1
  congr 1
  have hPinv : Matrix.of x.1.1 * (Matrix.of x.1.1)⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hP)
  rw [Matrix.mul_add]
  congr 1
  rw [← Matrix.mul_assoc (Matrix.of x.1.1) ((Matrix.of x.1.1)⁻¹ * Matrix.of x.1.2)
      (Q.submatrix Sum.inr id),
    ← Matrix.mul_assoc (Matrix.of x.1.1) (Matrix.of x.1.1)⁻¹ (Matrix.of x.1.2),
    hPinv, Matrix.one_mul]

end DLNFibre.DLN.RLCT
