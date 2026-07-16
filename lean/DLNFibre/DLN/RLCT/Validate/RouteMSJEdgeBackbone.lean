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

/-- **The inner integral is a.e.-measurable on `outerDom` (the peel gate).** The inner
`Γ`-integral of the freed-loss power, as a function of the front `x`, is `AEMeasurable` on `outerDom` —
the hypothesis `outerDom_lintegral_prod` needs to peel `(P, B₁₂)` off `C`. Route (à la
`chartInner_schurShearFree_eq`'s `hF'meas`): the schur-shear CoV (`shearBox_lintegral_eq`) rewrites the
`x`-dependent-domain inner to the FIXED-domain `∫_D genBox`, which on `{IsUnit P}` equals the INVERSE-FREE
continuous form (`freedSchurLoss_shear_isUnit_eq`); that continuous integrand's parametrized lintegral is
measurable (`Measurable.lintegral_prod_right'`), and it agrees with the inner a.e. on `outerDom`. Sidesteps
matrix-inverse measurability. -/
theorem coupledInner_aemeasurable {u a b n : ℕ} (Q : Matrix (Fin u ⊕ Fin b) (Fin n) ℝ) (c' T : ℝ)
    (hc0 : 0 ≤ c') :
    AEMeasurable (fun x : SJOuter u a b =>
        ∫⁻ Γ in {Γ : Fin a → Fin b → ℝ | Γ + schurShift x ∈ genBox (Fin a) (Fin b) T},
          ENNReal.ofReal ((freedSchurLoss x Γ Q) ^ (-c')))
      (volume.restrict (outerDom u a b T)) := by
  -- the four block projections are continuous (`Matrix.of ∘ projection`)
  have cP : Continuous (fun p : SJOuter u a b × (Fin a → Fin b → ℝ) => Matrix.of p.1.1.1) :=
    continuous_matrix (fun i j => (continuous_apply j).comp ((continuous_apply i).comp
      (continuous_fst.comp (continuous_fst.comp continuous_fst))))
  have cB : Continuous (fun p : SJOuter u a b × (Fin a → Fin b → ℝ) => Matrix.of p.1.1.2) :=
    continuous_matrix (fun i j => (continuous_apply j).comp ((continuous_apply i).comp
      (continuous_snd.comp (continuous_fst.comp continuous_fst))))
  have cC : Continuous (fun p : SJOuter u a b × (Fin a → Fin b → ℝ) => Matrix.of p.1.2) :=
    continuous_matrix (fun i j => (continuous_apply j).comp ((continuous_apply i).comp
      (continuous_snd.comp continuous_fst)))
  have cD : Continuous (fun p : SJOuter u a b × (Fin a → Fin b → ℝ) => Matrix.of p.2) :=
    continuous_matrix (fun i j => (continuous_apply j).comp ((continuous_apply i).comp continuous_snd))
  have m1 : Continuous (fun p : SJOuter u a b × (Fin a → Fin b → ℝ) =>
      Matrix.of p.1.1.1 * Q.submatrix Sum.inl id + Matrix.of p.1.1.2 * Q.submatrix Sum.inr id) :=
    (cP.matrix_mul continuous_const).add (cB.matrix_mul continuous_const)
  have m2 : Continuous (fun p : SJOuter u a b × (Fin a → Fin b → ℝ) =>
      Matrix.of p.1.2 * Q.submatrix Sum.inl id + Matrix.of p.2 * Q.submatrix Sum.inr id) :=
    (cC.matrix_mul continuous_const).add (cD.matrix_mul continuous_const)
  -- the inverse-free base is continuous (jointly in (x, D))
  have hcont : Continuous (fun p : SJOuter u a b × (Fin a → Fin b → ℝ) =>
      frobSq (Matrix.of p.1.1.1 * Q.submatrix Sum.inl id + Matrix.of p.1.1.2 * Q.submatrix Sum.inr id)
        + frobSq (Matrix.of p.1.2 * Q.submatrix Sum.inl id + Matrix.of p.2 * Q.submatrix Sum.inr id)) := by
    unfold frobSq
    exact (continuous_finset_sum _ (fun i _ => continuous_finset_sum _
        (fun j _ => (m1.matrix_elem i j).pow 2))).add
      (continuous_finset_sum _ (fun i _ => continuous_finset_sum _
        (fun j _ => (m2.matrix_elem i j).pow 2)))
  -- base^{−c'} = (base^{c'})⁻¹ (base ≥ 0) — measurable without needing base ≠ 0
  have hgmeas : Measurable (fun p : SJOuter u a b × (Fin a → Fin b → ℝ) =>
      ENNReal.ofReal ((frobSq (Matrix.of p.1.1.1 * Q.submatrix Sum.inl id
            + Matrix.of p.1.1.2 * Q.submatrix Sum.inr id)
          + frobSq (Matrix.of p.1.2 * Q.submatrix Sum.inl id
            + Matrix.of p.2 * Q.submatrix Sum.inr id)) ^ (-c'))) := by
    apply ENNReal.measurable_ofReal.comp
    have heq : (fun p : SJOuter u a b × (Fin a → Fin b → ℝ) =>
          (frobSq (Matrix.of p.1.1.1 * Q.submatrix Sum.inl id
              + Matrix.of p.1.1.2 * Q.submatrix Sum.inr id)
            + frobSq (Matrix.of p.1.2 * Q.submatrix Sum.inl id
              + Matrix.of p.2 * Q.submatrix Sum.inr id)) ^ (-c'))
        = fun p => ((frobSq (Matrix.of p.1.1.1 * Q.submatrix Sum.inl id
              + Matrix.of p.1.1.2 * Q.submatrix Sum.inr id)
            + frobSq (Matrix.of p.1.2 * Q.submatrix Sum.inl id
              + Matrix.of p.2 * Q.submatrix Sum.inr id)) ^ c')⁻¹ := by
      funext p; exact Real.rpow_neg (add_nonneg (frobSq_nonneg _) (frobSq_nonneg _)) c'
    rw [heq]
    exact ((Real.continuous_rpow_const hc0).comp hcont).measurable.inv
  -- the continuous-form parametrized lintegral is measurable
  have hFcont : Measurable (fun x : SJOuter u a b =>
      ∫⁻ D in genBox (Fin a) (Fin b) T,
        ENNReal.ofReal ((frobSq (Matrix.of x.1.1 * Q.submatrix Sum.inl id
              + Matrix.of x.1.2 * Q.submatrix Sum.inr id)
            + frobSq (Matrix.of x.2 * Q.submatrix Sum.inl id
              + Matrix.of D * Q.submatrix Sum.inr id)) ^ (-c'))) :=
    hgmeas.lintegral_prod_right' (ν := volume.restrict (genBox (Fin a) (Fin b) T))
  refine AEMeasurable.congr hFcont.aemeasurable ?_
  refine (ae_restrict_iff' (measurableSet_outerDom u a b T)).mpr (ae_of_all _ (fun x hx => ?_))
  -- on outerDom (IsUnit P), the inner equals the continuous-form lintegral
  dsimp only
  rw [shearBox_lintegral_eq x Q c' T]
  exact lintegral_congr (fun D => by rw [freedSchurLoss_shear_isUnit_eq x D Q hx.2.2.2])

end DLNFibre.DLN.RLCT
