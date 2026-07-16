import DLNFibre.DLN.RLCT.Validate.RouteMSJEdgeFubini

set_option linter.style.longLine false

/-!
# `RouteMSJEdgeAssembly` — the outerDom product split (connective tissue, outer side)

Thread `genm-tideD` (edge dispatch arm, b=1 a<u brick). The **outer product split** peeling the front pivot
pair `(P, B₁₂)` off the corank left-block `C` in the `outerDom` integral, so the per-slice corank charge
(`coupledInner_slice_le`, `RouteMSJEdgeFubini`) applies per fixed `(P, B₁₂)`.

`outerDom u a b T = OuterPB ×ˢ Ccube` (the `(P, B₁₂)` box ∩ `{IsUnit P}` times the `C` box), and the
`SJOuter` measure is the product measure, so Tonelli (`setLIntegral_prod`) factors the `x`-integral into
`∫_{pb ∈ OuterPB} ∫_{C ∈ Ccube}`.
-/

namespace DLNFibre.DLN.RLCT

open Matrix MeasureTheory
open scoped BigOperators ENNReal

/-- **The `(P, B₁₂)` box ∩ `{IsUnit P}`** — the front pivot pair factor of `outerDom`. -/
def outerPB (u b : ℕ) (T : ℝ) : Set ((Fin u → Fin u → ℝ) × (Fin u → Fin b → ℝ)) :=
  {pb | (∀ i j, pb.1 i j ∈ Set.Icc (-T) T) ∧ (∀ i j, pb.2 i j ∈ Set.Icc (-T) T)
    ∧ IsUnit (Matrix.of pb.1)}

/-- **`outerDom` factors as `outerPB ×ˢ (C-box)`.** The three box conditions + `IsUnit P` split into the
`(P, B₁₂)`-conditions (on `x.1`) and the `C`-box (on `x.2`). -/
theorem outerDom_eq_prod (u a b : ℕ) (T : ℝ) :
    outerDom u a b T
      = outerPB u b T ×ˢ {C : Fin a → Fin u → ℝ | ∀ i j, C i j ∈ Set.Icc (-T) T} := by
  ext x
  simp only [outerDom, outerPB, Set.mem_setOf_eq, Set.mem_prod]
  tauto

/-- **The outerDom product split (Tonelli).** For an a.e.-measurable `F : SJOuter u a b → ℝ≥0∞`, the
`outerDom` integral factors into the front pivot pair `(P, B₁₂) ∈ outerPB` and the corank left-block
`C ∈ [−T,T]^{a×u}`: `∫_{x ∈ outerDom} F x = ∫_{pb ∈ outerPB} ∫_{C ∈ Cbox} F (pb, C)`. Via
`outerDom_eq_prod` + the product measure (`Measure.volume_eq_prod`) + `setLIntegral_prod`. This peels
`(P, B₁₂)` off so the per-slice corank charge (`coupledInner_slice_le`) applies per fixed pivot pair. -/
theorem outerDom_lintegral_prod {u a b : ℕ} (T : ℝ) (F : SJOuter u a b → ℝ≥0∞)
    (hF : AEMeasurable F (volume.restrict (outerDom u a b T))) :
    (∫⁻ x in outerDom u a b T, F x)
      = ∫⁻ pb in outerPB u b T,
          ∫⁻ C in {C : Fin a → Fin u → ℝ | ∀ i j, C i j ∈ Set.Icc (-T) T}, F (pb, C) := by
  rw [outerDom_eq_prod u a b T] at hF ⊢
  rw [Measure.volume_eq_prod ((Fin u → Fin u → ℝ) × (Fin u → Fin b → ℝ)) (Fin a → Fin u → ℝ),
    setLIntegral_prod F hF]

end DLNFibre.DLN.RLCT
