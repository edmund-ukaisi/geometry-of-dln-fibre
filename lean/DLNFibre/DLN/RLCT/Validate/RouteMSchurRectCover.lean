import DLNFibre.DLN.RLCT.Validate.RouteMSchurRectN2b
import DLNFibre.DLN.RLCT.Foundations.S1G5Charts

/-!
# `DLNFibre.DLN.RLCT.Validate.RouteMSchurRectCover` — the RECTANGULAR radial-Δ `mn`-chart cover

The asymmetric (`Δ : Fin m → Fin n`) generalisation of the square radial-Δ cover
(`RouteMSchurGenCover.matToFlatGen` / `flatBoxGen` / `matBoxGen_outer_flat` / `gFlatGen_cover_sum`,
`Fin r × Fin r → Fin (r*r)`), with the flatten now over the asymmetric `Fin m × Fin n → Fin (m*n)`.
The flatten + measure-preservation + box-preimage + the `recStep` cover-to-sum are all index-set generic
(`finProdFinEquiv`, `piCurry`, `arrowCongr'`, and the `{N : ℕ}`-generic `pivotBlowupOn` / `recStep` over
`Finset (Fin N)`) — this file just instantiates them at `N = m*n`. NO threshold/analytic content.

The per-chart radial Jacobian is `|y_pivot|^{mn−1}` (`pivotBlowupOnDeriv_det`, `N = m*n`), so the a-axis
divisor exponent is `mn − 1 − 2c'` and the radial cap is `c' < mn/2` (vs the square `r² − 1 − 2c'`,
`c' < r²/2`).
-/

namespace DLNFibre.DLN.RLCT

open MeasureTheory Set
open scoped ENNReal BigOperators

/-- The rectangular flatten `matToFlat m n : (Fin m → Fin n → ℝ) ≃ᵐ (Fin (m*n) → ℝ)` (uncurry + the
`Fin m × Fin n ≃ Fin (m*n)` index reindex `finProdFinEquiv`). The asymmetric `matToFlatGen`. -/
noncomputable def matToFlatRect (m n : ℕ) : (Fin m → Fin n → ℝ) ≃ᵐ (Fin (m * n) → ℝ) :=
  (MeasurableEquiv.piCurry (fun (_ : Fin m) (_ : Fin n) => ℝ)).symm.trans
    (MeasurableEquiv.arrowCongr'
      ((Equiv.sigmaEquivProd (Fin m) (Fin n)).trans finProdFinEquiv) (MeasurableEquiv.refl ℝ))

theorem measurePreserving_matToFlatRect (m n : ℕ) :
    MeasurePreserving (matToFlatRect m n) (volume : Measure (Fin m → Fin n → ℝ))
      (volume : Measure (Fin (m * n) → ℝ)) := by
  unfold matToFlatRect
  refine MeasurePreserving.trans ?_ (volume_preserving_arrowCongr'
    ((Equiv.sigmaEquivProd (Fin m) (Fin n)).trans finProdFinEquiv)
    (MeasurableEquiv.refl ℝ) (MeasurePreserving.id _))
  exact (measurePreserving_piCurry (fun (_ : Fin m) (_ : Fin n) => ℝ)
    (fun _ _ => (volume : Measure ℝ))).symm
    (MeasurableEquiv.piCurry (fun (_ : Fin m) (_ : Fin n) => ℝ))

/-- The flattened `Δ`-box on the `Fin (m*n)` carrier: `[−T,T]^{mn}`. -/
def flatBoxRect (m n : ℕ) (T : ℝ) : Set (Fin (m * n) → ℝ) := {y | ∀ i, y i ∈ Set.Icc (-T) T}

theorem flatBoxRect_measurableSet (m n : ℕ) (T : ℝ) : MeasurableSet (flatBoxRect m n T) := by
  rw [flatBoxRect, Set.setOf_forall]
  exact MeasurableSet.iInter (fun i => (measurable_pi_apply i) measurableSet_Icc)

/-- `matBox m n T = matToFlatRect m n ⁻¹' flatBoxRect m n T`. -/
theorem matBoxRect_flatBox_preimage (m n : ℕ) (T : ℝ) :
    matBox m n T = matToFlatRect m n ⁻¹' flatBoxRect m n T := by
  ext Δ
  simp only [matBox, flatBoxRect, Set.mem_setOf_eq, Set.mem_preimage]
  set e : (Σ _ : Fin m, Fin n) ≃ Fin (m * n) :=
    (Equiv.sigmaEquivProd (Fin m) (Fin n)).trans finProdFinEquiv with he
  have hcoord : ∀ i : Fin (m * n), (matToFlatRect m n Δ) i = Δ (e.symm i).1 (e.symm i).2 := fun i => rfl
  constructor
  · intro h i; rw [hcoord i]; exact h (e.symm i).1 (e.symm i).2
  · intro h k j
    have := h (e ⟨k, j⟩)
    rw [hcoord (e ⟨k, j⟩), Equiv.symm_apply_apply] at this
    exact this

/-- The flat-`Δ` cover integrand: `gFlatRect m n p c' T y = ∫_{S∈box n p} frobSq(rmatMul (flat.symm y) S)^{−c'}`
(`S` now `n × p`, the contracted dim `n` is `Δ`'s column count). -/
noncomputable def gFlatRect (m n p : ℕ) (c' : ℝ) (T : ℝ) (y : Fin (m * n) → ℝ) : ℝ≥0∞ :=
  ∫⁻ S in matBox n p T,
    ENNReal.ofReal ((frobSq (rmatMul ((matToFlatRect m n).symm y) S)) ^ (-c'))

/-- The `Δ`-outer integral reindexes to the flat `gFlatRect` integral over `flatBoxRect`. -/
theorem matBoxRect_outer_flat (m n p : ℕ) (c' : ℝ) (T : ℝ) :
    (∫⁻ Δ in matBox m n T, ∫⁻ S in matBox n p T,
        ENNReal.ofReal ((frobSq (rmatMul Δ S)) ^ (-c')))
      = ∫⁻ y in flatBoxRect m n T, gFlatRect m n p c' T y := by
  have hmp := measurePreserving_matToFlatRect m n
  have hcomp := hmp.setLIntegral_comp_preimage_emb (matToFlatRect m n).measurableEmbedding
    (gFlatRect m n p c' T) (flatBoxRect m n T)
  rw [matBoxRect_flatBox_preimage, ← hcomp]
  refine setLIntegral_congr_fun ((matToFlatRect m n).measurable (flatBoxRect_measurableSet m n T))
    (fun Δ _ => ?_)
  rw [gFlatRect, MeasurableEquiv.symm_apply_apply]

/-- The cover-to-sum on the `Fin (m*n)` flat carrier (`recStep`, the `mn`-entry argmax cover). -/
theorem gFlatRect_cover_sum (m n p : ℕ) (hmn : 0 < m * n) (c' : ℝ) (T : ℝ) :
    (∫⁻ y in flatBoxRect m n T, gFlatRect m n p c' T y)
      = ∑ q ∈ (Finset.univ : Finset (Fin (m * n))),
          ∫⁻ y in chartDomOn (Finset.univ : Finset (Fin (m * n))) q \ pivotZeroOn q,
            ENNReal.ofReal |(pivotBlowupOnDeriv (Finset.univ : Finset (Fin (m * n))) q y).det|
              * (flatBoxRect m n T).indicator (gFlatRect m n p c' T) (pivotBlowupOn
                  (Finset.univ : Finset (Fin (m * n))) q y) := by
  exact recStep (Finset.univ : Finset (Fin (m * n))) ⟨0, hmn⟩ (Finset.mem_univ _)
    (flatBoxRect m n T) (flatBoxRect_measurableSet m n T) (gFlatRect m n p c' T)

end DLNFibre.DLN.RLCT
