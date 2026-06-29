import DLNFibre.DLN.RLCT.Validate.RouteMSchurDepth2
import DLNFibre.DLN.RLCT.Foundations.S1G5Charts

/-!
# `DLNFibre.DLN.RLCT.Validate.RouteMSchurGenCover` — the generic radial-Δ `r²`-chart cover

The arbitrary-corank generalisation of the corank-3 outer radial-Δ cover
(`RouteMSchurCorank3.matToFlat3` / `flatBox3` / `matBox3_outer_flat` / `gFlat3_cover_sum`), with
`Fin 3` → `Fin r`, `Fin 9` → `Fin (r*r)`. The flatten + measure-preservation + the box-preimage +
the outer reindex + the `recStep` cover-to-sum are all `r`-agnostic (the corank-3 proofs only used
`finProdFinEquiv`, `piCurry`, `arrowCongr'`, `recStep`/`argmaxCellOn` — all generic). This is the
boilerplate the per-corank recStep assembly stands on; it carries NO threshold/analytic content.
-/

namespace DLNFibre.DLN.RLCT

open MeasureTheory Set
open scoped ENNReal BigOperators

/-- The generic flatten `matToFlatGen r : (Fin r → Fin r → ℝ) ≃ᵐ (Fin (r*r) → ℝ)` (uncurry + the
`Fin r × Fin r ≃ Fin (r*r)` index reindex `finProdFinEquiv`). The `r`-generic `matToFlat3`. -/
noncomputable def matToFlatGen (r : ℕ) : (Fin r → Fin r → ℝ) ≃ᵐ (Fin (r * r) → ℝ) :=
  (MeasurableEquiv.piCurry (fun (_ : Fin r) (_ : Fin r) => ℝ)).symm.trans
    (MeasurableEquiv.arrowCongr'
      ((Equiv.sigmaEquivProd (Fin r) (Fin r)).trans finProdFinEquiv) (MeasurableEquiv.refl ℝ))

theorem measurePreserving_matToFlatGen (r : ℕ) :
    MeasurePreserving (matToFlatGen r) (volume : Measure (Fin r → Fin r → ℝ))
      (volume : Measure (Fin (r * r) → ℝ)) := by
  unfold matToFlatGen
  refine MeasurePreserving.trans ?_ (volume_preserving_arrowCongr'
    ((Equiv.sigmaEquivProd (Fin r) (Fin r)).trans finProdFinEquiv)
    (MeasurableEquiv.refl ℝ) (MeasurePreserving.id _))
  exact (measurePreserving_piCurry (fun (_ : Fin r) (_ : Fin r) => ℝ)
    (fun _ _ => (volume : Measure ℝ))).symm
    (MeasurableEquiv.piCurry (fun (_ : Fin r) (_ : Fin r) => ℝ))

/-- The flattened `Δ`-box on the `Fin (r*r)` carrier: `[−T,T]^{r²}`. -/
def flatBoxGen (r : ℕ) (T : ℝ) : Set (Fin (r * r) → ℝ) := {y | ∀ i, y i ∈ Set.Icc (-T) T}

theorem flatBoxGen_measurableSet (r : ℕ) (T : ℝ) : MeasurableSet (flatBoxGen r T) := by
  rw [flatBoxGen, Set.setOf_forall]
  exact MeasurableSet.iInter (fun i => (measurable_pi_apply i) measurableSet_Icc)

/-- `matBox r r T = matToFlatGen r ⁻¹' flatBoxGen r T`. -/
theorem matBoxGen_flatBox_preimage (r : ℕ) (T : ℝ) :
    matBox r r T = matToFlatGen r ⁻¹' flatBoxGen r T := by
  ext Δ
  simp only [matBox, flatBoxGen, Set.mem_setOf_eq, Set.mem_preimage]
  set e : (Σ _ : Fin r, Fin r) ≃ Fin (r * r) :=
    (Equiv.sigmaEquivProd (Fin r) (Fin r)).trans finProdFinEquiv with he
  have hcoord : ∀ i : Fin (r * r), (matToFlatGen r Δ) i = Δ (e.symm i).1 (e.symm i).2 := fun i => rfl
  constructor
  · intro h i; rw [hcoord i]; exact h (e.symm i).1 (e.symm i).2
  · intro h k j
    have := h (e ⟨k, j⟩)
    rw [hcoord (e ⟨k, j⟩), Equiv.symm_apply_apply] at this
    exact this

/-- The flat-`Δ` cover integrand: `gFlatGen r p c' T y = ∫_{S∈box r p} frobSq(rmatMul (flat.symm y) S)^{−c'}`. -/
noncomputable def gFlatGen (r p : ℕ) (c' : ℝ) (T : ℝ) (y : Fin (r * r) → ℝ) : ℝ≥0∞ :=
  ∫⁻ S in matBox r p T,
    ENNReal.ofReal ((frobSq (rmatMul ((matToFlatGen r).symm y) S)) ^ (-c'))

/-- The `Δ`-outer integral reindexes to the flat `gFlatGen` integral over `flatBoxGen`. -/
theorem matBoxGen_outer_flat (r p : ℕ) (c' : ℝ) (T : ℝ) :
    (∫⁻ Δ in matBox r r T, ∫⁻ S in matBox r p T,
        ENNReal.ofReal ((frobSq (rmatMul Δ S)) ^ (-c')))
      = ∫⁻ y in flatBoxGen r T, gFlatGen r p c' T y := by
  have hmp := measurePreserving_matToFlatGen r
  have hcomp := hmp.setLIntegral_comp_preimage_emb (matToFlatGen r).measurableEmbedding
    (gFlatGen r p c' T) (flatBoxGen r T)
  rw [matBoxGen_flatBox_preimage, ← hcomp]
  refine setLIntegral_congr_fun ((matToFlatGen r).measurable (flatBoxGen_measurableSet r T))
    (fun Δ _ => ?_)
  rw [gFlatGen, MeasurableEquiv.symm_apply_apply]

/-- The cover-to-sum on the `Fin (r*r)` flat carrier (`recStep`, the `r²`-entry argmax cover). -/
theorem gFlatGen_cover_sum (r p : ℕ) (hr : 0 < r * r) (c' : ℝ) (T : ℝ) :
    (∫⁻ y in flatBoxGen r T, gFlatGen r p c' T y)
      = ∑ q ∈ (Finset.univ : Finset (Fin (r * r))),
          ∫⁻ y in chartDomOn (Finset.univ : Finset (Fin (r * r))) q \ pivotZeroOn q,
            ENNReal.ofReal |(pivotBlowupOnDeriv (Finset.univ : Finset (Fin (r * r))) q y).det|
              * (flatBoxGen r T).indicator (gFlatGen r p c' T) (pivotBlowupOn
                  (Finset.univ : Finset (Fin (r * r))) q y) := by
  exact recStep (Finset.univ : Finset (Fin (r * r))) ⟨0, hr⟩ (Finset.mem_univ _)
    (flatBoxGen r T) (flatBoxGen_measurableSet r T) (gFlatGen r p c' T)

end DLNFibre.DLN.RLCT
