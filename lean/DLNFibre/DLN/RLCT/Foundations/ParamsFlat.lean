import DLNFibre.DLN.RLCT.Foundations.Rlct
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.MeasurableSpace.Embedding

/-!
# `DLNFibre.DLN.RLCT.Foundations.ParamsFlat` — flattening `Params H` to `ℝ^N` (measure infra)

`paramsEquivFlat : Params H ≃ᵐ (Fin (flatDim H) → ℝ)`, **measure-preserving** for the product
Lebesgue measure (`measurePreserving_paramsEquivFlat`) — the single reusable artifact the `(1,1,1)`
bridge, the S1.1 transport use-site, and the general R1 all transport through (state a measure
fact on `Fin N → ℝ`, pull back via `MeasurePreserving.integrableOn_comp_preimage`; the
`Matrix`-fiber wall is paid once here and never re-touched downstream).

## The assembly (Route A++, pp's thread-11 research)
`Params H = ∀ s, Matrix (Fin aₛ) (Fin bₛ) ℝ` is a 3-level nested `Pi` over `(s, i, j)`. Flatten by
two `MeasurableEquiv.piCurry` steps (over `J2 = Σ (Σ s, Fin aₛ), Fin bₛ`) then re-index to `Fin N`
by `arrowCongr' (Fintype.equivFin J2) (refl ℝ)`. The measures thread by **`rfl`** at every join — in
particular `Params`'s `volume` is *definitionally* the nested `Measure.pi` (the `Matrix` fiber's
measure is the `Pi` measure on its function space), so no shape-bridging lemma is needed; the
`MeasurableEquiv.trans`/`MeasurePreserving.symm` composition unifies them automatically.

The one Mathlib gap was `measurePreserving_piCurry` — the MP statement for the existing
`MeasurableEquiv.piCurry` (a `Σ`-indexed `Measure.pi` equals the nested `Measure.pi`-of-`Measure.pi`
under currying). Clean proof via the symmetric map (`Sigma.uncurry`): its preimage of a `Σ`-box is a
nested box, so `Measure.pi_eq` + `pi_pi` + `Fintype.prod_sigma` close it, then `.symm`.
The same lemma covers **both** piCurry steps (per-layer uncurry and across-layers flatten).
-/

open MeasureTheory MeasureTheory.Measure Set
namespace DLNFibre.DLN.RLCT

variable {L : ℕ}

/-- **The one Mathlib gap.** Currying a `Σ`-indexed product measure is measure-preserving: `piCurry`
sends `Measure.pi (over Σ i, κ i)` to the nested `Measure.pi`-of-`Measure.pi`. Proof via the
`Sigma.uncurry`: its preimage of a `Σ`-box `univ.pi s` is the nested box `univ.pi (fun i => univ.pi
(fun j => s ⟨i,j⟩))`, so `pi_pi` + `Fintype.prod_sigma` compute both sides, then `.symm`. -/
theorem measurePreserving_piCurry {ι : Type*} [Fintype ι] {κ : ι → Type*} [∀ i, Fintype (κ i)]
    (X : (i : ι) → κ i → Type*) [∀ i j, MeasurableSpace (X i j)]
    (μ : (i : ι) → (j : κ i) → Measure (X i j)) [∀ i j, SigmaFinite (μ i j)] :
    MeasurePreserving (MeasurableEquiv.piCurry X)
      (Measure.pi fun p : (i : ι) × κ i => μ p.1 p.2)
      (Measure.pi fun i => Measure.pi fun j => μ i j) := by
  set e := (MeasurableEquiv.piCurry X).symm with he
  refine MeasurePreserving.symm e ?_
  refine ⟨e.measurable, (pi_eq fun s hs => ?_).symm⟩
  rw [Measure.map_apply e.measurable (MeasurableSet.univ_pi hs)]
  have hpre : e ⁻¹' (univ.pi s) = univ.pi (fun i => univ.pi (fun j => s ⟨i, j⟩)) := by
    ext g
    simp only [he, MeasurableEquiv.piCurry, MeasurableEquiv.coe_mk, Set.mem_preimage,
      Set.mem_pi, Set.mem_univ, forall_true_left]
    exact ⟨fun h i j => h ⟨i, j⟩, fun h p => h p.1 p.2⟩
  rw [hpre, pi_pi]
  simp_rw [pi_pi]
  exact (Fintype.prod_sigma (fun p : (i : ι) × κ i => (μ p.1 p.2) (s p))).symm

/-! ## The flat index and dimension -/

/-- The layer-and-row index `Σ s : Fin L, Fin H⁽ˢ⁾` (intermediate index for the first `piCurry`). -/
abbrev FlatRowIdx (H : Fin (L + 1) → ℕ) : Type := Σ s : Fin L, Fin (H s.castSucc)

/-- The full flat index `Σ (q : Σ s, Fin H⁽ˢ⁾), Fin H⁽ˢ⁺¹⁾` — one entry per matrix coordinate across
all layers. Its cardinality is `N = Σ_s H⁽ˢ⁾·H⁽ˢ⁺¹⁾`, the total parameter dimension. -/
abbrev FlatIdx (H : Fin (L + 1) → ℕ) : Type := Σ q : FlatRowIdx H, Fin (H q.1.succ)

/-- The flattened parameter dimension `N = Σ_s H⁽ˢ⁾·H⁽ˢ⁺¹⁾`. -/
def flatDim (H : Fin (L + 1) → ℕ) : ℕ := Fintype.card (FlatIdx H)

/-- `flatDim H = Σ_s H⁽ˢ⁾·H⁽ˢ⁺¹⁾` (the sum of per-layer matrix sizes). -/
theorem flatDim_eq (H : Fin (L + 1) → ℕ) :
    flatDim H = ∑ s : Fin L, (H s.castSucc) * (H s.succ) := by
  unfold flatDim FlatIdx FlatRowIdx
  rw [Fintype.card_sigma, Fintype.sum_sigma]
  simp only [Fintype.card_fin, Finset.sum_const, Finset.card_univ, smul_eq_mul]

/-! ## The measure-preserving flattening -/

/-- The measure-preserving equivalence `Params H ≃ᵐ (Fin N → ℝ)`: two `piCurry` steps (collapse the
`(s, i, j)` nesting to the flat index `FlatIdx H`) then re-index to `Fin N` by `arrowCongr'`. -/
noncomputable def paramsEquivFlat (H : Fin (L + 1) → ℕ) : Params H ≃ᵐ (Fin (flatDim H) → ℝ) :=
  (MeasurableEquiv.piCurry
      (fun (s : Fin L) (_ : Fin (H s.castSucc)) => Fin (H s.succ) → ℝ)).symm.trans
    ((MeasurableEquiv.piCurry (fun (q : FlatRowIdx H) (_ : Fin (H q.1.succ)) => ℝ)).symm.trans
      (MeasurableEquiv.arrowCongr' (Fintype.equivFin (FlatIdx H)) (MeasurableEquiv.refl ℝ)))

/-- **The keystone.** `paramsEquivFlat` is measure-preserving for the product Lebesgue (`volume`)
measures — so any integrability/RLCT fact on `Fin N → ℝ` transports to `Params H` (and back) via
`MeasurePreserving.integrableOn_comp_preimage`. Assembled from the two `measurePreserving_piCurry`
steps (`.symm`) and `volume_preserving_arrowCongr'`; the measures join by `rfl` (`Params`'s `volume`
is definitionally the nested `Measure.pi`). -/
theorem measurePreserving_paramsEquivFlat (H : Fin (L + 1) → ℕ) :
    MeasurePreserving (paramsEquivFlat H) (volume : Measure (Params H))
      (volume : Measure (Fin (flatDim H) → ℝ)) := by
  unfold paramsEquivFlat
  have h1 := measurePreserving_piCurry
    (fun (s : Fin L) (_ : Fin (H s.castSucc)) => Fin (H s.succ) → ℝ)
    (fun q _ => (volume : Measure (Fin (H q.succ) → ℝ)))
  have h2 := measurePreserving_piCurry
    (fun (q : FlatRowIdx H) (_ : Fin (H q.1.succ)) => ℝ) (fun _ _ => (volume : Measure ℝ))
  have ha := volume_preserving_arrowCongr' (Fintype.equivFin (FlatIdx H)) (MeasurableEquiv.refl ℝ)
    (MeasurePreserving.id (volume : Measure ℝ))
  exact (h1.symm _).trans ((h2.symm _).trans ha)

/-! ## `paramsEquivFlat` is a homeomorphism (continuity, both directions)

`paramsEquivFlat` is a `MeasurableEquiv`; these upgrade it to continuous in both directions (it is a
homeomorphism). Needed wherever a neighbourhood (not just a measurable set) must transport across
the flattening — the `rlctAt`/`weightedThreshold` `∃ U ∈ 𝓝` quantifier in the S1.1 transport rung
and R1. Each `piCurry`/`piCurry.symm` is `Sigma.curry`/`Sigma.uncurry` (continuous: every output
coordinate is an evaluation); `arrowCongr'` is a coordinate re-index (continuous). -/

/-- `Sigma.uncurry` on a `Pi`-type is continuous (each output coordinate is an evaluation). -/
theorem continuous_sigmaUncurry {ι : Type*} {κ : ι → Type*} (X : (i : ι) → κ i → Type*)
    [∀ i j, TopologicalSpace (X i j)] :
    Continuous (Sigma.uncurry : (∀ i j, X i j) → (∀ q : (i : ι) × κ i, X q.1 q.2)) := by
  apply continuous_pi; intro q
  exact (continuous_apply q.2).comp (continuous_apply q.1)

/-- `Sigma.curry` on a `Pi`-type is continuous (each output coordinate is an evaluation). -/
theorem continuous_sigmaCurry {ι : Type*} {κ : ι → Type*} (X : (i : ι) → κ i → Type*)
    [∀ i j, TopologicalSpace (X i j)] :
    Continuous (Sigma.curry : (∀ q : (i : ι) × κ i, X q.1 q.2) → (∀ i j, X i j)) := by
  apply continuous_pi; intro i; apply continuous_pi; intro j
  exact continuous_apply (⟨i, j⟩ : (i : ι) × κ i)

/-- `paramsEquivFlat` is continuous (two `Sigma.uncurry` steps + an evaluation re-index). -/
theorem continuous_paramsEquivFlat (H : Fin (L + 1) → ℕ) :
    Continuous (paramsEquivFlat H) := by
  have e1 : Continuous (⇑(MeasurableEquiv.piCurry
      (fun (s : Fin L) (_ : Fin (H s.castSucc)) => Fin (H s.succ) → ℝ)).symm) := by
    rw [MeasurableEquiv.coe_piCurry_symm]; exact continuous_sigmaUncurry _
  have e2 : Continuous (⇑(MeasurableEquiv.piCurry
      (fun (q : FlatRowIdx H) (_ : Fin (H q.1.succ)) => ℝ)).symm) := by
    rw [MeasurableEquiv.coe_piCurry_symm]; exact continuous_sigmaUncurry _
  have e3 : Continuous (⇑(MeasurableEquiv.arrowCongr'
      (Fintype.equivFin (FlatIdx H)) (MeasurableEquiv.refl ℝ))) := by
    apply continuous_pi; intro i; exact continuous_apply ((Fintype.equivFin (FlatIdx H)).symm i)
  exact e3.comp (e2.comp e1)

/-- `paramsEquivFlat.symm` is continuous (two `Sigma.curry` steps + an evaluation re-index). -/
theorem continuous_paramsEquivFlat_symm (H : Fin (L + 1) → ℕ) :
    Continuous (paramsEquivFlat H).symm := by
  have e1 : Continuous (⇑(MeasurableEquiv.piCurry
      (fun (s : Fin L) (_ : Fin (H s.castSucc)) => Fin (H s.succ) → ℝ))) := by
    rw [MeasurableEquiv.coe_piCurry]; exact continuous_sigmaCurry _
  have e2 : Continuous (⇑(MeasurableEquiv.piCurry
      (fun (q : FlatRowIdx H) (_ : Fin (H q.1.succ)) => ℝ))) := by
    rw [MeasurableEquiv.coe_piCurry]; exact continuous_sigmaCurry _
  have e3 : Continuous (⇑(MeasurableEquiv.arrowCongr'
      (Fintype.equivFin (FlatIdx H)) (MeasurableEquiv.refl ℝ)).symm) := by
    apply continuous_pi; intro i; exact continuous_apply ((Fintype.equivFin (FlatIdx H)) i)
  exact e1.comp (e2.comp e3)

end DLNFibre.DLN.RLCT
