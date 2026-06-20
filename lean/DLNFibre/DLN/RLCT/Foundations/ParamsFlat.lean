import DLNFibre.DLN.RLCT.Foundations.Rlct
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.MeasurableSpace.Embedding

/-!
# `DLNFibre.DLN.RLCT.Foundations.ParamsFlat` — flattening `Params H` to `ℝ^N` (measure infra)

Route A toward `paramsEquivFlat : Params H ≃ᵐ (Fin N → ℝ)` measure-preserving (task #15): the single
reusable artifact the `(1,1,1)` bridge, the S1.1 use-site, and the general R1 all transport through.

The one Mathlib gap (pp's thread-11 research): `measurePreserving_piCurry` — the measure-preserving
statement for the existing `MeasurableEquiv.piCurry` (a `Σ`-indexed `Measure.pi` equals the nested
`Measure.pi`-of-`Measure.pi` under currying). Mirrors `measurePreserving_arrowProdEquivProdArrow`,
but the clean route is via the **symmetric** map (`Sigma.uncurry`): its preimage of a `Σ`-box is a
nested box, so `Measure.pi_eq` + `pi_pi` + `Fintype.prod_sigma` close it, then
`MeasurePreserving.symm`.
Everything else for the `paramsEquivFlat` assembly (`arrowCongr'` + `measurePreserving_arrowCongr'`,
`Fintype.equivFin`, the `card (Idx H) = N` count) is confirmed-present in Mathlib v4.29.

## Assembly status (the gap lemma is banked; the final `paramsEquivFlat` assembly is held)

`measurePreserving_piCurry` (below) is the banked gap. The remaining `paramsEquivFlat` assembly hits
the recurring **`Matrix`-as-`def` instance wall**: `MeasurableSpace (Matrix (Fin (H s.castSucc)) … ℝ)`
does **not** synthesise uniformly in symbolic `s` (same cause as the parked `(1,1,1)` bridge), so the
type-level chain `Params H ≃ᵐ (∀ s, (Fin aₛ × Fin bₛ) → ℝ)` via `MeasurableEquiv.piCongrRight`
(`curry.symm` per layer) **fails instance synthesis**, and `Params`'s `volume` is not `rfl`-equal to
the nested `Measure.pi` (the `Matrix`-fiber instances resolve only per *concrete* `s`). Route options
(pp on-demand): supply the `Matrix` fiber instances explicitly via `inferInstanceAs` at each
`piCongrRight`/`piCurry` use; or route per-layer through `funUnique`/`measurePreserving_pi` with
`fin_cases`-discharged fibers (as in the `(1,1,1)` proof); or a `Measure.pi`-shape helper equating
`Params`'s `volume` to the nested `Measure.pi`. The gap lemma stands ready for whichever route. -/

open MeasureTheory MeasureTheory.Measure Set
namespace DLNFibre.DLN.RLCT

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

end DLNFibre.DLN.RLCT
