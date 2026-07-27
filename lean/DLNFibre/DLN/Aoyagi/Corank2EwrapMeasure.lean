import DLNFibre.DLN.Aoyagi.Corank2CoreGenWrap
import DLNFibre.DLN.RLCT.Validate.RouteMSJCorankResidual

/-!
# `DLN.Aoyagi.Corank2EwrapMeasure` — `MeasurePreserving eWrap` (the sole un-banked V-lower residual)

`eWrap : (Fin 21 → ℝ) ≃ₜ Tuple (3,3,4)` (`Corank2CoreGenWrap`) is the transpose flatten: every tuple
entry equals exactly ONE input coordinate `u k`, so it is a pure **coordinate permutation** of the 21
real coordinates (origin-fixing, `eWrap_zero`). A coordinate permutation preserves the product-Lebesgue
volume — the fact `coreReduction` needs to identify the `(3,3,4)` DLN square-Frobenius RLCT with the
core-loss RLCT (`Corank2CiteFree334` carried it as an unproven hypothesis).

## Construction (route B — no opaque `Fintype.equivFin`)

`canonFlatten`/`tupleFlat` (`LearningCoefficient`) are measure-preserving but reindex by the OPAQUE
`Fintype.equivFin`, so they cannot be matched to `eWrap` coordinate-by-coordinate. Instead we build a
CONCRETE combinator flatten `cFlat : Tuple (3,3,4) ≃ᵐ (Fin 21 → ℝ)` (measure-preserving) from
`piFinTwo` (split the two layers) → `eMatFlat` per layer (`RouteMSJCorankResidual`) →
`sumPiEquivProdPi.symm` (combine `Fin 9 ⊕ Fin 12`) → `arrowCongr' finSumFinEquiv` (reindex to `Fin 21`).
`cFlat`'s reads are transparent, so the single scattered coordinate permutation relating it to `eWrap`
is the explicit `piSymm : Fin 21 → Fin 21` (a genuine permutation, `Bijective` by `decide`), and
`cFlat (eWrap u) = fun k ↦ u (piSymm k)` closes by `fin_cases k <;> rfl`. Then
`eWrap = cFlat.symm ∘ (arrowCongr' piEquiv id)` with both factors measure-preserving.
-/

open MeasureTheory
open DLNFibre.Core DLNFibre.Core.Aoyagi
open DLNFibre.DLN.RLCT (eMatFlat measurePreserving_eMatFlat)

namespace DLNFibre.DLN.Aoyagi.Corank2CoreGenWrap

/-! ## The concrete combinator flatten `cFlat : Tuple (3,3,4) ≃ᵐ (Fin 21 → ℝ)` -/

/-- The concrete measure-preserving flatten of the `(3,3,4)` tuple: split the two layers (`piFinTwo`),
flatten each layer matrix (`eMatFlat`), combine `Fin 9 ⊕ Fin 12` (`sumPiEquivProdPi`), reindex to
`Fin 21` (`arrowCongr' finSumFinEquiv`). All reads are transparent (no `Fintype.equivFin`). -/
noncomputable def cFlat : Tuple (k := ℝ) dvec ≃ᵐ (Fin 21 → ℝ) :=
  (MeasurableEquiv.piFinTwo (fun i : Fin 2 =>
      Fin (dvec i.succ) → Fin (dvec i.castSucc) → ℝ)).trans
    ((MeasurableEquiv.prodCongr (eMatFlat 3 3) (eMatFlat 4 3)).trans
      ((MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin 9 ⊕ Fin 12 => ℝ)).symm.trans
        (MeasurableEquiv.arrowCongr' finSumFinEquiv (MeasurableEquiv.refl ℝ))))

/-- `cFlat` is measure-preserving (chain of `volume_preserving_*` on each combinator step). -/
theorem measurePreserving_cFlat :
    MeasurePreserving cFlat (volume : Measure (Tuple (k := ℝ) dvec))
      (volume : Measure (Fin 21 → ℝ)) := by
  unfold cFlat
  have hA := volume_preserving_piFinTwo
    (fun i : Fin 2 => Fin (dvec i.succ) → Fin (dvec i.castSucc) → ℝ)
  have hB := (measurePreserving_eMatFlat 3 3).prod (measurePreserving_eMatFlat 4 3)
  have hC := measurePreserving_sumPiEquivProdPi_symm (fun _ : Fin 9 ⊕ Fin 12 => (volume : Measure ℝ))
  have hD := volume_preserving_arrowCongr' (@finSumFinEquiv 9 12) (MeasurableEquiv.refl ℝ)
    (MeasurePreserving.id (volume : Measure ℝ))
  exact hA.trans (hB.trans (hC.trans hD))

/-! ## The scattered coordinate permutation relating `cFlat` to `eWrap` -/

/-- The permutation `Fin 21 → Fin 21` (inverse direction) matching `cFlat`'s canonical coordinate
order to `eWrap`'s scattered layout — hand-derived from the combinator chain, `decide`-verified to be
a bijection. -/
def piSymm : Fin 21 → Fin 21 :=
  ![20, 2, 3, 0, 4, 6, 1, 5, 7, 8, 12, 16, 9, 13, 17, 10, 14, 18, 11, 15, 19]

theorem piSymm_bijective : Function.Bijective piSymm := by decide

/-- The coordinate permutation as an `Equiv.Perm (Fin 21)` whose `symm` is `piSymm`. -/
noncomputable def piEquiv : Equiv.Perm (Fin 21) :=
  (Equiv.ofBijective piSymm piSymm_bijective).symm

theorem piEquiv_symm_apply (k : Fin 21) : piEquiv.symm k = piSymm k := rfl

/-- **The coordinate match**: `cFlat (eWrap u) = u ∘ piSymm` (the flatten reindexes `eWrap`'s reads by
the permutation `piSymm`). Closes by `fin_cases` + `rfl` — every step reduces (transparent reads). -/
theorem cFlat_eWrap (u : Fin 21 → ℝ) : cFlat (eWrap u) = fun k => u (piSymm k) := by
  funext k
  fin_cases k <;> rfl

/-! ## `MeasurePreserving eWrap` -/

/-- **`MeasurePreserving eWrap`** (volume → volume): `eWrap` is a coordinate permutation, so it equals
the measure-preserving `cFlat.symm` composed with the measure-preserving coordinate reindex
`arrowCongr' piEquiv id`. This discharges the sole un-banked input of `coreReduction` at `(3,3,4)`. -/
theorem measurePreserving_eWrap :
    MeasurePreserving eWrap (volume : Measure (Fin 21 → ℝ))
      (volume : Measure (Tuple (k := ℝ) dvec)) := by
  have harrow : MeasurePreserving (MeasurableEquiv.arrowCongr' piEquiv (MeasurableEquiv.refl ℝ))
      (volume : Measure (Fin 21 → ℝ)) (volume : Measure (Fin 21 → ℝ)) :=
    volume_preserving_arrowCongr' piEquiv (MeasurableEquiv.refl ℝ) (MeasurePreserving.id _)
  have hcomp := (measurePreserving_cFlat.symm cFlat).comp harrow
  have hfun : (⇑cFlat.symm ∘ ⇑(MeasurableEquiv.arrowCongr' piEquiv (MeasurableEquiv.refl ℝ)))
      = ⇑eWrap := by
    funext u
    have hmatch : cFlat (eWrap u)
        = ⇑(MeasurableEquiv.arrowCongr' piEquiv (MeasurableEquiv.refl ℝ)) u := by
      rw [cFlat_eWrap]; rfl
    simp only [Function.comp_apply]
    rw [← hmatch, cFlat.symm_apply_apply]
  rwa [hfun] at hcomp

end DLNFibre.DLN.Aoyagi.Corank2CoreGenWrap
