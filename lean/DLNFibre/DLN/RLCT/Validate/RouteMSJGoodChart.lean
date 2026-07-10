import DLNFibre.DLN.RLCT.Validate.RouteMSJCornerGate
import DLNFibre.DLN.RLCT.Validate.RouteMSJGoodLoss
import DLNFibre.DLN.RLCT.Validate.RouteMSJCorankResidual

/-!
# `DLNFibre.DLN.RLCT.Validate.RouteMSJGoodChart` — the good-chart endpoint in matrix coordinates

**Thread `genm-resmap`, Stage 2 (S,J) resolution-map tide.** The banked corner endpoint
`corner_block_cube_lintegral_lt_top_of_injective` (`RouteMSJCornerGate`) is stated over the FLAT cube
`[-1,1]ⁿ ⊆ (Fin n → ℝ)` for a squared-injective-linear loss `∑ⱼ (L z)ⱼ²`. The `(S,J)` change-of-variables
lands the good-chart resolved loss `g_cc(Γ, v) = frobSq(P·v·A₂) + frobSq((C·v + Γ·W)·A₂)` in **matrix
coordinates** — the joint block `(Γ, v)` ranging over a product of matrix boxes. This module bridges the
two: it flattens the matrix-product box to the flat cube (measure-preserving) and packages the good-chart
map `sjGoodMap` (banked, `RouteMSJGoodLoss`) as an injective linear map on the flat coordinates, so the
endpoint applies directly.

* **`twoMatBox_injectiveLinear_lintegral_lt_top`** — the abstract transport lemma: given ANY
  measure-preserving flatten `E : (Matrix p q × Matrix r s) ≃ᵐ (Fin n → ℝ)` sending the matrix-product box
  onto the flat cube, and an injective linear `L : (Fin n → ℝ) →ₗ (Fin m → ℝ)`, the matrix-box integral of
  the loss `(∑ⱼ (L (E x))ⱼ²)^{−c'}` is finite for `c' < n/2`. (`E` is a hypothesis; the concrete flatten is
  built below.)

S2-FREE (no `monomial_rlct`, no `cited_aoyagi_dln`); network-free (pure measure theory + matrix algebra).
-/

namespace DLNFibre.DLN.RLCT

open MeasureTheory Set Matrix
open scoped ENNReal BigOperators

/-- **The good-chart endpoint, matrix-box coordinates (transport form).** Given a measure-preserving
flatten `E` of the matrix-product domain `Matrix (Fin p) (Fin q) ℝ × Matrix (Fin r) (Fin s) ℝ` onto the
flat coordinate space `Fin n → ℝ` that carries the matrix-product box `matBox p q 1 ×ˢ matBox r s 1` onto
the flat cube `[-1,1]ⁿ`, and an injective linear `L : (Fin n → ℝ) →ₗ (Fin m → ℝ)`, the matrix-box integral
of the squared-linear loss `(∑ⱼ (L (E x))ⱼ²)^{−c'}` is finite below the threshold `c' < n/2`.

Pure transport: rewrite the domain to `E ⁻¹' cube` (`hbox`), push the integral along the
measure-preserving embedding `E` (`setLIntegral_comp_preimage_emb`) to the flat cube, and invoke the
banked `corner_block_cube_lintegral_lt_top_of_injective`. The concrete flatten `E` is supplied by
`twoMatFlat` below. -/
theorem twoMatBox_injectiveLinear_lintegral_lt_top {p q r s n m : ℕ} [NeZero n]
    (E : ((Fin p → Fin q → ℝ) × (Fin r → Fin s → ℝ)) ≃ᵐ (Fin n → ℝ))
    (hE : MeasurePreserving E
      (volume : Measure ((Fin p → Fin q → ℝ) × (Fin r → Fin s → ℝ)))
      (volume : Measure (Fin n → ℝ)))
    (hbox : matBox p q 1 ×ˢ matBox r s 1
      = E ⁻¹' Set.univ.pi (fun _ : Fin n => Set.Icc (-1 : ℝ) 1))
    (L : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ)) (hL : Function.Injective L)
    (c' : NNReal) (hc' : (c' : ℝ) < (n : ℝ) / 2) :
    ∫⁻ x in matBox p q 1 ×ˢ matBox r s 1,
        ENNReal.ofReal ((∑ j, (L (E x) j) ^ 2) ^ (-(c' : ℝ))) < ⊤ := by
  rw [hbox]
  rw [hE.setLIntegral_comp_preimage_emb E.measurableEmbedding
    (fun z => ENNReal.ofReal ((∑ j, (L z j) ^ 2) ^ (-(c' : ℝ))))
    (Set.univ.pi (fun _ : Fin n => Set.Icc (-1 : ℝ) 1))]
  exact corner_block_cube_lintegral_lt_top_of_injective L hL (c' : ℝ) c'.coe_nonneg hc'

/-! ## The linear + measure-preserving matrix flatten

The endpoint lives on `Fin n → ℝ`; the good-chart loss lives on a product of matrix spaces. To feed the
endpoint we need a flatten that is BOTH a `LinearEquiv` (so the loss transports its degree-2 homogeneity
and positivity) AND measure-preserving (so the box integral transports). The banked `eMatFlat` is the
measure-preserving flatten; we pair it with a same-coe `LinearEquiv` (`matFlatL`) built from
`LinearEquiv.curry` + `LinearEquiv.funCongrLeft`, then combine two of them across a product. -/

/-- **The single-matrix flatten as an ℝ-linear equivalence** `(Fin p → Fin q → ℝ) ≃ₗ (Fin (p*q) → ℝ)`.
Same underlying reindex as `eMatFlat` (both read the entry at the `finProdFinEquiv`-decoded index), but
packaged as a `LinearEquiv` so its inverse is an ℝ-linear map. -/
noncomputable def matFlatL (p q : ℕ) : (Fin p → Fin q → ℝ) ≃ₗ[ℝ] (Fin (p * q) → ℝ) :=
  (LinearEquiv.curry ℝ ℝ (Fin p) (Fin q)).symm.trans
    (LinearEquiv.funCongrLeft ℝ ℝ (finProdFinEquiv (m := p) (n := q)).symm)

/-- `matFlatL p q D i = D (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2`. -/
theorem matFlatL_apply (p q : ℕ) (D : Fin p → Fin q → ℝ) (i : Fin (p * q)) :
    matFlatL p q D i = D (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2 := by
  simp only [matFlatL, LinearEquiv.trans_apply, LinearEquiv.funCongrLeft_apply,
    LinearMap.funLeft_apply, LinearEquiv.coe_curry_symm, Function.uncurry]

/-- `⇑(matFlatL p q) = ⇑(eMatFlat p q)` — the linear flatten and the measure-preserving flatten agree
as functions (both the `finProdFinEquiv`-decode entry read). -/
theorem coe_matFlatL (p q : ℕ) :
    (matFlatL p q : (Fin p → Fin q → ℝ) → (Fin (p * q) → ℝ)) = eMatFlat p q := by
  funext D i
  rw [matFlatL_apply, eMatFlat_apply]
  rfl

/-- `matFlatL p q` is measure-preserving (transferred from the banked `eMatFlat`). -/
theorem measurePreserving_matFlatL (p q : ℕ) :
    MeasurePreserving (matFlatL p q)
      (volume : Measure (Fin p → Fin q → ℝ)) (volume : Measure (Fin (p * q) → ℝ)) := by
  rw [coe_matFlatL]
  exact measurePreserving_eMatFlat p q

/-- **The product-of-two-matrix flatten as an ℝ-linear equivalence**
`((Fin p → Fin q → ℝ) × (Fin r → Fin s → ℝ)) ≃ₗ (Fin (p*q + r*s) → ℝ)`. Flatten each factor
(`matFlatL`), glue the two flat vectors as a `Fin (p*q) ⊕ Fin (r*s)`-indexed function
(`sumArrowLequivProdArrow`), and reindex the sum to `Fin (p*q + r*s)` (`finSumFinEquiv`). Linear
(so its inverse is an ℝ-linear map, giving the good-chart loss its homogeneity/positivity transport)
and measure-preserving (below). -/
noncomputable def twoMatFlatL (p q r s : ℕ) :
    ((Fin p → Fin q → ℝ) × (Fin r → Fin s → ℝ)) ≃ₗ[ℝ] (Fin (p * q + r * s) → ℝ) :=
  ((matFlatL p q).prodCongr (matFlatL r s)).trans
    (((LinearEquiv.sumArrowLequivProdArrow (Fin (p * q)) (Fin (r * s)) ℝ ℝ).symm).trans
      (LinearEquiv.funCongrLeft ℝ ℝ (finSumFinEquiv (m := p * q) (n := r * s)).symm))

/-- `twoMatFlatL p q r s x k = Sum.elim (matFlatL p q x.1) (matFlatL r s x.2) (finSumFinEquiv.symm k)`
— the flat vector reads the `x.1`-block or the `x.2`-block according to which side of the sum `k`
decodes to. -/
theorem twoMatFlatL_apply (p q r s : ℕ)
    (x : (Fin p → Fin q → ℝ) × (Fin r → Fin s → ℝ)) (k : Fin (p * q + r * s)) :
    twoMatFlatL p q r s x k
      = Sum.elim (matFlatL p q x.1) (matFlatL r s x.2) (finSumFinEquiv.symm k) := by
  simp only [twoMatFlatL, LinearEquiv.trans_apply, LinearEquiv.funCongrLeft_apply,
    LinearMap.funLeft_apply, LinearEquiv.prodCongr_apply, Function.comp_apply]
  rcases h : (finSumFinEquiv (m := p * q) (n := r * s)).symm k with a | b <;> rfl

/-- `twoMatFlatL p q r s` is measure-preserving. Its coe equals the composite of three banked
measure-preserving maps — the per-factor flatten product `Prod.map (matFlatL ·) (matFlatL ·)`
(`measurePreserving_matFlatL` × `measurePreserving_matFlatL`), the sum-pi splitter
(`sumPiEquivProdPi.symm`), and the sum-index reindex (`arrowCongr' finSumFinEquiv`). -/
theorem measurePreserving_twoMatFlatL (p q r s : ℕ) :
    MeasurePreserving (twoMatFlatL p q r s)
      (volume : Measure ((Fin p → Fin q → ℝ) × (Fin r → Fin s → ℝ)))
      (volume : Measure (Fin (p * q + r * s) → ℝ)) := by
  -- the three banked measure-preserving factors
  have hprod : MeasurePreserving (Prod.map (matFlatL p q) (matFlatL r s))
      (volume : Measure ((Fin p → Fin q → ℝ) × (Fin r → Fin s → ℝ)))
      (volume : Measure ((Fin (p * q) → ℝ) × (Fin (r * s) → ℝ))) := by
    rw [show (volume : Measure ((Fin p → Fin q → ℝ) × (Fin r → Fin s → ℝ)))
          = (volume : Measure (Fin p → Fin q → ℝ)).prod volume from Measure.volume_eq_prod _ _,
      show (volume : Measure ((Fin (p * q) → ℝ) × (Fin (r * s) → ℝ)))
          = (volume : Measure (Fin (p * q) → ℝ)).prod volume from Measure.volume_eq_prod _ _]
    exact (measurePreserving_matFlatL p q).prod (measurePreserving_matFlatL r s)
  have hsum : MeasurePreserving
      (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin (p * q) ⊕ Fin (r * s) => ℝ)).symm
      (volume : Measure ((Fin (p * q) → ℝ) × (Fin (r * s) → ℝ)))
      (volume : Measure (Fin (p * q) ⊕ Fin (r * s) → ℝ)) :=
    volume_measurePreserving_sumPiEquivProdPi_symm _
  have hreindex : MeasurePreserving
      (MeasurableEquiv.arrowCongr' (finSumFinEquiv (m := p * q) (n := r * s))
        (MeasurableEquiv.refl ℝ))
      (volume : Measure (Fin (p * q) ⊕ Fin (r * s) → ℝ))
      (volume : Measure (Fin (p * q + r * s) → ℝ)) :=
    volume_preserving_arrowCongr' (finSumFinEquiv (m := p * q) (n := r * s))
      (MeasurableEquiv.refl ℝ) (MeasurePreserving.id (volume : Measure ℝ))
  -- the coe of `twoMatFlatL` is the composite of the three
  have hcoe : (twoMatFlatL p q r s : _ → (Fin (p * q + r * s) → ℝ))
      = (MeasurableEquiv.arrowCongr' (finSumFinEquiv (m := p * q) (n := r * s))
            (MeasurableEquiv.refl ℝ))
        ∘ ((MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin (p * q) ⊕ Fin (r * s) => ℝ)).symm
        ∘ (Prod.map (matFlatL p q) (matFlatL r s))) := by
    funext x k
    rw [twoMatFlatL_apply]
    rfl
  have hcomp := hreindex.comp (hsum.comp hprod)
  rwa [← hcoe] at hcomp

end DLNFibre.DLN.RLCT
