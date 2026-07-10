import DLNFibre.DLN.RLCT.Validate.RouteMSJCornerGate
import DLNFibre.DLN.RLCT.Validate.RouteMSJGoodLoss
import DLNFibre.DLN.RLCT.Validate.RouteMSJCorankResidual
import DLNFibre.DLN.RLCT.Validate.RouteMSJCorankStep
import DLNFibre.DLN.RLCT.Validate.RouteMSJChartWeld
import DLNFibre.DLN.RLCT.Validate.RouteMSJChartShear

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

/-- The matrix-product box is the `twoMatFlatL`-preimage of the flat cube `[-1,1]^{p*q+r*s}`. -/
theorem twoMatFlatL_box_preimage (p q r s : ℕ) :
    matBox p q 1 ×ˢ matBox r s 1
      = twoMatFlatL p q r s ⁻¹' Set.univ.pi (fun _ : Fin (p * q + r * s) => Set.Icc (-1 : ℝ) 1) := by
  ext x
  simp only [Set.mem_prod, matBox, Set.mem_setOf_eq, Set.mem_preimage, Set.mem_pi,
    Set.mem_univ, true_implies]
  constructor
  · rintro ⟨h1, h2⟩ j
    rw [twoMatFlatL_apply]
    rcases (finSumFinEquiv (m := p * q) (n := r * s)).symm j with a | b
    · rw [Sum.elim_inl, matFlatL_apply]; exact h1 _ _
    · rw [Sum.elim_inr, matFlatL_apply]; exact h2 _ _
  · intro h
    refine ⟨fun i k => ?_, fun i k => ?_⟩
    · have hj := h (finSumFinEquiv (Sum.inl (finProdFinEquiv (i, k))))
      rw [twoMatFlatL_apply, Equiv.symm_apply_apply, Sum.elim_inl, matFlatL_apply,
        Equiv.symm_apply_apply] at hj
      exact hj
    · have hj := h (finSumFinEquiv (Sum.inr (finProdFinEquiv (i, k))))
      rw [twoMatFlatL_apply, Equiv.symm_apply_apply, Sum.elim_inr, matFlatL_apply,
        Equiv.symm_apply_apply] at hj
      exact hj

/-! ## The good-chart cross-coupled loss endpoint (matrix coordinates)

Packaging `sjGoodMap` (banked, `RouteMSJGoodLoss`) as an ℝ-linear map so its loss transports the
degree-2 homogeneity and (via `sjGoodMap_loss_pos`) the sphere positivity through the flatten, then
feeding the banked `corner_block_cube_lintegral_lt_top_of_pos`. -/

section GoodChart
variable {t p q h o : ℕ}

/-- `frobSq` is continuous (a finite sum of squared coordinate evaluations). -/
theorem continuous_frobSq {a b : Type*} [Fintype a] [Fintype b] :
    Continuous (fun M : a → b → ℝ => frobSq M) := by
  unfold frobSq
  exact continuous_finset_sum _ (fun i _ => continuous_finset_sum _
    (fun j _ => ((continuous_apply j).comp (continuous_apply i)).pow 2))

/-- **The good-chart map `sjGoodMap` as an ℝ-linear map** (matrix multiplication is bilinear, so
`(Γ, v) ↦ (P·v·A₂, (C·v + Γ·W)·A₂)` is linear). Its coe is `sjGoodMap`; this bundles the additivity
and homogeneity needed to transport the loss. -/
def sjGoodMapₗ (P : Matrix (Fin t) (Fin t) ℝ) (C : Matrix (Fin p) (Fin t) ℝ)
    (W : Matrix (Fin q) (Fin h) ℝ) (A2 : Matrix (Fin h) (Fin o) ℝ) :
    (Matrix (Fin p) (Fin q) ℝ × Matrix (Fin t) (Fin h) ℝ) →ₗ[ℝ]
      (Matrix (Fin t) (Fin o) ℝ × Matrix (Fin p) (Fin o) ℝ) where
  toFun := sjGoodMap P C W A2
  map_add' x y := by
    refine Prod.ext ?_ ?_
    · show P * (x.2 + y.2) * A2 = P * x.2 * A2 + P * y.2 * A2
      rw [Matrix.mul_add, Matrix.add_mul]
    · show (C * (x.2 + y.2) + (x.1 + y.1) * W) * A2
          = (C * x.2 + x.1 * W) * A2 + (C * y.2 + y.1 * W) * A2
      simp only [Matrix.mul_add, Matrix.add_mul]; abel
  map_smul' r x := by
    refine Prod.ext ?_ ?_
    · show P * (r • x.2) * A2 = r • (P * x.2 * A2)
      rw [Matrix.mul_smul, Matrix.smul_mul]
    · show (C * (r • x.2) + (r • x.1) * W) * A2 = r • ((C * x.2 + x.1 * W) * A2)
      rw [Matrix.mul_smul, Matrix.smul_mul, ← smul_add, Matrix.smul_mul]

@[simp] theorem sjGoodMapₗ_apply (P : Matrix (Fin t) (Fin t) ℝ) (C : Matrix (Fin p) (Fin t) ℝ)
    (W : Matrix (Fin q) (Fin h) ℝ) (A2 : Matrix (Fin h) (Fin o) ℝ) (x) :
    sjGoodMapₗ P C W A2 x = sjGoodMap P C W A2 x := rfl

/-- **The Schur-split loss equals `g_cc` once the sheared row-blocks factor through the deep factor.**
If the shear coordinate `Q̃_p = v·A₂` and the corank rows `Q_b = W·A₂` (the depth reduction of the tail
product, vslice §4a), then the exact Schur-split loss `frobSq(P·Q̃_p) + frobSq(C·Q̃_p + Γ·Q_b)` equals the
good-chart cross-coupled loss `g_cc(Γ, v) = frobSq(sjGoodMap P C W A₂ (Γ, v))`. Pure matrix associativity
(`P·(v·A₂) = P·v·A₂`, `C·(v·A₂) + Γ·(W·A₂) = (C·v + Γ·W)·A₂`). -/
theorem schurSplitLoss_eq_sjGoodMap (P : Matrix (Fin t) (Fin t) ℝ) (C : Matrix (Fin p) (Fin t) ℝ)
    (Γ : Matrix (Fin p) (Fin q) ℝ) (W : Matrix (Fin q) (Fin h) ℝ) (A2 : Matrix (Fin h) (Fin o) ℝ)
    (v : Matrix (Fin t) (Fin h) ℝ) :
    frobSq (P * (v * A2)) + frobSq (C * (v * A2) + Γ * (W * A2))
      = frobSq (sjGoodMap P C W A2 (Γ, v)).1 + frobSq (sjGoodMap P C W A2 (Γ, v)).2 := by
  have h1 : P * (v * A2) = P * v * A2 := (Matrix.mul_assoc P v A2).symm
  have h2 : C * (v * A2) + Γ * (W * A2) = (C * v + Γ * W) * A2 := by
    rw [Matrix.add_mul, Matrix.mul_assoc C v A2, Matrix.mul_assoc Γ W A2]
  simp only [sjGoodMap]
  rw [h1, h2]

/-- **The exact pointwise CoV bridge (item 4): `frobSq(A₀·Q) = g_cc(Γ, v)` on the pivot chart.** With
`A₀ = fromBlocks P B C D` (pivot `P` invertible) and the tail product `Q` whose sheared/corank row-blocks
factor through the deep factor `A₂` — `Q̃_p := Q_p + P⁻¹·B·Q_b = v·A₂` and `Q_b = W·A₂` — the raw
front-factor loss equals the resolved cross-coupled loss `g_cc(Γ, v)`, `Γ = schurCompl P B C D`. Composes
the banked `frobSq_schur_block_split` with `schurSplitLoss_eq_sjGoodMap`. The factorization hypotheses
`hp`, `hb` are the DEPTH REDUCTION the change-of-variables supplies from `prod (tailChain M) A'`. -/
theorem frobSq_schur_eq_sjGoodMap (P : Matrix (Fin t) (Fin t) ℝ) [Invertible P]
    (B : Matrix (Fin t) (Fin q) ℝ) (C : Matrix (Fin p) (Fin t) ℝ) (D : Matrix (Fin p) (Fin q) ℝ)
    (Q : Matrix (Fin t ⊕ Fin q) (Fin o) ℝ)
    (v : Matrix (Fin t) (Fin h) ℝ) (W : Matrix (Fin q) (Fin h) ℝ) (A2 : Matrix (Fin h) (Fin o) ℝ)
    (hp : Q.submatrix Sum.inl id + ⅟P * B * Q.submatrix Sum.inr id = v * A2)
    (hb : Q.submatrix Sum.inr id = W * A2) :
    frobSq (fromBlocks P B C D * Q)
      = frobSq (sjGoodMap P C W A2 (schurCompl P B C D, v)).1
        + frobSq (sjGoodMap P C W A2 (schurCompl P B C D, v)).2 := by
  rw [frobSq_schur_block_split P B C D Q, hp, hb]
  exact schurSplitLoss_eq_sjGoodMap P C (schurCompl P B C D) W A2 v

/-- **The good-chart cross-coupled loss is endpoint-admissible in matrix coordinates.** For the
good-chart data (pivot `P` left-invertible, deep factor `A₂` and resolved map `W` right-invertible)
and `c' < (p*q + t*h)/2`, the matrix-product-box integral of the resolved cross-coupled loss
`g_cc(Γ, v) = frobSq(P·v·A₂) + frobSq((C·v + Γ·W)·A₂)` to the `−c'` power is finite. Flatten the joint
block `(Γ, v)` to `Fin (p*q + t*h) → ℝ` (`twoMatFlatL`, measure-preserving + linear), transporting the
box to the flat cube; the loss becomes a degree-2-homogeneous, continuous, sphere-positive
(`sjGoodMap_loss_pos`) function, so the banked `corner_block_cube_lintegral_lt_top_of_pos` closes it.
This is the good-chart `(S,J)` endpoint the change-of-variables feeds. -/
theorem sjGoodMap_loss_matBox_lt_top [NeZero (p * q + t * h)]
    (P : Matrix (Fin t) (Fin t) ℝ) (LP : Matrix (Fin t) (Fin t) ℝ) (hP : LP * P = 1)
    (C : Matrix (Fin p) (Fin t) ℝ)
    (W : Matrix (Fin q) (Fin h) ℝ) (RW : Matrix (Fin h) (Fin q) ℝ) (hW : W * RW = 1)
    (A2 : Matrix (Fin h) (Fin o) ℝ) (RA : Matrix (Fin o) (Fin h) ℝ) (hA2 : A2 * RA = 1)
    (c' : NNReal) (hc' : (c' : ℝ) < (p * q + t * h : ℝ) / 2) :
    ∫⁻ x in matBox p q 1 ×ˢ matBox t h 1,
        ENNReal.ofReal ((frobSq (sjGoodMap P C W A2 x).1
          + frobSq (sjGoodMap P C W A2 x).2) ^ (-(c' : ℝ))) < ⊤ := by
  classical
  set F := twoMatFlatL p q t h with hFdef
  -- the loss on matrix coordinates, and its flat-coordinate version `g = loss ∘ F.symm`
  set loss : ((Fin p → Fin q → ℝ) × (Fin t → Fin h → ℝ)) → ℝ :=
    fun x => frobSq (sjGoodMap P C W A2 x).1 + frobSq (sjGoodMap P C W A2 x).2 with hlossdef
  set g : (Fin (p * q + t * h) → ℝ) → ℝ := fun z => loss (F.symm z) with hgdef
  -- `sjGoodMap` is continuous (linear on finite-dim), hence `loss` and `g` are continuous
  have hsjcont : Continuous (sjGoodMap P C W A2) := by
    have : Continuous (sjGoodMapₗ P C W A2) := (sjGoodMapₗ P C W A2).continuous_of_finiteDimensional
    simpa only [sjGoodMapₗ_apply] using this
  have hlosscont : Continuous loss := by
    rw [hlossdef]
    exact (continuous_frobSq.comp (continuous_fst.comp hsjcont)).add
      (continuous_frobSq.comp (continuous_snd.comp hsjcont))
  have hFsymmcont : Continuous (F.symm : (Fin (p * q + t * h) → ℝ) → _) :=
    F.symm.toLinearMap.continuous_of_finiteDimensional
  have hgc : Continuous g := by rw [hgdef]; exact hlosscont.comp hFsymmcont
  -- degree-2 homogeneity of `g` (from the linearity of `F.symm` and `sjGoodMap`, and `frobSq_smul`)
  have hom : ∀ (r : ℝ) (z : Fin (p * q + t * h) → ℝ), g (r • z) = r ^ 2 * g z := by
    intro r z
    simp only [hgdef, hlossdef]
    rw [map_smul]
    have hs : sjGoodMap P C W A2 (r • F.symm z) = r • sjGoodMap P C W A2 (F.symm z) := by
      have := (sjGoodMapₗ P C W A2).map_smul r (F.symm z)
      simpa only [sjGoodMapₗ_apply, RingHom.id_apply] using this
    rw [hs]
    show frobSq (r • (sjGoodMap P C W A2 (F.symm z)).1)
        + frobSq (r • (sjGoodMap P C W A2 (F.symm z)).2)
      = r ^ 2 * (frobSq (sjGoodMap P C W A2 (F.symm z)).1
        + frobSq (sjGoodMap P C W A2 (F.symm z)).2)
    rw [frobSq_smul, frobSq_smul]; ring
  -- sphere positivity of `g` (from injectivity of `F.symm` and the banked `sjGoodMap_loss_pos`)
  have hpos : ∀ ω : Metric.sphere (0 : EuclideanSpace ℝ (Fin (p * q + t * h))) 1,
      0 < g (WithLp.ofLp (ω : EuclideanSpace ℝ (Fin (p * q + t * h)))) := by
    intro ω
    simp only [hgdef, hlossdef]
    have hωne : (ω : EuclideanSpace ℝ (Fin (p * q + t * h))) ≠ 0 := by
      intro hω0
      have hn := mem_sphere_zero_iff_norm.mp ω.2
      rw [hω0, norm_zero] at hn
      exact one_ne_zero hn.symm
    have hne : (WithLp.ofLp (ω : EuclideanSpace ℝ (Fin (p * q + t * h))) : Fin _ → ℝ) ≠ 0 := by
      rw [Ne, WithLp.ofLp_eq_zero]; exact hωne
    have hxne : F.symm (WithLp.ofLp (ω : EuclideanSpace ℝ (Fin (p * q + t * h)))) ≠ 0 :=
      fun hzero => hne (F.symm.injective (hzero.trans (map_zero F.symm).symm))
    exact sjGoodMap_loss_pos P LP hP C W RW hW A2 RA hA2 _ hxne
  -- transport the box integral to the flat cube via the measure-preserving flatten, then endpoint
  set Fm := F.toContinuousLinearEquiv.toHomeomorph.toMeasurableEquiv with hFmdef
  have hFmcoe : (Fm : ((Fin p → Fin q → ℝ) × (Fin t → Fin h → ℝ)) → (Fin (p * q + t * h) → ℝ))
      = ⇑F := rfl
  have hFmp : MeasurePreserving Fm
      (volume : Measure ((Fin p → Fin q → ℝ) × (Fin t → Fin h → ℝ)))
      (volume : Measure (Fin (p * q + t * h) → ℝ)) := by
    refine ⟨Fm.measurable, ?_⟩
    have := (measurePreserving_twoMatFlatL p q t h).map_eq
    rwa [← hFmcoe] at this
  have hbox : matBox p q 1 ×ˢ matBox t h 1
      = Fm ⁻¹' Set.univ.pi (fun _ : Fin (p * q + t * h) => Set.Icc (-1 : ℝ) 1) := by
    rw [hFmcoe]; exact twoMatFlatL_box_preimage p q t h
  -- the integrand transports: `loss x = g (Fm x)` (since `Fm x = F x` and `F.symm (F x) = x`)
  have hgFm : ∀ x, g (Fm x) = loss x := by
    intro x
    rw [hgdef]
    simp only
    rw [hFmcoe, F.symm_apply_apply]
  have hmeas : MeasurableSet
      (Fm ⁻¹' Set.univ.pi (fun _ : Fin (p * q + t * h) => Set.Icc (-1 : ℝ) 1)) :=
    (MeasurableSet.univ_pi (fun _ => measurableSet_Icc)).preimage Fm.measurable
  have hEqOn : Set.EqOn (fun x => ENNReal.ofReal ((loss x) ^ (-(c' : ℝ))))
      (fun x => (fun z => ENNReal.ofReal ((g z) ^ (-(c' : ℝ)))) (Fm x))
      (Fm ⁻¹' Set.univ.pi (fun _ : Fin (p * q + t * h) => Set.Icc (-1 : ℝ) 1)) := by
    intro x _
    show ENNReal.ofReal ((loss x) ^ (-(c' : ℝ))) = ENNReal.ofReal ((g (Fm x)) ^ (-(c' : ℝ)))
    rw [hgFm]
  rw [hbox, setLIntegral_congr_fun hmeas hEqOn,
    hFmp.setLIntegral_comp_preimage_emb Fm.measurableEmbedding
      (fun z => ENNReal.ofReal ((g z) ^ (-(c' : ℝ))))
      (Set.univ.pi (fun _ : Fin (p * q + t * h) => Set.Icc (-1 : ℝ) 1))]
  exact corner_block_cube_lintegral_lt_top_of_pos g hgc hom (c' : ℝ) c'.coe_nonneg
    (by push_cast; exact hc') hpos

/-- **Non-vacuity witness.** At equal unit widths with identity pivot/resolved maps (`P = W = A₂ = 1`,
so `LP = RW = RA = 1`, `C = 0`), the good-chart hypotheses of `sjGoodMap_loss_matBox_lt_top` are jointly
satisfiable — so the theorem is not vacuously true. -/
example : True := by
  haveI : NeZero (1 * 1 + 1 * 1) := ⟨by norm_num⟩
  have _ := sjGoodMap_loss_matBox_lt_top (1 : Matrix (Fin 1) (Fin 1) ℝ)
    (1 : Matrix (Fin 1) (Fin 1) ℝ) (one_mul 1) (0 : Matrix (Fin 1) (Fin 1) ℝ)
    (1 : Matrix (Fin 1) (Fin 1) ℝ) (1 : Matrix (Fin 1) (Fin 1) ℝ) (one_mul 1)
    (1 : Matrix (Fin 1) (Fin 1) ℝ) (1 : Matrix (Fin 1) (Fin 1) ℝ) (one_mul 1) 0 (by norm_num)
  trivial

end GoodChart

/-! ## The full inner-integral change of variables (raw chart integral → freed Schur loss)

Composing the two banked transports — the block-reindex + Schur split weld
(`chartInner_schurWeld_eq_of_emb`) and the measure-preserving shear (`chartInner_schurShearFree_eq`) —
carries the RAW inner front-factor chart integral (the inner fibre of `gammaPeelIntegral`) all the way to
the outer `(P, B₁₂, C)`-integral of the inner freed-Schur-loss `Γ`-integral over the shear-image box.
This is the measure half of the CoV entry, banked end-to-end. -/

/-- **The inner chart integral equals the outer/inner freed-Schur-loss integral.** For a `t`-element
`(ρ, κ)` pivot and a fixed tail product `Q`, the inner fibre of `gammaPeelIntegral`
(`∫_{A₀ ∈ matBox ∩ pivotChart ρ κ} frobSq(A₀·Q)^{−c'}`) equals the outer integral over the
`(P, B₁₂, C)`-box-with-invertible-pivot `outerDom` of the inner integral over the shear-image
`Γ`-box of `(freedSchurLoss x Γ Q̃)^{−c'}`, `Q̃ = Q.submatrix (blockSplitEquiv κ) id`. Pure composition of
`chartInner_schurWeld_eq_of_emb` (reindex + Schur split) and `chartInner_schurShearFree_eq` (the shear
`D ↦ Γ`, Jacobian 1). The remaining CoV steps (identifying `freedSchurLoss` with the good-chart `g_cc`
via the depth reduction `Q̃ₚ = v·A₂`, `Q_b = W·A₂`, and the nested finiteness against the endpoint
`sjGoodMap_loss_matBox_lt_top` on the refined cover) are the un-banked mountain. -/
theorem chartInner_eq_outerShearFree {p n q t : ℕ}
    (ρ : Fin t ↪ Fin p) (κ : Fin t ↪ Fin n)
    (Q : Matrix (Fin n) (Fin q) ℝ) (c' T : ℝ) :
    ∫⁻ A₀ in matBox p n T ∩ pivotChart ρ κ,
        ENNReal.ofReal ((frobSq (rmatMul A₀ Q)) ^ (-c'))
      = ∫⁻ x in outerDom t (p - t) (n - t) T,
          ∫⁻ Γ in {Γ : Fin (p - t) → Fin (n - t) → ℝ |
              Γ + schurShift x ∈ genBox (Fin (p - t)) (Fin (n - t)) T},
            ENNReal.ofReal
              ((freedSchurLoss x Γ (Q.submatrix (blockSplitEquiv κ) id)) ^ (-c')) := by
  rw [chartInner_schurWeld_eq_of_emb ρ κ Q c' T,
    chartInner_schurShearFree_eq (Q.submatrix (blockSplitEquiv κ) id) c' T]

end DLNFibre.DLN.RLCT
