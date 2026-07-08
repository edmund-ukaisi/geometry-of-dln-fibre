import DLNFibre.DLN.RLCT.Validate.RouteMSJChartWeld

/-!
# `DLNFibre.DLN.RLCT.Validate.RouteMSJChartShear` — the measure-preserving shear `D ↦ Γ` (free the corank block)

**Piece 1 of the R1-UPPER `(S,J)` peel's Γ-integration** (thread `genm-sjcarrier7`; the final gate →
`sjJointResolution`, `RouteMSJResolution.lean`). The banked Schur weld
(`chartInner_schurWeld_eq_of_emb`, `RouteMSJChartWeld`) rewrote the RAW front-factor chart integral to
the cross-coupled Schur block integral over `genBox ∩ {IsUnit toBlocks₁₁}`, EXPOSING the corank block
`Γ = D − C·P⁻¹·B₁₂` inside the integrand (`schurLoss`). This module **frees `Γ` as an independent
integration variable**: it decomposes the block-matrix integral over its four blocks `(P, B₁₂, C, D)`
and change-of-variables the innermost `D`-block to `Γ` (a translation `D ↦ D − C·P⁻¹·B₁₂` at fixed
`(P, B₁₂, C)`, measure-preserving), landing on the *freed* Schur loss in which `Γ` appears only in the
corank term `frobSq (C·Q̃ₚ + Γ·Q_b)`.

## What lands here (this module — the shear that frees `Γ`)

* **`blockSplitD`** — the measure-preserving block decomposition `((Fin t ⊕ Fin a) → (Fin t ⊕ Fin b) →
  ℝ) ≃ᵐ SJOuter t a b × (Fin a → Fin b → ℝ)`, `SJOuter t a b = ((Fin t → Fin t → ℝ) × (Fin t → Fin b →
  ℝ)) × (Fin a → Fin t → ℝ)` the `(P, B₁₂, C)` triple, the last factor the corank `D`-block. Built by
  a row split (`sumPiEquivProdPi`) + a column split of each row block (`splitCols`) + a reassociation.
* **`of_blockSplitD_symm_eq_fromBlocks`** — the reconstruction: `Matrix.of (blockSplitD.symm (x, D)) =
  fromBlocks (of x.1.1) (of x.1.2) (of x.2) (of D)`, i.e. the four factors ARE the four blocks.
* **`freedSchurLoss`** — the Schur loss with the corank block `Γ` as a FREE argument (not the derived
  `D − C·P⁻¹·B₁₂`): `frobSq (P·Q̃ₚ) + frobSq (C·Q̃ₚ + Γ·Q_b)`, `Q̃ₚ = Q_p + P⁻¹·B₁₂·Q_b`.
* **`chartInner_schurShearFree_eq`** — the shear identity (EQUALITY, no finiteness claim, no branch
  condition): the Schur block chart integral equals the OUTER integral over the `(P, B₁₂, C)`-box ∩
  `{IsUnit P}` of the INNER `Γ`-integral over the shear-image box `{Γ | Γ + C·P⁻¹·B₁₂ ∈ box}`, of the
  FREED Schur loss `(freedSchurLoss x Γ Q̃)^{−c'}`.

## What is NOT here (the standing mountain — reported precisely)

The corank block `Γ` is now FREE, but not yet INTEGRATED. What remains (decorrelated-Codex/design-cert
scoped, `genm-sjjoint-design/cert.md`): (i) enlarge the shear-image box to the full space (`≤`,
integrand `≥ 0`) and apply the banked anisotropic corank atom (`corankBlock_morsePeel_setLE`,
`RouteMSJCorankPeel`) — which needs the deeper core strictly positive (`w > 0`, NOT supplied pointwise)
and `Q_b Q_bᵀ` positive-definite (fails on the bottleneck charts `M₁−t > min deeper widths`); (ii) the
separate `c' ≤ a/2` bounded-integrand branch; (iii) the `(S,J)` OUTER `A'`-descent supplying `w > 0` and
carrying the accumulated Gram residual to the monomial terminal — the genuine unbuilt gap.
`sjJointResolution` (`RouteMSJResolution`) stays the single named sorry, UNTOUCHED — this tide adds a
sorry-free module.

S2-FREE: measure-preserving product/arrow reindexes + a translation shear + matrix algebra; no
`monomial_rlct`. Axiom footprint: the clean three `[propext, Classical.choice, Quot.sound]`.
-/

namespace DLNFibre.DLN.RLCT

open Matrix MeasureTheory
open scoped BigOperators ENNReal

/-! ## The block decomposition `B ≃ᵐ (P, B₁₂, C) × D` -/

/-- **The outer `(P, B₁₂, C)` block triple** — the front-factor blocks OTHER than the corank `D`-block:
`P` (pivot, `t × t`), `B₁₂` (`t × b`), `C` (`a × t`). -/
abbrev SJOuter (t a b : ℕ) : Type :=
  ((Fin t → Fin t → ℝ) × (Fin t → Fin b → ℝ)) × (Fin a → Fin t → ℝ)

/-- **The column split** `(Fin r → (Fin c ⊕ Fin d) → ℝ) ≃ᵐ (Fin r → Fin c → ℝ) × (Fin r → Fin d → ℝ)`
— split each row's `(Fin c ⊕ Fin d)`-indexed codomain into its left/right column blocks. -/
noncomputable def splitCols (r c d : ℕ) :
    (Fin r → (Fin c ⊕ Fin d) → ℝ) ≃ᵐ (Fin r → Fin c → ℝ) × (Fin r → Fin d → ℝ) :=
  (MeasurableEquiv.arrowCongr' (Equiv.refl (Fin r))
      (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin c ⊕ Fin d => ℝ))).trans
    (MeasurableEquiv.arrowProdEquivProdArrow (Fin c → ℝ) (Fin d → ℝ) (Fin r))

/-- `splitCols` value: the two components read the left / right column entries. -/
theorem splitCols_apply (r c d : ℕ) (f : Fin r → (Fin c ⊕ Fin d) → ℝ) :
    splitCols r c d f
      = (fun i j => f i (Sum.inl j), fun i j => f i (Sum.inr j)) := rfl

/-- `splitCols` is measure-preserving (`arrowCongr'` MP then `arrowProdEquivProdArrow` MP). -/
theorem measurePreserving_splitCols (r c d : ℕ) :
    MeasurePreserving (splitCols r c d)
      (volume : Measure (Fin r → (Fin c ⊕ Fin d) → ℝ)) volume := by
  unfold splitCols
  refine MeasurePreserving.trans ?_
    (volume_measurePreserving_arrowProdEquivProdArrow (Fin c → ℝ) (Fin d → ℝ) (Fin r))
  exact volume_preserving_arrowCongr' (Equiv.refl (Fin r))
    (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin c ⊕ Fin d => ℝ))
    (volume_measurePreserving_sumPiEquivProdPi (fun _ : Fin c ⊕ Fin d => ℝ))

/-- **The block decomposition** `((Fin t ⊕ Fin a) → (Fin t ⊕ Fin b) → ℝ) ≃ᵐ SJOuter t a b × (Fin a →
Fin b → ℝ)`: split rows into top/bottom (`sumPiEquivProdPi`), split each into left/right columns
(`splitCols`), reassociate to place the corank `D`-block `(a × b)` last. -/
noncomputable def blockSplitD (t a b : ℕ) :
    ((Fin t ⊕ Fin a) → (Fin t ⊕ Fin b) → ℝ) ≃ᵐ SJOuter t a b × (Fin a → Fin b → ℝ) :=
  (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin t ⊕ Fin a => (Fin t ⊕ Fin b) → ℝ)).trans
    ((MeasurableEquiv.prodCongr (splitCols t t b) (splitCols a t b)).trans
      (MeasurableEquiv.prodAssoc (α := (Fin t → Fin t → ℝ) × (Fin t → Fin b → ℝ))
        (β := Fin a → Fin t → ℝ) (γ := Fin a → Fin b → ℝ)).symm)

/-- `blockSplitD` is measure-preserving. -/
theorem measurePreserving_blockSplitD (t a b : ℕ) :
    MeasurePreserving (blockSplitD t a b)
      (volume : Measure ((Fin t ⊕ Fin a) → (Fin t ⊕ Fin b) → ℝ)) volume := by
  unfold blockSplitD
  refine MeasurePreserving.trans
    (volume_measurePreserving_sumPiEquivProdPi (fun _ : Fin t ⊕ Fin a => (Fin t ⊕ Fin b) → ℝ)) ?_
  refine MeasurePreserving.trans ?_
    (volume_preserving_prodAssoc (α₁ := (Fin t → Fin t → ℝ) × (Fin t → Fin b → ℝ))
      (β₁ := Fin a → Fin t → ℝ) (γ₁ := Fin a → Fin b → ℝ)).symm
  exact (measurePreserving_splitCols t t b).prod (measurePreserving_splitCols a t b)

/-- **The forward readback** — `blockSplitD B` reads the four blocks of `B`: `(P, B₁₂, C)` (the outer
triple) and `D` (the corank block). All four components are `toFun`s, so this reduces by `rfl`. -/
theorem blockSplitD_apply (t a b : ℕ) (B : (Fin t ⊕ Fin a) → (Fin t ⊕ Fin b) → ℝ) :
    blockSplitD t a b B
      = (((fun i j => B (Sum.inl i) (Sum.inl j), fun i j => B (Sum.inl i) (Sum.inr j)),
          fun i j => B (Sum.inr i) (Sum.inl j)), fun i j => B (Sum.inr i) (Sum.inr j)) := by
  simp only [blockSplitD, MeasurableEquiv.coe_trans, Function.comp_apply,
    MeasurableEquiv.coe_sumPiEquivProdPi, Equiv.sumPiEquivProdPi_apply, MeasurableEquiv.prodAssoc]
  rfl

/-- **The reconstruction** — `blockSplitD.symm (x, D)` is the block matrix with blocks `(P, B₁₂, C, D)`:
`Matrix.of (blockSplitD.symm (x, D)) = fromBlocks (of x.1.1) (of x.1.2) (of x.2) (of D)`. Exhibits the
`fromBlocks` matrix as the preimage: `blockSplitD` of the `fromBlocks`-function returns `(x, D)`
(forward readback + `fromBlocks_apply`), so its `.symm` is that function. -/
theorem of_blockSplitD_symm_eq_fromBlocks (t a b : ℕ)
    (x : SJOuter t a b) (D : Fin a → Fin b → ℝ) :
    Matrix.of ((blockSplitD t a b).symm (x, D))
      = Matrix.fromBlocks (Matrix.of x.1.1) (Matrix.of x.1.2) (Matrix.of x.2) (Matrix.of D) := by
  obtain ⟨⟨P, B12⟩, C⟩ := x
  have hfwd : blockSplitD t a b
      (fun I J => Matrix.fromBlocks (Matrix.of P) (Matrix.of B12) (Matrix.of C) (Matrix.of D) I J)
      = (((P, B12), C), D) := by
    rw [blockSplitD_apply]
    simp only [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
      Matrix.fromBlocks_apply₂₂, Matrix.of_apply]
  have hsymm : (blockSplitD t a b).symm (((P, B12), C), D)
      = (fun I J => Matrix.fromBlocks (Matrix.of P) (Matrix.of B12) (Matrix.of C) (Matrix.of D) I J) :=
    by rw [← hfwd, MeasurableEquiv.symm_apply_apply]
  rw [hsymm]; rfl

/-! ## The freed Schur loss and the block shift -/

/-- **The block shift** `C · P⁻¹ · B₁₂` (as a `Fin a → Fin b → ℝ` function) — the pivot-determined
correction that the corank block `D` is translated by to expose `Γ = D − C·P⁻¹·B₁₂`. -/
noncomputable def schurShift {t a b : ℕ} (x : SJOuter t a b) : Fin a → Fin b → ℝ :=
  fun i j => (Matrix.of x.2 * (Matrix.of x.1.1)⁻¹ * Matrix.of x.1.2) i j

/-- **The freed Schur loss** — the cross-coupled Schur loss with the corank block `Γ` as an
INDEPENDENT argument (not the derived `D − C·P⁻¹·B₁₂`): the pivot energy `frobSq (P·Q̃ₚ)` (`Γ`-free)
plus the corank energy `frobSq (C·Q̃ₚ + Γ·Q_b)`, `Q̃ₚ = Q_p + P⁻¹·B₁₂·Q_b`, `P = of x.1.1`, `B₁₂ = of
x.1.2`, `C = of x.2`. -/
noncomputable def freedSchurLoss {t a b q : ℕ}
    (x : SJOuter t a b) (Γ : Fin a → Fin b → ℝ) (Q : Matrix (Fin t ⊕ Fin b) (Fin q) ℝ) : ℝ :=
  frobSq (Matrix.of x.1.1 * (Q.submatrix Sum.inl id
      + (Matrix.of x.1.1)⁻¹ * Matrix.of x.1.2 * Q.submatrix Sum.inr id))
    + frobSq (Matrix.of x.2 * (Q.submatrix Sum.inl id
        + (Matrix.of x.1.1)⁻¹ * Matrix.of x.1.2 * Q.submatrix Sum.inr id)
      + Matrix.of Γ * Q.submatrix Sum.inr id)

/-- **The shear-substitution identity (pointwise).** With the corank block translated `D = Γ + C·P⁻¹·B₁₂`
(so its Schur complement `Γ_schur = D − C·P⁻¹·B₁₂ = Γ`), the Schur block loss of the reconstructed
block matrix is the freed Schur loss: `schurLoss (of (blockSplitD.symm (x, Γ + schurShift x))) Q =
freedSchurLoss x Γ Q`. The block-shift cancellation `(of Γ + C·P⁻¹·B₁₂) − C·P⁻¹·B₁₂ = of Γ`
(`add_sub_cancel_right`) collapses the Schur complement to the free `Γ`. -/
theorem schurLoss_of_blockSplitD_symm_shift {t a b q : ℕ}
    (x : SJOuter t a b) (Γ : Fin a → Fin b → ℝ) (Q : Matrix (Fin t ⊕ Fin b) (Fin q) ℝ) :
    schurLoss (Matrix.of ((blockSplitD t a b).symm (x, Γ + schurShift x))) Q
      = freedSchurLoss x Γ Q := by
  rw [of_blockSplitD_symm_eq_fromBlocks]
  have hblk₁₁ : (Matrix.fromBlocks (Matrix.of x.1.1) (Matrix.of x.1.2) (Matrix.of x.2)
      (Matrix.of (Γ + schurShift x))).toBlocks₁₁ = Matrix.of x.1.1 := rfl
  have hblk₁₂ : (Matrix.fromBlocks (Matrix.of x.1.1) (Matrix.of x.1.2) (Matrix.of x.2)
      (Matrix.of (Γ + schurShift x))).toBlocks₁₂ = Matrix.of x.1.2 := rfl
  have hblk₂₁ : (Matrix.fromBlocks (Matrix.of x.1.1) (Matrix.of x.1.2) (Matrix.of x.2)
      (Matrix.of (Γ + schurShift x))).toBlocks₂₁ = Matrix.of x.2 := rfl
  have hblk₂₂ : (Matrix.fromBlocks (Matrix.of x.1.1) (Matrix.of x.1.2) (Matrix.of x.2)
      (Matrix.of (Γ + schurShift x))).toBlocks₂₂ = Matrix.of (Γ + schurShift x) := rfl
  -- the Schur complement collapses to `of Γ`.
  have hcompl : Matrix.of (Γ + schurShift x)
      - Matrix.of x.2 * (Matrix.of x.1.1)⁻¹ * Matrix.of x.1.2 = Matrix.of Γ := by
    ext i j
    simp only [schurShift, Matrix.sub_apply, Matrix.of_apply, Pi.add_apply]
    ring
  unfold schurLoss freedSchurLoss
  rw [hblk₁₁, hblk₁₂, hblk₂₁, hblk₂₂, hcompl]

/-! ## The outer `(P, B₁₂, C)` domain and the block-decomposition preimage -/

/-- **The outer domain** — the `(P, B₁₂, C)`-triples whose three blocks lie in the `[−T, T]` box AND
whose pivot block `P` is a unit (the chart condition `IsUnit toBlocks₁₁`, which reads only `P`). -/
def outerDom (t a b : ℕ) (T : ℝ) : Set (SJOuter t a b) :=
  {x | (∀ i j, x.1.1 i j ∈ Set.Icc (-T) T) ∧ (∀ i j, x.1.2 i j ∈ Set.Icc (-T) T)
    ∧ (∀ i j, x.2 i j ∈ Set.Icc (-T) T) ∧ IsUnit (Matrix.of x.1.1)}

/-- The outer domain is measurable (finite box intersections + the invertible-pivot locus). -/
theorem measurableSet_outerDom (t a b : ℕ) (T : ℝ) : MeasurableSet (outerDom t a b T) := by
  have hbox {r c : ℕ} (proj : SJOuter t a b → (Fin r → Fin c → ℝ)) (hproj : Measurable proj) :
      MeasurableSet {x : SJOuter t a b | ∀ i j, proj x i j ∈ Set.Icc (-T) T} := by
    have : {x : SJOuter t a b | ∀ i j, proj x i j ∈ Set.Icc (-T) T}
        = ⋂ (i : Fin r), ⋂ (j : Fin c), {x | proj x i j ∈ Set.Icc (-T) T} := by
      ext x; simp only [Set.mem_iInter, Set.mem_setOf_eq]
    rw [this]
    exact MeasurableSet.iInter (fun i => MeasurableSet.iInter (fun j =>
      (((measurable_pi_apply j).comp ((measurable_pi_apply i).comp hproj))) measurableSet_Icc))
  have hP : Measurable (fun x : SJOuter t a b => x.1.1) :=
    (measurable_fst.comp measurable_fst)
  have hB12 : Measurable (fun x : SJOuter t a b => x.1.2) :=
    (measurable_snd.comp measurable_fst)
  have hC : Measurable (fun x : SJOuter t a b => x.2) := measurable_snd
  have hU : MeasurableSet {x : SJOuter t a b | IsUnit (Matrix.of x.1.1)} := by
    have hdet : Measurable (fun x : SJOuter t a b => (Matrix.of x.1.1).det) := by
      refine (Continuous.matrix_det ?_).measurable.comp hP
      exact continuous_matrix (fun i j => (continuous_apply j).comp (continuous_apply i))
    have hEq : {x : SJOuter t a b | IsUnit (Matrix.of x.1.1)}
        = {x | (Matrix.of x.1.1).det ≠ 0} := by
      ext x; exact (Matrix.isUnit_iff_isUnit_det _).trans isUnit_iff_ne_zero
    rw [hEq]; exact hdet (measurableSet_singleton (0 : ℝ)).compl
  exact ((hbox _ hP).inter ((hbox _ hB12).inter ((hbox _ hC).inter hU)))

/-- **The block-decomposition preimage.** `blockSplitD` pulls the product `outerDom ×ˢ (D-box)` back to
the block box ∩ invertible-pivot locus: `blockSplitD ⁻¹' (outerDom ×ˢ genBox) = genBox ∩ {IsUnit
toBlocks₁₁}`. Each of the four block conditions matches an entry-block of `B` (`blockSplitD_apply`), and
the `IsUnit P` on the outer factor is `IsUnit (toBlocks₁₁ B)` (`toBlocks₁₁ B = of (P-entries of B)`). -/
theorem blockSplitD_preimage_outerDom (t a b : ℕ) (T : ℝ) :
    blockSplitD t a b ⁻¹' (outerDom t a b T ×ˢ genBox (Fin a) (Fin b) T)
      = genBox (Fin t ⊕ Fin a) (Fin t ⊕ Fin b) T ∩ {B | IsUnit (Matrix.toBlocks₁₁ B)} := by
  ext B
  simp only [Set.mem_preimage, Set.mem_prod, Set.mem_inter_iff, Set.mem_setOf_eq,
    blockSplitD_apply, outerDom, genBox]
  constructor
  · rintro ⟨⟨hP, hB12, hC, hU⟩, hD⟩
    refine ⟨fun I J => ?_, hU⟩
    cases I with
    | inl i => cases J with
      | inl j => exact hP i j
      | inr j => exact hB12 i j
    | inr i => cases J with
      | inl j => exact hC i j
      | inr j => exact hD i j
  · rintro ⟨hbox, hU⟩
    exact ⟨⟨fun i j => hbox (Sum.inl i) (Sum.inl j), fun i j => hbox (Sum.inl i) (Sum.inr j),
      fun i j => hbox (Sum.inr i) (Sum.inl j), hU⟩, fun i j => hbox (Sum.inr i) (Sum.inr j)⟩

/-! ## The shear identity — the Schur block chart integral with `Γ` freed -/

/-- **The shear identity (EQUALITY; the corank block `Γ` freed).** The cross-coupled Schur block chart
integral (from the banked weld) equals the OUTER integral, over the `(P, B₁₂, C)`-box ∩ `{IsUnit P}`, of
the INNER integral over the shear-image box `{Γ | Γ + C·P⁻¹·B₁₂ ∈ box}` of the FREED Schur loss
`(freedSchurLoss x Γ Q)^{−c'}` — `Γ` now an INDEPENDENT integration variable (not the derived Schur
complement `D − C·P⁻¹·B₁₂`).

The route (all measure-preserving, no finiteness or branch conditions): transport through the MP block
decomposition `blockSplitD` (`setLIntegral_comp_preimage_emb`, domain factorization
`blockSplitD_preimage_outerDom`); Tonelli split off the inner `D`-block (`setLIntegral_prod`, its
`AEMeasurable` supplied a.e. by the chart identity `frobSq (B·Q) = schurLoss B Q` on `{IsUnit
toBlocks₁₁}` — the continuous `frobSq (B·Q)` sidesteps the matrix inverse); and the per-outer
translation `D = Γ + C·P⁻¹·B₁₂` (`measurePreserving_add_right`, no measurability), whose substitution
collapses the Schur complement to the free `Γ` (`schurLoss_of_blockSplitD_symm_shift`). -/
theorem chartInner_schurShearFree_eq {t a b q : ℕ}
    (Q : Matrix (Fin t ⊕ Fin b) (Fin q) ℝ) (c' T : ℝ) :
    ∫⁻ B in genBox (Fin t ⊕ Fin a) (Fin t ⊕ Fin b) T ∩ {B | IsUnit (Matrix.toBlocks₁₁ B)},
        ENNReal.ofReal ((schurLoss (Matrix.of B) Q) ^ (-c'))
      = ∫⁻ x in outerDom t a b T,
          ∫⁻ Γ in {Γ : Fin a → Fin b → ℝ | Γ + schurShift x ∈ genBox (Fin a) (Fin b) T},
            ENNReal.ofReal ((freedSchurLoss x Γ Q) ^ (-c')) := by
  set F : SJOuter t a b × (Fin a → Fin b → ℝ) → ℝ≥0∞ :=
    fun y => ENNReal.ofReal ((schurLoss (Matrix.of ((blockSplitD t a b).symm y)) Q) ^ (-c')) with hF
  -- `F'`: the continuous chart-form (frobSq of a product — no matrix inverse), used only for `F`'s
  -- a.e.-measurability on the chart domain.
  have hF'meas : Measurable (fun y : SJOuter t a b × (Fin a → Fin b → ℝ) =>
      ENNReal.ofReal ((frobSq (Matrix.of ((blockSplitD t a b).symm y) * Q)) ^ (-c'))) := by
    apply ENNReal.measurable_ofReal.comp
    apply Measurable.comp (g := fun r : ℝ => r ^ (-c')) (by fun_prop)
    have hof : Continuous (fun B : (Fin t ⊕ Fin a) → (Fin t ⊕ Fin b) → ℝ => (Matrix.of B)) :=
      continuous_matrix (fun I J => (continuous_apply J).comp (continuous_apply I))
    have hcont : Continuous (fun B : (Fin t ⊕ Fin a) → (Fin t ⊕ Fin b) → ℝ =>
        frobSq (Matrix.of B * Q)) := by
      have hmul := hof.matrix_mul (continuous_const (y := Q))
      unfold frobSq
      exact continuous_finset_sum _ (fun i _ => continuous_finset_sum _
        (fun j _ => ((hmul.matrix_elem i j).pow 2)))
    exact hcont.measurable.comp (blockSplitD t a b).symm.measurable
  -- transport LHS through `blockSplitD` (MP) + domain factorization.
  have hpre := (measurePreserving_blockSplitD t a b).setLIntegral_comp_preimage_emb
    (MeasurableEquiv.measurableEmbedding (blockSplitD t a b)) F
    (outerDom t a b T ×ˢ genBox (Fin a) (Fin b) T)
  rw [blockSplitD_preimage_outerDom] at hpre
  have hLHS :
      ∫⁻ B in genBox (Fin t ⊕ Fin a) (Fin t ⊕ Fin b) T ∩ {B | IsUnit (Matrix.toBlocks₁₁ B)},
          ENNReal.ofReal ((schurLoss (Matrix.of B) Q) ^ (-c'))
        = ∫⁻ y in outerDom t a b T ×ˢ genBox (Fin a) (Fin b) T, F y := by
    rw [← hpre]
    refine setLIntegral_congr_fun
      ((measurableSet_genBox T).inter measurableSet_isUnit_toBlocks₁₁) (fun B _ => ?_)
    simp only [hF, MeasurableEquiv.symm_apply_apply]
  rw [hLHS, Measure.volume_eq_prod (SJOuter t a b) (Fin a → Fin b → ℝ),
    setLIntegral_prod F ?_]
  · -- inner shear per outer `x`.
    refine setLIntegral_congr_fun (measurableSet_outerDom t a b T) (fun x _ => ?_)
    have hshear := (measurePreserving_add_right (volume : Measure (Fin a → Fin b → ℝ))
        (schurShift x)).setLIntegral_comp_preimage_emb
      (measurableEmbedding_addRight (schurShift x)) (fun D => F (x, D))
      (genBox (Fin a) (Fin b) T)
    rw [← hshear]
    refine setLIntegral_congr_fun ((measurableSet_genBox T).preimage (by fun_prop))
      (fun Γ _ => ?_)
    simp only [hF, schurLoss_of_blockSplitD_symm_shift]
  · -- `F` is a.e.-measurable on the chart domain: `F = F'` there (chart identity `frobSq = schurLoss`).
    refine AEMeasurable.congr hF'meas.aemeasurable ?_
    refine (ae_restrict_iff'
      ((measurableSet_outerDom t a b T).prod (measurableSet_genBox T))).mpr
      (ae_of_all _ (fun y hy => ?_))
    obtain ⟨x, D⟩ := y
    have hyU : IsUnit (Matrix.of x.1.1) := (Set.mem_prod.mp hy).1.2.2.2
    have hblk : IsUnit (Matrix.of ((blockSplitD t a b).symm (x, D))).toBlocks₁₁ := by
      rw [of_blockSplitD_symm_eq_fromBlocks]; exact hyU
    simp only [hF]
    rw [frobSq_schur_split_inv (Matrix.of ((blockSplitD t a b).symm (x, D))) hblk Q]

end DLNFibre.DLN.RLCT
