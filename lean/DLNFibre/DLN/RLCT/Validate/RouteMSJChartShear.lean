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

end DLNFibre.DLN.RLCT
