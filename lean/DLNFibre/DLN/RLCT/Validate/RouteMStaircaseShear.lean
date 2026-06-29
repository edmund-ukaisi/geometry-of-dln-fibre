import DLNFibre.DLN.RLCT.Validate.RouteMGenChainBridge

/-!
# `RouteMStaircaseShear` — the opaque-width staircase-shear cast infrastructure (direction 2)

The cast-zone scaffolding for the direction-2 staircase factorization of the unconditional interior-det
headline (`staircase-det-bricks-statement-card.md`, the residual). The determinant must be taken at the
LINEAR-MAP level (iterated `lowerTri_det`), NOT via a single-grading `Matrix.BlockTriangular` (the
input/output partitions genuinely differ — `RouteMGradingObstruction`). This module banks the bottom layer
of cast lemmas that every staircase-block read needs: the inverse-direction evaluation of the canonical
width split `finSplit`.

`finSplit (h : t ≤ M') : Fin M' ≃ Fin t ⊕ Fin (M' − t)` is `(finCongr (M' = t + (M'−t))).trans
finSumFinEquiv.symm`. Its forward `castAdd`/`natAdd` reads are banked (`chainA_apply_*`, via the
`finSplit hle (cast (castAdd i)) = Sum.inl i` shows). The dual we add here is the SYMM direction: the
explicit `Fin M'` index that `finSplit.symm` produces from a `Sum.inl`/`Sum.inr`. This removes the
repeated local `Fin.ext; simp` index-normalization proof currently inlined before every block read.

* `finSplit_symm_inl` / `finSplit_symm_natAdd` — the kept/residual symm reads.

Axiom-clean `[propext, Classical.choice, Quot.sound]` (pure `Fin`/`Equiv` algebra; no analysis).
-/

namespace DLNFibre.DLN.RLCT

open Matrix

/-! ## The `finSplit.symm` evaluation (opaque widths) -/

/-- **`finSplit.symm` on the kept block**: `finSplit (h).symm (Sum.inl i) = Fin.cast (…) (Fin.castAdd c i)`
— the kept directions of the split land in the first `t` ambient slots (the `castAdd` block). The inverse
of `chainA_apply_castAdd`'s `finSplit hle (cast (castAdd i)) = Sum.inl i`; banked here so block reads need
no inline `Fin.ext` normalization. -/
theorem finSplit_symm_inl {t M' : ℕ} (h : t ≤ M') (i : Fin t) :
    (finSplit (M := M') (t := t) h).symm (Sum.inl i)
      = Fin.cast (show t + (M' - t) = M' by omega) (Fin.castAdd (M' - t) i) := by
  simp only [finSplit, Equiv.symm_trans_apply, Equiv.symm_symm, finCongr_symm, finCongr_apply]
  rw [finSumFinEquiv_apply_left]

/-- **`finSplit.symm` on the residual block**: `finSplit (h).symm (Sum.inr a) = Fin.cast (…)
(Fin.natAdd t a)` — the residual directions land in the last `M' − t` ambient slots (the `natAdd` block).
The inverse of `chainA_apply_natAdd`'s residual read. -/
theorem finSplit_symm_inr {t M' : ℕ} (h : t ≤ M') (a : Fin (M' - t)) :
    (finSplit (M := M') (t := t) h).symm (Sum.inr a)
      = Fin.cast (show t + (M' - t) = M' by omega) (Fin.natAdd t a) := by
  simp only [finSplit, Equiv.symm_trans_apply, Equiv.symm_symm, finCongr_symm, finCongr_apply]
  rw [finSumFinEquiv_apply_right]

end DLNFibre.DLN.RLCT
