import DLNFibre.DLN.RLCT.Validate.RouteMChainBlock
import DLNFibre.DLN.RLCT.Validate.RouteMSchurFrameDet

/-!
# `RouteMGenChainBridge` — Phase B2 bounded sub-pieces (the `chainA`↔flat-frame bridge + det-1 chaining)

The bounded, immediately-bankable sub-pieces of Phase B2 (the design's `threads/36-…/design.md` §3a +
the decorrelated-Codex re-scope `threads/36-…/codex/route-… / b2-…`): the opaque-width `chainA`/`chainQ`
ENTRY LAWS (generalizing the `(3,3,3,3)` probe `chainA_213_entry` to arbitrary `t`/`c`/`M'`) and the
DET-1 chaining map.

These are the mechanical bridge from the abstract `chainA`/`chainQ` (the rate chart's layers) to the
explicit block rows that the flat-frame det factorization (`Q · ∏ chain_s · ∏ Schur_s · ∏ LDU_s · radial`)
consumes — `chainA`'s `finSplit` reindex resolves to the kept/lift block partition via
`finSumFinEquiv_symm_apply_{castAdd,natAdd}`. The det-1 fact `chainUnit_det` confirms the unit-triangular
chaining `(W, C) ↦ (W, C − N·W)` contributes determinant `1` (the cert's `G_s⁻¹` chaining), so the chart
det is carried entirely by the Schur/LDU/radial factors.

NB the full `phiFlat_abs_det` is NOT a bounded build from here (the prefix-fold scaffold + the global
chart-equality over opaque widths remain — Codex-confirmed multi-pass, `design.md` Phase B2/B3); these are
the bounded bricks it stands on.

* `chainA_apply_castAdd` / `chainA_apply_natAdd` — the kept/lift row laws of `chainA` (opaque widths).
* `chainQ_apply_castAdd` / `chainQ_apply_natAdd` — the `chainQ` column laws.
* `chainUnitMap` / `chainUnit_det` — the det-1 chaining map `(W, C) ↦ (W, C − N·W)`.

Axiom-clean `[propext, Classical.choice, Quot.sound]` (pure matrix algebra; no S2).
-/

namespace DLNFibre.DLN.RLCT

open Matrix LinearMap

variable {𝕜 : Type*} [CommRing 𝕜]

/-! ## The `chainA` entry laws (opaque widths) -/

/-- **`chainA` kept-row law**: `chainA h N W C (cast (castAdd i)) j = (C − N·W) i j` — the first `t` rows
of the lift column `[C − N·W ; W]` (the `finSplit` `castAdd` block). The opaque-width generalization of
the `(3,3,3,3)` probe `chainA_213_entry`'s kept rows. -/
theorem chainA_apply_castAdd {M' t c m' : ℕ} (h : t + c = M') (N : Matrix (Fin t) (Fin c) 𝕜)
    (W : Matrix (Fin c) (Fin m') 𝕜) (C : Matrix (Fin t) (Fin m') 𝕜) (i : Fin t) (j : Fin m') :
    chainA h N W C (Fin.cast h (Fin.castAdd c i)) j = (C - N * W) i j := by
  simp only [chainA, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.of_apply, Equiv.refl_symm,
    Equiv.refl_apply, Equiv.symm_symm]
  rw [show finSplit (show t ≤ M' by omega) (Fin.cast h (Fin.castAdd c i)) = Sum.inl i from by
    simp only [finSplit, Equiv.trans_apply, finCongr_apply]
    rw [show (Fin.cast (show M' = t + (M' - t) by omega) (Fin.cast h (Fin.castAdd c i)))
          = Fin.castAdd (M' - t) i from by apply Fin.ext; simp]
    exact finSumFinEquiv_symm_apply_castAdd i]
  rfl

/-- **`chainA` lift-row law**: `chainA h N W C (cast (natAdd a)) j = W a j` — the last `c` rows of the
lift column are the lift `W` (the `finSplit` `natAdd` block). -/
theorem chainA_apply_natAdd {M' t c m' : ℕ} (h : t + c = M') (N : Matrix (Fin t) (Fin c) 𝕜)
    (W : Matrix (Fin c) (Fin m') 𝕜) (C : Matrix (Fin t) (Fin m') 𝕜) (a : Fin c) (j : Fin m') :
    chainA h N W C (Fin.cast h (Fin.natAdd t a)) j = W a j := by
  simp only [chainA, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.of_apply, Equiv.refl_symm,
    Equiv.refl_apply, Equiv.symm_symm]
  rw [show finSplit (show t ≤ M' by omega) (Fin.cast h (Fin.natAdd t a))
        = Sum.inr (Fin.cast (by omega) a) from by
    simp only [finSplit, Equiv.trans_apply, finCongr_apply]
    rw [show (Fin.cast (show M' = t + (M' - t) by omega) (Fin.cast h (Fin.natAdd t a)))
          = Fin.natAdd t (Fin.cast (by omega) a) from by apply Fin.ext; simp]
    exact finSumFinEquiv_symm_apply_natAdd _]
  simp only [Sum.elim_inr, Matrix.submatrix_apply]
  congr 1

/-! ## The `chainQ` column laws (opaque widths) -/

/-- **`chainQ` kept-column law**: `chainQ h N i (cast (castAdd j)) = (1 : t×t) i j` — the first `t`
columns of the chaining row `[I | N]` are the identity. -/
theorem chainQ_apply_castAdd {M' t c : ℕ} (h : t + c = M') (N : Matrix (Fin t) (Fin c) 𝕜)
    (i : Fin t) (j : Fin t) :
    chainQ h N i (Fin.cast h (Fin.castAdd c j)) = (1 : Matrix (Fin t) (Fin t) 𝕜) i j := by
  simp only [chainQ, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.of_apply, Equiv.refl_symm,
    Equiv.refl_apply, Equiv.symm_symm]
  rw [show finSplit (show t ≤ M' by omega) (Fin.cast h (Fin.castAdd c j)) = Sum.inl j from by
    simp only [finSplit, Equiv.trans_apply, finCongr_apply]
    rw [show (Fin.cast (show M' = t + (M' - t) by omega) (Fin.cast h (Fin.castAdd c j)))
          = Fin.castAdd (M' - t) j from by apply Fin.ext; simp]
    exact finSumFinEquiv_symm_apply_castAdd j]
  rfl

/-- **`chainQ` residual-column law**: `chainQ h N i (cast (natAdd a)) = N i a` — the last `c` columns of
the chaining row `[I | N]` are the residual `N`. -/
theorem chainQ_apply_natAdd {M' t c : ℕ} (h : t + c = M') (N : Matrix (Fin t) (Fin c) 𝕜)
    (i : Fin t) (a : Fin c) :
    chainQ h N i (Fin.cast h (Fin.natAdd t a)) = N i a := by
  simp only [chainQ, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.of_apply, Equiv.refl_symm,
    Equiv.refl_apply, Equiv.symm_symm]
  rw [show finSplit (show t ≤ M' by omega) (Fin.cast h (Fin.natAdd t a))
        = Sum.inr (Fin.cast (by omega) a) from by
    simp only [finSplit, Equiv.trans_apply, finCongr_apply]
    rw [show (Fin.cast (show M' = t + (M' - t) by omega) (Fin.cast h (Fin.natAdd t a)))
          = Fin.natAdd t (Fin.cast (by omega) a) from by apply Fin.ext; simp]
    exact finSumFinEquiv_symm_apply_natAdd _]
  simp only [Sum.elim_inr, Matrix.submatrix_apply]
  congr 1

/-! ## The det-1 chaining map (the cert's unit-triangular `G_s⁻¹`) -/

/-- **The chaining map** `(W, C) ↦ (W, C − N·W)` on `Matrix (Fin c) (Fin m') × Matrix (Fin t) (Fin m')`
— the cert's unit-triangular `G_s⁻¹` chaining (in the `(W, C)` pairing where the coupling goes
second-from-first). A `lowerTri id id (W ↦ −N·W)`. -/
noncomputable def chainUnitMap {t c m' : ℕ} (N : Matrix (Fin t) (Fin c) ℝ) :
    (Matrix (Fin c) (Fin m') ℝ × Matrix (Fin t) (Fin m') ℝ) →ₗ[ℝ]
      (Matrix (Fin c) (Fin m') ℝ × Matrix (Fin t) (Fin m') ℝ) :=
  lowerTri LinearMap.id LinearMap.id
    { toFun := fun W => - (N * W)
      map_add' := by intro a b; rw [Matrix.mul_add, neg_add]
      map_smul' := by intro a b; simp [Matrix.mul_smul] }

/-- **`det (chainUnitMap N) = 1`** — the unit-triangular chaining contributes determinant `1`. The cert's
`G_s⁻¹` det-1 fact; so the chart det is carried by the Schur/LDU/radial factors, not the chaining. -/
theorem chainUnit_det {t c m' : ℕ} (N : Matrix (Fin t) (Fin c) ℝ) :
    LinearMap.det (chainUnitMap (m' := m') N) = 1 := by
  rw [chainUnitMap, lowerTri_det, LinearMap.det_id, one_mul, LinearMap.det_id]

end DLNFibre.DLN.RLCT
