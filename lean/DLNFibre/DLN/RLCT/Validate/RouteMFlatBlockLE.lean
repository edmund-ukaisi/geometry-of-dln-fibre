import DLNFibre.DLN.RLCT.Validate.RouteMProjV0Gate

/-!
# `RouteMFlatBlockLE` — `flatBlock` as a `LinearEquiv` `SchurInc t r c ≃ₗ Matrix (Fin Trow) (Fin Wcol)`

The gate's `flatBlock` (`RouteMProjV0Gate`) flattens a `SchurInc t r c` tuple `(A,N,X,E)` into the
block matrix `[[A,N],[X,E]] : Matrix (Fin Trow) (Fin Wcol)` (`t + r = Trow`, `t + c = Wcol`). It is a
LINEAR ISOMORPHISM — dimension `t² + tc + rt + rc = (t+r)(t+c)` on both sides, the four blocks
recovered by the row/col split. This module upgrades it to a `LinearEquiv`, the layer-0 OUTPUT reshape
the two-sided staircase `eOut` consumes (`Agen 0`/layer-0 Params matrix ↔ the `SchurInc` increment
output of `schurFrameDeriv`).

* `flatBlockLin` — `flatBlock` as a `LinearMap` (it is entrywise a `Sum.elim` of the 4 block
  projections, hence linear; the same linearity `flatBlock_differentiableAt` uses).
* `unflatBlock` — the inverse: extract the four blocks `(A,N,X,E)` from `[[A,N],[X,E]]` by the
  `castAdd/natAdd` row/col splits.
* `flatBlockLE` — the `LinearEquiv`, via `LinearEquiv.ofLinear` + the round-trip identities (the
  banked `flatBlock_castAdd/natAdd` for one direction, the `Sum.elim` split for the other).

Axiom-clean `[propext, Classical.choice, Quot.sound]` (matrix algebra + finite splits; no analysis).
-/

open Matrix
open scoped BigOperators

namespace DLNFibre.DLN.RLCT

/-! ## `flatBlock` as a linear map, and the un-flatten inverse -/

/-- `flatBlock` as a `LinearMap` on the `SchurInc` increment space. Entrywise a `Sum.elim` of the four
block coordinate projections, so additive + ℝ-homogeneous. -/
noncomputable def flatBlockLin {t r c Trow Wcol : ℕ} (hr : t + r = Trow) (hc : t + c = Wcol) :
    SchurInc t r c →ₗ[ℝ] Matrix (Fin Trow) (Fin Wcol) ℝ where
  toFun := flatBlock hr hc
  map_add' z w := by
    ext i j
    simp only [flatBlock, Matrix.of_apply, Matrix.add_apply]
    rcases finSumFinEquiv.symm (Fin.cast hr.symm i) with i' | a <;>
      rcases finSumFinEquiv.symm (Fin.cast hc.symm j) with j' | b <;>
      simp only [Sum.elim_inl, Sum.elim_inr, Matrix.add_apply, Prod.fst_add, Prod.snd_add]
  map_smul' s z := by
    ext i j
    simp only [flatBlock, Matrix.of_apply, Matrix.smul_apply, RingHom.id_apply]
    rcases finSumFinEquiv.symm (Fin.cast hr.symm i) with i' | a <;>
      rcases finSumFinEquiv.symm (Fin.cast hc.symm j) with j' | b <;>
      simp only [Sum.elim_inl, Sum.elim_inr, Matrix.smul_apply, Prod.smul_fst, Prod.smul_snd,
        smul_eq_mul]

/-- The un-flatten map: extract the four blocks `(A, N, X, E)` from a block matrix `[[A,N],[X,E]]` by
the canonical `castAdd/natAdd` row/col splits. The inverse of `flatBlockLin`. -/
noncomputable def unflatBlock {t r c Trow Wcol : ℕ} (hr : t + r = Trow) (hc : t + c = Wcol)
    (B : Matrix (Fin Trow) (Fin Wcol) ℝ) : SchurInc t r c :=
  (Matrix.of fun i j => B (Fin.cast hr (Fin.castAdd r i)) (Fin.cast hc (Fin.castAdd c j)),
    Matrix.of fun i j => B (Fin.cast hr (Fin.castAdd r i)) (Fin.cast hc (Fin.natAdd t j)),
    Matrix.of fun i j => B (Fin.cast hr (Fin.natAdd t i)) (Fin.cast hc (Fin.castAdd c j)),
    Matrix.of fun i j => B (Fin.cast hr (Fin.natAdd t i)) (Fin.cast hc (Fin.natAdd t j)))

/-- `unflatBlock` as a `LinearMap`. -/
noncomputable def unflatBlockLin {t r c Trow Wcol : ℕ} (hr : t + r = Trow) (hc : t + c = Wcol) :
    Matrix (Fin Trow) (Fin Wcol) ℝ →ₗ[ℝ] SchurInc t r c where
  toFun := unflatBlock hr hc
  map_add' B C := by
    simp only [unflatBlock, Matrix.add_apply]
    rfl
  map_smul' s B := by
    simp only [unflatBlock, Matrix.smul_apply, RingHom.id_apply]
    rfl

/-! ## The round-trips -/

/-- `unflatBlock (flatBlock z) = z` — extracting the four blocks recovers the tuple (each block read
through the matching `castAdd/natAdd` split selects the right `Sum.elim` branch via the banked
`flatBlock_castAdd/natAdd`). -/
theorem unflatBlock_flatBlock {t r c Trow Wcol : ℕ} (hr : t + r = Trow) (hc : t + c = Wcol)
    (z : SchurInc t r c) : unflatBlock hr hc (flatBlock hr hc z) = z := by
  -- componentwise on the 4 blocks
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))
  · ext i j
    show flatBlock hr hc z (Fin.cast hr (Fin.castAdd r i)) (Fin.cast hc (Fin.castAdd c j)) = z.1 i j
    rw [flatBlock_castAdd hr hc z i,
      show Fin.cast hc.symm (Fin.cast hc (Fin.castAdd c j)) = Fin.castAdd c j from by
        apply Fin.ext; simp, finSumFinEquiv_symm_apply_castAdd, Sum.elim_inl]
  · ext i j
    show flatBlock hr hc z (Fin.cast hr (Fin.castAdd r i)) (Fin.cast hc (Fin.natAdd t j))
      = z.2.1 i j
    rw [flatBlock_castAdd hr hc z i,
      show Fin.cast hc.symm (Fin.cast hc (Fin.natAdd t j)) = Fin.natAdd t j from by
        apply Fin.ext; simp, finSumFinEquiv_symm_apply_natAdd, Sum.elim_inr]
  · ext i j
    show flatBlock hr hc z (Fin.cast hr (Fin.natAdd t i)) (Fin.cast hc (Fin.castAdd c j))
      = z.2.2.1 i j
    rw [flatBlock_natAdd hr hc z i,
      show Fin.cast hc.symm (Fin.cast hc (Fin.castAdd c j)) = Fin.castAdd c j from by
        apply Fin.ext; simp, finSumFinEquiv_symm_apply_castAdd, Sum.elim_inl]
  · ext i j
    show flatBlock hr hc z (Fin.cast hr (Fin.natAdd t i)) (Fin.cast hc (Fin.natAdd t j))
      = z.2.2.2 i j
    rw [flatBlock_natAdd hr hc z i,
      show Fin.cast hc.symm (Fin.cast hc (Fin.natAdd t j)) = Fin.natAdd t j from by
        apply Fin.ext; simp, finSumFinEquiv_symm_apply_natAdd, Sum.elim_inr]

/-- `flatBlock (unflatBlock B) = B` — reassembling the four extracted blocks recovers the matrix. Each
entry `(i, j)`: split `i` (row) and `j` (col) by the canonical sum split, then the `flatBlock`
`Sum.elim` selects the block that `unflatBlock` read from exactly that split position. -/
theorem flatBlock_unflatBlock {t r c Trow Wcol : ℕ} (hr : t + r = Trow) (hc : t + c = Wcol)
    (B : Matrix (Fin Trow) (Fin Wcol) ℝ) : flatBlock hr hc (unflatBlock hr hc B) = B := by
  ext i j
  -- decompose row `i` and col `j` by the canonical sum split
  obtain ⟨is, hieq⟩ : ∃ is : Fin t ⊕ Fin r, i = Fin.cast hr (finSumFinEquiv is) :=
    ⟨finSumFinEquiv.symm (Fin.cast hr.symm i), by rw [Equiv.apply_symm_apply]; apply Fin.ext; simp⟩
  obtain ⟨js, hjeq⟩ : ∃ js : Fin t ⊕ Fin c, j = Fin.cast hc (finSumFinEquiv js) :=
    ⟨finSumFinEquiv.symm (Fin.cast hc.symm j), by rw [Equiv.apply_symm_apply]; apply Fin.ext; simp⟩
  subst hieq hjeq
  rcases is with i' | a <;> rcases js with j' | b
  · rw [show (Fin.cast hr (finSumFinEquiv (Sum.inl i')) : Fin Trow)
          = Fin.cast hr (Fin.castAdd r i') from by apply Fin.ext; simp,
        flatBlock_castAdd, show (Fin.cast hc (finSumFinEquiv (Sum.inl j')) : Fin Wcol)
          = Fin.cast hc (Fin.castAdd c j') from by apply Fin.ext; simp,
        show Fin.cast hc.symm (Fin.cast hc (Fin.castAdd c j')) = Fin.castAdd c j' from by
          apply Fin.ext; simp, finSumFinEquiv_symm_apply_castAdd, Sum.elim_inl]
    rfl
  · rw [show (Fin.cast hr (finSumFinEquiv (Sum.inl i')) : Fin Trow)
          = Fin.cast hr (Fin.castAdd r i') from by apply Fin.ext; simp,
        flatBlock_castAdd, show (Fin.cast hc (finSumFinEquiv (Sum.inr b)) : Fin Wcol)
          = Fin.cast hc (Fin.natAdd t b) from by apply Fin.ext; simp,
        show Fin.cast hc.symm (Fin.cast hc (Fin.natAdd t b)) = Fin.natAdd t b from by
          apply Fin.ext; simp, finSumFinEquiv_symm_apply_natAdd, Sum.elim_inr]
    rfl
  · rw [show (Fin.cast hr (finSumFinEquiv (Sum.inr a)) : Fin Trow)
          = Fin.cast hr (Fin.natAdd t a) from by apply Fin.ext; simp,
        flatBlock_natAdd, show (Fin.cast hc (finSumFinEquiv (Sum.inl j')) : Fin Wcol)
          = Fin.cast hc (Fin.castAdd c j') from by apply Fin.ext; simp,
        show Fin.cast hc.symm (Fin.cast hc (Fin.castAdd c j')) = Fin.castAdd c j' from by
          apply Fin.ext; simp, finSumFinEquiv_symm_apply_castAdd, Sum.elim_inl]
    rfl
  · rw [show (Fin.cast hr (finSumFinEquiv (Sum.inr a)) : Fin Trow)
          = Fin.cast hr (Fin.natAdd t a) from by apply Fin.ext; simp,
        flatBlock_natAdd, show (Fin.cast hc (finSumFinEquiv (Sum.inr b)) : Fin Wcol)
          = Fin.cast hc (Fin.natAdd t b) from by apply Fin.ext; simp,
        show Fin.cast hc.symm (Fin.cast hc (Fin.natAdd t b)) = Fin.natAdd t b from by
          apply Fin.ext; simp, finSumFinEquiv_symm_apply_natAdd, Sum.elim_inr]
    rfl

/-- **`flatBlock` as a `LinearEquiv`** `SchurInc t r c ≃ₗ Matrix (Fin Trow) (Fin Wcol)` — the layer-0
output reshape (`Agen 0`/layer-0 Params matrix ↔ the `SchurInc` increment output). Via
`LinearEquiv.ofLinear` + the two round-trips. -/
noncomputable def flatBlockLE {t r c Trow Wcol : ℕ} (hr : t + r = Trow) (hc : t + c = Wcol) :
    SchurInc t r c ≃ₗ[ℝ] Matrix (Fin Trow) (Fin Wcol) ℝ :=
  LinearEquiv.ofLinear (flatBlockLin hr hc) (unflatBlockLin hr hc)
    (by ext B i j; exact congrFun (congrFun (flatBlock_unflatBlock hr hc B) i) j)
    (by
      refine LinearMap.ext (fun z => ?_)
      exact unflatBlock_flatBlock hr hc z)

end DLNFibre.DLN.RLCT
