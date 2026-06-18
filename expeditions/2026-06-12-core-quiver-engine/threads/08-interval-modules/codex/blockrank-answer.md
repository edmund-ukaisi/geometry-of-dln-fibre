**Typeclass**

Use `[Field k]` for the clean theorem. `Matrix.rank` is defined over `[CommRing k]`, but the proof needs additivity of `finrank` on product ranges. The confirmed lemma `Module.finrank_prod` needs free finite modules under `StrongRankCondition`; over a field the relevant ranges are finite-dimensional subspaces, so instances are automatic. Arbitrary `CommRing` is not clean without extra freeness/finite hypotheses on the two ranges.

**Recommended Route**

Use `mulVecLin`, not `toMatrix`. Reason: rectangular `LinearMap.toMatrix_prodMap` is absent in this pin; only the square endomorphism version is present.

Confirmed lemmas used:

- `Matrix.fromBlocks_mulVec` CONFIRMED
- `LinearEquiv.sumArrowLequivProdArrow` CONFIRMED
- `LinearMap.range_prodMap` CONFIRMED
- `LinearEquiv.finrank_map_eq` CONFIRMED
- `LinearMap.range_comp` CONFIRMED
- `LinearMap.range_comp_of_range_eq_top` CONFIRMED
- `Module.finrank_prod` CONFIRMED
- `Matrix.rank` CONFIRMED

You need a small helper for `Submodule.prod` finrank; no existing `Submodule.finrank_prod` found.

```lean
import Mathlib.LinearAlgebra.Matrix.Rank

open Matrix

namespace Submodule

noncomputable def prodEquivSubtypeProd {R M M' : Type*} [Semiring R]
    [AddCommMonoid M] [Module R M] [AddCommMonoid M'] [Module R M']
    (p : Submodule R M) (q : Submodule R M') :
    p.prod q ≃ₗ[R] p × q where
  toFun x := (⟨x.1.1, x.2.1⟩, ⟨x.1.2, x.2.2⟩)
  invFun y := ⟨(y.1, y.2), by simp⟩
  left_inv x := by ext <;> rfl
  right_inv x := by ext <;> rfl
  map_add' x y := by ext <;> rfl
  map_smul' r x := by ext <;> rfl

@[simp] theorem finrank_prod {R M M' : Type*} [Semiring R]
    [StrongRankCondition R]
    [AddCommMonoid M] [Module R M] [AddCommMonoid M'] [Module R M']
    (p : Submodule R M) (q : Submodule R M')
    [Module.Free R p] [Module.Free R q] [Module.Finite R p] [Module.Finite R q] :
    Module.finrank R (p.prod q) = Module.finrank R p + Module.finrank R q := by
  rw [(prodEquivSubtypeProd p q).finrank_eq, Module.finrank_prod]

end Submodule

theorem rank_fromBlocks_zero_zero
    {k : Type*} [Field k]
    {a b c d : ℕ}
    (A : Matrix (Fin a) (Fin b) k) (B : Matrix (Fin c) (Fin d) k) :
    (Matrix.fromBlocks A 0 0 B).rank = A.rank + B.rank := by
  classical
  let Er := LinearEquiv.sumArrowLequivProdArrow (Fin a) (Fin c) k k
  let Ec := LinearEquiv.sumArrowLequivProdArrow (Fin b) (Fin d) k k
  let f := (Matrix.fromBlocks A 0 0 B).mulVecLin
  let g := A.mulVecLin.prodMap B.mulVecLin

  have hfg : Er.toLinearMap.comp f = g.comp Ec.toLinearMap := by
    apply LinearMap.ext
    intro x
    ext i <;> cases i
    · simp [Er, Ec, f, g, Matrix.fromBlocks_mulVec]; rfl
    · simp [Er, Ec, f, g, Matrix.fromBlocks_mulVec]; rfl

  rw [Matrix.rank, Matrix.rank, Matrix.rank]
  calc
    Module.finrank k (LinearMap.range f)
        = Module.finrank k (Submodule.map Er.toLinearMap (LinearMap.range f)) := by
            rw [LinearEquiv.finrank_map_eq]
    _ = Module.finrank k (LinearMap.range (Er.toLinearMap.comp f)) := by
            rw [LinearMap.range_comp]
    _ = Module.finrank k (LinearMap.range (g.comp Ec.toLinearMap)) := by
            rw [hfg]
    _ = Module.finrank k (LinearMap.range g) := by
            rw [LinearMap.range_comp_of_range_eq_top _ Ec.range]
    _ = Module.finrank k (LinearMap.range A.mulVecLin) +
        Module.finrank k (LinearMap.range B.mulVecLin) := by
            rw [LinearMap.range_prodMap, Submodule.finrank_prod]
```

**Q1**

Exact existing product finrank lemma:

- `Module.finrank_prod` CONFIRMED

Useful adjacent lemmas:

- `LinearEquiv.finrank_eq` CONFIRMED
- `LinearEquiv.finrank_map_eq` CONFIRMED

Not present:

- `Submodule.finrank_prod` CONFIRMED ABSENT by grep.

**Friction Points**

1. Avoid rectangular `toMatrix_prodMap`: absent. Use `mulVecLin` plus `Matrix.fromBlocks_mulVec`.
2. For function spaces over sums, use `LinearEquiv.sumArrowLequivProdArrow`; avoid `Fin (a+c)` until after this lemma, then reindex separately with `Matrix.rank_reindex`.
3. `Module.finrank_prod` does not rewrite `Module.finrank k (p.prod q)` directly. Add the tiny `p.prod q ≃ₗ p × q` helper above.