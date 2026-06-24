**Ranking**

1. **(A) Linear-map/basis route is the cleanest.** Treat `B` as `f := B.mulVecLin : (Fin b → ℝ) →ₗ[ℝ] (Fin a → ℝ)`, where `a = H 0`, `b = H (Fin.last L)`. Then prove the matrix in adapted bases is the rank block, and use basis-change matrices for `P,Q`.

   The main glue lemma is confirmed in v4.29:

   `basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix`

   It gives:
   ```lean
   c.toMatrix c' * LinearMap.toMatrix b' c' f * b'.toMatrix b
     = LinearMap.toMatrix b c f
   ```
   with `b'`,`c'` the old standard bases and `b`,`c` the adapted bases. See [Matrix/Basis.lean](/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/rung0-defs/lean/.lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix/Basis.lean:202).

2. **(B) No one-shot adapted-basis theorem found.** The closest useful APIs are:
   `Submodule.exists_isCompl`, `LinearMap.kerComplementEquivRange`, `Submodule.prodEquivOfIsCompl`, `Module.finBasisOfFinrankEq`, `LinearMap.finrank_range_add_finrank_ker`, and `Submodule.finrank_add_eq_of_isCompl`.

   `Module.Basis.ofSplitExact` exists, but it is not the direct normal-form theorem; it is more natural for quotient/split-exact constructions.

3. **(C) Pure Gaussian elimination is worse.** Mathlib has square transvection diagonalization (`exists_list_transvec_mul_mul_list_transvec_eq_diagonal`), but that is square-matrix API and does not directly give this rectangular rank normal form. Using it here would add embedding/rescaling/rank bookkeeping.

**Recommended Staging**

Let:
```lean
a := H 0
b := H (Fin.last L)
V := Fin b → ℝ
W := Fin a → ℝ
f := B.mulVecLin
```

Use `hB` plus `Matrix.rank` to get:
```lean
finrank ℝ (LinearMap.range f) = r
```
and use `Matrix.rank_le_height`, `Matrix.rank_le_width` to get `r ≤ a`, `r ≤ b`.

Construct:

- `bR : Basis (Fin r) ℝ (LinearMap.range f)` via `Module.finBasisOfFinrankEq`.
- A complement `C` of `ker f`, then `LinearMap.kerComplementEquivRange f : C ≃ₗ[ℝ] LinearMap.range f`.
- Domain first block basis: pull `bR` back to `C`.
- Kernel basis: `Basis (Fin (b-r)) ℝ (ker f)` using rank-nullity.
- Domain adapted basis from `(C × ker f) ≃ₗ V` using `Submodule.prodEquivOfIsCompl` and `Basis.prod`.

For codomain:

- Choose a complement `D` of `range f`.
- Basis of `D` indexed by `Fin (a-r)` using `Submodule.finrank_add_eq_of_isCompl`.
- Codomain adapted basis from `(range f × D) ≃ₗ W`.

Then prove the easy sum-index normal form first:
```lean
LinearMap.toMatrix bDomΣ bCodΣ f
```
has entries `1` on the `(Sum.inl i, Sum.inl i)` block and `0` elsewhere.

**Exact RHS Matching**

Do not try to make the adapted bases directly “morally first `r`” by ad hoc indexing. Build them on sum indices, then reindex:

```lean
eRows : Fin r ⊕ Fin (a-r) ≃ Fin a :=
  finSumFinEquiv.trans (finCongr (by omega))

eCols : Fin r ⊕ Fin (b-r) ≃ Fin b :=
  finSumFinEquiv.trans (finCongr (by omega))
```

Then define:
```lean
bDom := bDomΣ.reindex eCols
bCod := bCodΣ.reindex eRows
```

Prove a small helper:
```lean
LinearMap.toMatrix (bDomΣ.reindex eCols) (bCodΣ.reindex eRows) f
  = (LinearMap.toMatrix bDomΣ bCodΣ f).reindex eRows eCols
```
by `ext i j` and `simp [LinearMap.toMatrix_apply, Module.Basis.reindex_apply]`.

Finally prove the pure Fin arithmetic lemma:
```lean
(J.reindex eRows eCols)
  = Matrix.of fun i j =>
      if (i : ℕ) = (j : ℕ) ∧ (i : ℕ) < r then (1 : ℝ) else 0
```
by cases on `eRows.symm i` and `eCols.symm j`, using `finSumFinEquiv_apply_left/right` and `omega`.

**Basis Change to P,Q**

Let `stdV := Pi.basisFun ℝ (Fin b)` and `stdW := Pi.basisFun ℝ (Fin a)`.

Use:
```lean
P := bCod.toMatrix stdW
Q := stdV.toMatrix bDom
```

Then:
```lean
P * B * Q
= bCod.toMatrix stdW * LinearMap.toMatrix stdV stdW f * stdV.toMatrix bDom
= LinearMap.toMatrix bDom bCod f
```

For `LinearMap.toMatrix stdV stdW f = B`, use `LinearMap.toMatrix_toLin` together with `Matrix.toLin_eq_toLin'` and `Matrix.toLin'_apply'`. I would avoid relying on `LinearMap.toMatrix_eq_toMatrix'`; in v4.29 its printed statement is square-looking, so verify before using.

`IsUnit P` and `IsUnit Q` come from `Module.Basis.invertibleToMatrix` plus `isUnit_of_invertible`.

**Size Estimate**

This is not a 40-line proof. With helper lemmas staged well, expect about **180-250 lines** the first time. The real cost is not linear algebra; it is the two reindexing helpers and Fin arithmetic needed to land exactly on your `Matrix.of` RHS.