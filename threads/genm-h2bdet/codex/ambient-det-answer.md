**Verdict:** for opaque dependent block widths, the cleanest Mathlib route is **block-triangular determinant on a Σ-indexed matrix**, not `LinearMap.det_pi`.

**Ranked Routes**

1. **Best: `Matrix.BlockTriangular.det_fintype` on the reindexed Jacobian.**
   Reindex `Fin N` to `ChartIdx`, set
   ```lean
   A := LinearMap.toMatrix' Dchart
   ```
   where `Dchart` is the conjugated derivative on `ChartIdx → ℝ`. Prove:
   ```lean
   htri : A.BlockTriangular Sigma.fst
   ```
   then use:
   ```lean
   Matrix.BlockTriangular.det_fintype htri
   ```
   This gives:
   ```lean
   A.det = ∏ k : Fin L, (A.toSquareBlock Sigma.fst k).det
   ```
   This is the Mathlib theorem meant for opaque Σ-partitions. Exact verified names: `Matrix.BlockTriangular.det_fintype`, `Matrix.toSquareBlock`, `Matrix.det_reindex_self`, `LinearMap.det_toMatrix'`, `LinearMap.det_conj`.

2. **Good if you package it: derive/use a local `det_blockDiagonal'` lemma.**
   Mathlib has dependent:
   ```lean
   Matrix.blockDiagonal'
   Matrix.blockTriangular_blockDiagonal'
   ```
   but **no direct `Matrix.det_blockDiagonal'` theorem** in v4.29. `Matrix.det_blockDiagonal` exists only for equal-sized homogeneous blocks. For dependent blocks, prove the product theorem from:
   ```lean
   Matrix.blockTriangular_blockDiagonal'
   Matrix.BlockTriangular.det_fintype
   ```
   This is fine, but the `toSquareBlock` subtype casts are the main nuisance.

3. **Usually not applicable: `LinearMap.det_pi`.**
   Verified:
   ```lean
   LinearMap.det_pi
   ```
   but it is homogeneous:
   ```lean
   f : ι → M →ₗ[R] M
   ```
   Your boundary fibers are dependent:
   ```lean
   B k := Fin (schurDim k) ⊕ Fin (liftDim k)
   ```
   so after `Σ → Π` curry you get `(k : Fin L) → (B k → ℝ)`, not `Fin L → M`. Thus `LinearMap.det_pi` is only clean if all block spaces are definitionally the same type, which they are not.

**Triangular Shortcut**

A pure `Matrix.det_of_upperTriangular` route fails unless each `kLens` Jacobian is triangular in your chosen total order. It is not enough that the global map is block diagonal.

The diagonal bookkeeping would give:

- spectator diagonal entries: `1`;
- K-core diagonal entries: partial derivatives of `kLens K i j` with respect to the same K-coordinate.

But the determinant of the K-core block is **not** generally the product of those diagonal entries, because `kLens` has within-core off-diagonal Jacobian entries. The correct statement is block triangular with arbitrary square diagonal blocks, not scalar triangular.

So use:
```lean
Matrix.BlockTriangular.det_fintype
```
not:
```lean
Matrix.det_of_upperTriangular
```
except inside some already-proved triangular factorization of `kLens`.

**Concrete Plan**

Use the chart reindex carefully: `funCongrLeft` is contravariant. For
```lean
chartIdxEquiv : Fin N ≃ ChartIdx
```
the flat-to-chart equivalence is likely:
```lean
Echart : (Fin N → ℝ) ≃ₗ[ℝ] (ChartIdx → ℝ) :=
  LinearEquiv.funCongrLeft ℝ ℝ chartIdxEquiv.symm
```

Then define:
```lean
D := (fderiv ℝ kLDU y).toLinearMap

Dchart :=
  (Echart : _ →ₗ[ℝ] _) ∘ₗ D ∘ₗ (Echart.symm : _ →ₗ[ℝ] _)
```

Use:
```lean
LinearMap.det_conj D Echart
```
to replace `det D` by `det Dchart`, and:
```lean
rw [← LinearMap.det_toMatrix' Dchart]
```

For the matrix:
```lean
A := LinearMap.toMatrix' Dchart
```
prove block triangular by entry computation:
```lean
htri : A.BlockTriangular Sigma.fst
```
This only requires cross-boundary derivatives vanish.

Then:
```lean
have hdet := Matrix.BlockTriangular.det_fintype htri
```

For each block `k`, identify
```lean
A.toSquareBlock Sigma.fst k
```
with the natural per-boundary Jacobian on
```lean
B k := Fin (schurDim k) ⊕ Fin (liftDim k)
```
using an equivalence
```lean
{c : ChartIdx // c.1 = k} ≃ B k
```
and `Matrix.det_reindex_self`.

Inside each boundary block, split K-core vs spectators. Best is a linear equivalence:
```lean
(B k → ℝ) ≃ₗ[ℝ] ((Fin (t_k * t_k) → ℝ) × (SpectatorIdx k → ℝ))
```
then conjugate the block derivative to:
```lean
(fderiv ℝ kLens (readK y k)).toLinearMap.prodMap LinearMap.id
```
Use:
```lean
LinearMap.det_prodMap
LinearMap.det_id
```
and your banked:
```lean
kLens_abs_det (readK y k)
```

Main cast landmines:

- `{c : ChartIdx // c.1 = k}` is not defeq to `B k`;
- `Fin (t_k * t_k)` is not defeq to `Fin t_k × Fin t_k`;
- `funCongrLeft` direction needs `.symm`;
- avoid expecting `LinearMap.det_pi` to handle dependent block widths.

**Bounded vs Wall**

This is bounded, not a wall, if you add one local lemma hiding the Σ-block determinant/cast work. Expect roughly **150-300 lines** if the derivative-entry zero facts are already available. Without that helper lemma, the theorem will be cluttered by subtype/cast rewrites, but Mathlib v4.29 has the determinant machinery you need.