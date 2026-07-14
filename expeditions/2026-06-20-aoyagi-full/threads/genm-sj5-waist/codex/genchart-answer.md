## 1. Verdict

Choose Route A, but compute the determinant blockwise rather than through a scalar Jacobian matrix. [FACT] The requested theorem permits arbitrary `g`, while Route B’s Tonelli proof needs at least `AEMeasurable` joint integrands (`setLIntegral_prod`) and its Haar-to-lintegral step uses `lintegral_map`, requiring measurability. Route A retains the working single application of `lintegral_image_eq_lintegral_abs_det_fderiv_mul`, and this repository already contains the width-generic determinant theorem needed for the chart.

## 2. Route A determinant

Use the block space

```lean
SchurInc 1 s z =
  Matrix (Fin 1) (Fin 1) ℝ ×
    (Matrix (Fin 1) (Fin z) ℝ ×
      (Matrix (Fin s) (Fin 1) ℝ × Matrix (Fin s) (Fin z) ℝ))
```

with block order `(K,N,X,E) = (p,t,ℓ,w)`. Then

```lean
schurFrameMap (K,N,X,E) = (K, K*N, X*K, X*K*N + E)
```

is your chart, up to `add_comm` in the bottom-right block.

[FACT, local] The following are already proved at variable width:

- [`schurFrameMap_hasFDerivAt`](/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/agent-a9de48b5481a7e1e3/lean/DLNFibre/DLN/RLCT/Validate/RouteMFactorMaps.lean:51)
- [`schurFrameDeriv_det`](/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/agent-a9de48b5481a7e1e3/lean/DLNFibre/DLN/RLCT/Validate/RouteMSchurFrameDet.lean:278):
  ```lean
  LinearMap.det (schurFrameDeriv X K N) = K.det ^ (s + z)
  ```
- `schurFrameD_abs_det`, giving the form needed by CoV.
- `schurFrameMap_inj_of_det_ne_zero_gen`.

There is no scalar index type or order in the recommended determinant proof. The derivative is a threefold nesting of the local `lowerTri` construction, with diagonal blocks

```text
id,  N ↦ K*N,  X ↦ X*K,  id
```

and all product-rule terms placed in the lower-left coupling maps. Thus no off-diagonal entrywise obligations occur.

The underlying Mathlib facts are:

- [FACT] `LinearMap.det_eq_det_mul_det` for an invariant subspace, used by local `lowerTri_det`.
- [FACT] `LinearMap.det_pi`, giving `det (N ↦ K*N) = K.det ^ z`.
- [FACT] `LinearMap.det_conj`, `Matrix.det_transpose`, giving `det (X ↦ X*K) = K.det ^ s`.
- [FACT] `LinearMap.det_comp` and `LinearMap.det_prodMap` if you factor the derivative further.
- [FACT] `Matrix.det_unique` reduces the `1×1` determinant to `p`.

Hence `det DΦ = p^(s+z)` and `|det DΦ| = |p|^(s+z)`.

If you insist on a scalar matrix, use `Fin (1 + z + s + s*z)` with the ordinary order and consecutive blocks `(p,t,ℓ,w)`. [FACT] `Matrix.det_of_lowerTriangular` expects `BlockTriangular OrderDual.toDual`. Prove triangularity by splitting only on the four block roles. Alternatively, [FACT] `Matrix.BlockTriangular.det_fintype` factors the four diagonal blocks. This is strictly more bookkeeping than the product-space proof.

## 3. Route B’s exact scaling primitive

[FACT] At v4.29:

```lean
Measure.map_addHaar_smul volume hp
```

specializes, for `E` of real finrank `d` and `hp : p ≠ 0`, to

```lean
Measure.map (p • ·) (volume : Measure E)
  = ENNReal.ofReal (|(p ^ d)⁻¹|) • volume
```

This is used verbatim in [`lintegral_comp_smul_euclidean`](/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/agent-a9de48b5481a7e1e3/lean/DLNFibre/DLN/RLCT/Validate/RouteMSJTwoBlockRadial.lean:53). No `Real.rpow` is needed.

The more general [FACT] lemma is:

```lean
Measure.map_linearMap_addHaar_eq_smul_addHaar volume hdet
```

which yields

```lean
Measure.map T volume
  = ENNReal.ofReal |(LinearMap.det T)⁻¹| • volume
```

and, for measurable `F`,

```lean
∫⁻ x, F (T x)
  = ENNReal.ofReal |(LinearMap.det T)⁻¹| * ∫⁻ x, F x
```

via [FACT] `lintegral_map` and `lintegral_smul_measure`.

The Tonelli skeleton would put `p` outermost, translate the `w`-integral first, then apply scaling to `u=(t,ℓ)`:

```text
|p|^(s+z) ∫u ∫w g(p, p•u, w + shear(p,u))
 = |p|^(s+z) ∫u ∫w g(p, p•u, w)
 = ∫B,C ∫D g(p,B,C,D).
```

The factor remains inside the outer `p`-integral. The obstruction is that [FACT] `setLIntegral_prod` requires `AEMeasurable`; therefore this Tonelli route does not prove the stated arbitrary-`g` theorem without strengthening its hypotheses.

## 4. Cleaner third formulation

Conjugate the banked Schur frame by the block reshape:

```lean
E : Matrix (Fin (s+1)) (Fin (z+1)) ℝ ≃L[ℝ] SchurInc 1 s z
Φ := E.symm ∘ schurFrameMap ∘ E
```

[FACT, local] `flatBlockLE` supplies the underlying linear equivalence. The derivative is the conjugate of `schurFrameD`; [FACT] `LinearMap.det_conj` removes both reshape factors. This gives Route A’s single CoV with no explicit Jacobian matrix and is the cleanest implementation.

## 5. Main Lean risks

1. Aligning `Fin (s+1)`/`Fin (z+1)` coordinates with `SchurInc 1 s z`, including the repository’s Matrix norm/module instance diamond.
2. Matching the derivative after conjugation, especially `E + X*K*N` versus `X*K*N + E`.
3. Translating `p ≠ 0` into the singleton condition `K.det ≠ 0` for the generic injectivity lemma.