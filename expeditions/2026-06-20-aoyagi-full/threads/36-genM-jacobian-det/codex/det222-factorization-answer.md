   These should be `funext`, `fin_cases`, `simp [pivotBlowupOn, shear222]`, `ring`.
3. Define `shear222Deriv` exactly as the product-rule derivative of the three changed rows.
4. Prove:
   ```lean
   shear222_hasFDerivAt
   shear222Deriv_det : (shear222Deriv p).det = 1
   ```
   Use the same `BlockTriangular` row argument as `shear334Deriv_det`, with modified set `{0,6,7}`.
5. Define:
   ```lean
   T222Deriv u :=
     (pivotBlowupOnDeriv ({1,4} : Finset (Fin 8)) 4 (shear222 (pb222 u))).comp
       ((shear222Deriv (pb222 u)).comp
         (pivotBlowupOnDeriv ({0,6,7} : Finset (Fin 8)) 0 u))
   ```
6. Det:
   ```lean
   |(T222Deriv u).det| = |u 0|^2 * |u 4|
   ```
   from `pivotBlowupOnDeriv_det`, `shear222Deriv_det`, and `(shear222 (pb222 u)) 4 = u 4`.

Then compose with `Q222CLM := paramsEquivFlatCLE M222 ∘ pack222CLM`; prove `|det Q222CLM| = 1` by the existing measure-preserving reshape pattern. This gives:

```lean
|LinearMap.det (fderiv ℝ phi u).toLinearMap| = |u 0|^2 * |u 4|
```

I would not do the raw 8×8 determinant unless this factorization unexpectedly bogs down. A direct sparse/block proof is feasible, but it is less reusable and does not help the eventual `cov` as much.

For planning: the determinant/fderiv part is a bounded small build. The full `cov`/atom may still be its own scoped sub-build because you also need injectivity off `{x0 = 0} ∪ {x4 = 0}` and the null-slice addback for `{x4 = 0}`. But the determinant is not a multi-tide obstruction.
tokens used
120,497
**Recommendation:** use the factorization. The missing move is:

```lean
T222 = bsubst222 ∘ shear222 ∘ pb222
```

not `bsubst222 ∘ pb222`, and not a shear after `bsubst222`.

Define, with `x0=a`, `x1=b`, `x4=e`:

```lean
pb222     := pivotBlowupOn ({0,6,7} : Finset (Fin 8)) 0
bsubst222 := pivotBlowupOn ({1,4} : Finset (Fin 8)) 4

shear222 p i :=
  if i = 0 then p 0 - p 1 * p 2
  else if i = 6 then p 6 + p 5 * p 1
  else if i = 7 then p 7 - p 1 * p 3
  else p i
```

Then:

```lean
pb222 u =
  [x0, x1, x2, x3, x4, x5, x0*x6, x0*x7]

shear222 (pb222 u) =
  [x0 - x1*x2, x1, x2, x3, x4, x5,
   x0*x6 + x5*x1, x0*x7 - x1*x3]

T222 u =
  [x0 - x1*x2, x4*x1, x2, x3, x4, x5,
   x0*x6 + x5*x1, x0*x7 - x1*x3]
```

Now pack by

```lean
pack222 w =
  ( A0 = !![w 4, w 1; w 5, w 6],
    A1 = !![w 0, w 7; w 2, w 3] )
```

so `chartParams222 = pack222 ∘ T222`.

The obstruction disappears because `shear222` uses bare `x1` before `bsubst222` replaces the surviving coordinate slot `1` by `x4*x1`. The terms `-x1*x2`, `-x1*x3`, and `x5*x1` are ordinary polynomial triangular shear terms; the derivative is block triangular with diagonal `1`, so determinant `1`.

Concrete Lean route:

1. Copy the `T334` pattern from [RouteMLayerCoverGEL2.lean](/home/ubuntu/workspace/geometry-of-dln-fibre/lean/DLNFibre/DLN/RLCT/Validate/RouteMLayerCoverGEL2.lean:680), but in `Fin 8`.
2. Prove:
   ```lean
   pb222_apply
   shear_pb222_apply
   T222_apply
   chartParams222_eq_pack_T
   ```
   These should be `funext`, `fin_cases`, `simp [pivotBlowupOn, shear222]`, `ring`.
3. Define `shear222Deriv` exactly as the product-rule derivative of the three changed rows.
4. Prove:
   ```lean
   shear222_hasFDerivAt
   shear222Deriv_det : (shear222Deriv p).det = 1
   ```
   Use the same `BlockTriangular` row argument as `shear334Deriv_det`, with modified set `{0,6,7}`.
5. Define:
   ```lean
   T222Deriv u :=
     (pivotBlowupOnDeriv ({1,4} : Finset (Fin 8)) 4 (shear222 (pb222 u))).comp
       ((shear222Deriv (pb222 u)).comp
         (pivotBlowupOnDeriv ({0,6,7} : Finset (Fin 8)) 0 u))
   ```
6. Det:
   ```lean
   |(T222Deriv u).det| = |u 0|^2 * |u 4|
   ```
   from `pivotBlowupOnDeriv_det`, `shear222Deriv_det`, and `(shear222 (pb222 u)) 4 = u 4`.

Then compose with `Q222CLM := paramsEquivFlatCLE M222 ∘ pack222CLM`; prove `|det Q222CLM| = 1` by the existing measure-preserving reshape pattern. This gives:

```lean
|LinearMap.det (fderiv ℝ phi u).toLinearMap| = |u 0|^2 * |u 4|
```

I would not do the raw 8×8 determinant unless this factorization unexpectedly bogs down. A direct sparse/block proof is feasible, but it is less reusable and does not help the eventual `cov` as much.

For planning: the determinant/fderiv part is a bounded small build. The full `cov`/atom may still be its own scoped sub-build because you also need injectivity off `{x0 = 0} ∪ {x4 = 0}` and the null-slice addback for `{x4 = 0}`. But the determinant is not a multi-tide obstruction.
