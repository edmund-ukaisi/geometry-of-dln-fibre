# Reproduction - A2 Case 2 constructed source-readback production

Date: 2026-06-28.

Status: reproduced, Lean-formalised, and xhigh-reviewed PASS.

## Target

This note upgrades the finite constructed Case 2 displayed-product theorem to
an actual retained-passive source-readback statement for the constructed data.
It is still not arbitrary retained-passive coverage.

Given successor selected-entry coordinates `yNext` with nonzero displayed
successor pivot coordinate at `(J+2,J+2)`, construct a retained-passive-shaped
source edge family

```text
E : p : Fin 2 |-> Matrix (rho + kappa_{p+1}) (rho + kappa_p) R
```

such that `E` lies in the source-recursive determinant chart and

```text
residualFactorProduct (sourceReadback E).C (Fin.last 2) 0 = T(yNext),
```

where `T(yNext)` is the successor selected-entry matrix.  Since the selected
successor pivot coordinate is nonzero, this source-readback residual-factor
product is nonzero.

The coefficient field in Lean is `R = ℝ`; the product-side construction used
to make the displayed product is ring-generic, but the selected-entry
coordinate APIs are real-valued.

## Pen-and-Paper Factor Orientation

In Aoyagi's Case 2 selected pivot chart, the old normalized residual block has
the displayed form

```text
N = [1  y]
    [x  Z].
```

Column clearing uses

```text
Q    = [1 -y],      Q^{-1} = [1 y],
       [0  I]               [0 I]
```

so

```text
N Q = [1  0]
      [x  Z - x y].
```

The following factor is transported by `C' = Q^{-1} C`, hence the lower tail
of `C'` is the free following factor `C'_+`.  Row clearing then removes the
first column and leaves the post-pivot residual block

```text
D_+ = Z - x y.
```

The pivot scalar is absorbed into the updated weights; it is not an extra
factor in the two-edge residual product.

With retained-passive two-edge orientation,

```text
C^rp_0 : kappa_1 -> kappa_0 = C'_+,
C^rp_1 : kappa_2 -> kappa_1 = D_+.
```

Thus

```text
residualFactorProduct C^rp (Fin.last 2) 0
  = C^rp_1 * C^rp_0
  = D_+ * C'_+.
```

The per-factor equalities are the important point:

```text
(sourceReadback E).C 1 = D_+,
(sourceReadback E).C 0 = C'_+.
```

Product equality alone would not determine these factors.

## Constructed Source Family

The already landed finite construction produces `residual` and `Cprime` such
that

```text
case2DisplayedPostPivotFreeTwoEdgeFactorProduct n hS hcont residual Cprime
  = T(yNext)
```

and the product is nonzero.

Package these factors as the synthetic two-edge retained-passive datum

```text
data = case2PostPivotRetainedPassiveData n hS hcont residual Cprime.
```

By construction,

```text
data.C 1 = case2DisplayedPostPivotResidualBlock n hS hcont residual,
data.C 0 = case2DisplayedPostPivotFreeFollowingFactor n hS hcont Cprime.
```

The source edge family is

```text
E = data.edgeMatrix.
```

The determinant-chart theorem for the synthetic datum gives `data.detChart`.
The retained-passive source-map theorem then gives

```text
sourceRecursiveDetChart E
```

and the source-readback left inverse gives

```text
sourceReadback E = data.
```

Therefore

```text
residualFactorProduct (sourceReadback E).C (Fin.last 2) 0
  = residualFactorProduct data.C (Fin.last 2) 0
  = residualFactorProduct (case2PostPivotFreeTwoEdgeFactorFamily ...) (Fin.last 2) 0
  = T(yNext).
```

The nonzero conclusion follows by rewriting to the already constructed nonzero
displayed product.

## Proved / Assumed / Cited / Deferred

**Proved by this reproduction.** For every successor selected-entry coordinate
vector with nonzero displayed successor pivot coordinate, there exists a
two-edge retained-passive-shaped source family in the source-recursive
determinant chart whose actual `sourceReadback` residual-factor product is the
successor selected-entry matrix and is nonzero.

**Assumed.** The branch hypotheses `hS`, `hcont`, `hnext`, endpoint equivalence
`eNext`, and nonzero successor pivot coordinate.

**Cited.** Aoyagi pp. 19-22 for the Case 2 selected-pivot clearing algebra.
The retained-passive source/readback inverse is local Lean infrastructure
already reproduced in this expedition.

**Deferred.** Arbitrary retained-passive `sourceReadback E` factor alignment;
selected-entry source/prior measure transport for this constructed source
family; original source-rank coverage; normal crossings; pole order; RLCT.

## Lean Shape

Lean endpoints:

```text
exists_sourceRecursive_case2PostPivot_sourceReadback_residualFactorProduct_eq_successorSelectedEntryMatrix_of_yNext_pivot_ne_zero
exists_sourceRecursiveEdgeFamily_case2PostPivot_sourceReadback_residualFactorProduct_eq_successorSelectedEntryMatrix_of_yNext_pivot_ne_zero
```

The first theorem keeps the constructed `residual` and `Cprime` witnesses
visible.  The second theorem existentially exposes only the produced source
edge family `E`.
