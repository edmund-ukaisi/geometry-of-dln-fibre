# A2 retained-passive Case 2 synthetic two-edge data

## Boundary

This slice is finite retained-passive bookkeeping for the post-pivot Case 2
two-edge chain.  It constructs a retained-passive coordinate datum whose active
`C` factors are, by definition, Aoyagi's displayed post-pivot residual block and
the following free factor.

It does not construct a source chart, prove that a fixed-base source edge family
has these coordinates, identify a longer retained-passive suffix with this
two-edge chain, prove the entrywise successor-source readout, prove weighted
pushforward or Jacobian facts, compare the original DLN loss, prove normal
crossings, compute pole order, or extract an RLCT.

## Pen-and-paper reproduction

Work in the concrete post-pivot Case 2 endpoint family

```text
kappa 0 = tau,
kappa 1 = Case2ResidualColIndex n S (J+1),
kappa 2 = Case2ResidualRowIndex n S (J+1).
```

The retained-passive nonredundant coordinate datum for `M=1` has fields

```text
A1passive : Fin 1 -> Matrix rho rho R,
F2        : Fin 2 -> Matrix rho (kappa p) R,
A3passive : Fin 1 -> Matrix (kappa (p+1)) rho R,
C         : Fin 2 -> Matrix (kappa (p+1)) (kappa p) R,
Ctop      : Matrix rho rho R,
F3        : Matrix (kappa 2) rho R.
```

Define the synthetic Case 2 datum by

```text
A1passive 0 = 1,
F2 p        = 0,
A3passive 0 = 0,
C 0         = case2DisplayedPostPivotFreeFollowingFactor,
C 1         = case2DisplayedPostPivotResidualBlock,
Ctop        = 1,
F3          = 0.
```

Equivalently, the active family `C` is exactly
`case2PostPivotFreeTwoEdgeFactorFamily n hS hcont residual Cprime`.

The determinant chart for nonredundant retained-passive coordinates asks for

```text
IsUnit det(Ctop) and forall p : Fin 1, IsUnit det(A1passive p).
```

For the synthetic datum this reduces to

```text
IsUnit det(1) and IsUnit det(1),
```

so it is inhabited by the unit `1` in the base field.

For the residual-factor product, the finite two-edge unfold gives

```text
residualFactorProduct(C, 2, 0) = C 1 * C 0
  = D_(J+1) * C'_+.
```

The earlier Case 2 selected-entry bridge already proves that, under the
entrywise successor-source readout

```text
D_(J+1) * C'_+ at (i,t)
  = case2DisplayedSourceChartMap n hS hnext
      yNext_(J+2,J+2)
      (CenterCoord.sourceResidual yNext)
      (case2ResidualBlockCoordinateIndexEquivPivotEntriesOfEquivs
        n S (J+1) refl eNext (i,t)).1,
```

the two-edge product is the successor selected-entry `CenterCoord.chartMap`
matrix.  Since the synthetic retained-passive datum has exactly that `C` family,
the same theorem gives the retained-passive `hdataFactor` shape:

```text
residualFactorProduct(syntheticData.C, 2, 0)
  = matrix(c |-> CenterCoord.chartMap
      pivotNext yNext
      (case2ResidualBlockCoordinateIndexEquivPivotEntriesOfEquivs
        n S (J+1) refl eNext c)).
```

Here `pivotNext` is `(J+2,J+2)` as an element of the successor center
`case2ResidualBlockPivotEntries n S (J+1)`.

## Checks

- The endpoint family is exactly `Fin 3`, not a longer retained-passive suffix.
- The factor order is `C 1` then `C 0`; this is `D_(J+1) * C'_+`.
- The determinant-chart proof uses only `Ctop=1` and `A1passive=1`.
- The entrywise successor-source readout remains supplied.  This slice removes
  generic factor-identification hypotheses only because the synthetic datum
  defines the active factors to be the displayed Case 2 factors.
