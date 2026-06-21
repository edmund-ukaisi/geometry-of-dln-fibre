# Pen-and-paper reproduction - A4 Case 2 free Cprime local product package

Status: reproduced as a paired finite source-coordinate product package.

## Source Anchor

Aoyagi PDF pp. 19-22, Case 2.  In the displayed top-left pivot chart the paper
uses the substitutions

```text
D = u * D_chart,
C' = Q^-1 C,
D'' = D_chart * Q,
D''' = P D'',
```

with `P` clearing the lower entries in the first column after the row-weighted
diagonal is inserted.  The displayed calculation is

```text
P diag(b') D'' C' = diag(b') D''' C'.
```

In the continuing branch, the paper then renames primed variables and says the
inductive statement holds with `J` increased by one.

## Reproduction

Work only in the displayed pivot-first finite coordinates.  Let `Cprime` be a
free pivot-first chart-coordinate following matrix.  Define the old pivot-first
following matrix by

```text
C_old = Q * Cprime.
```

Equivalently, after transporting residual columns back to source order and
setting non-residual source columns to zero, this gives a total
source-coordinate following function whose residual restriction is `C_old`.
The already-reproduced inverse calculation gives

```text
Q^-1 C_old = Cprime.
```

Therefore the displayed source-coordinate `Q/P` identity can be read with
this free chart-coordinate following factor:

```text
P diag(old row weights) D_source_chart C_old
  = diag(successor row weights) D''' Cprime.
```

Independently, the free-`Cprime` continuing calculation gives

```text
(D''' Cprime)_lower,reindexed
  =
D_postpivot * Cprime_tail,reindexed.
```

Pairing these two equalities gives a finite local product package:

1. the old source-substituted product is rewritten as the row-weighted
   cleared product with free `Cprime`;
2. the continuing lower rows of the bare cleared product `D''' Cprime` are
   the next same-stage residual block times the free `Cprime` tail.

The two equalities must remain distinct unless an additional weighted
lower-row projection is stated: the right side of the `Q/P` identity contains
the successor row-weight diagonal multiplying `D''' Cprime`.

When the concrete displayed source-chart constructor is used, the same package
can be conjoined with the existing corrected selected-label exponent, level,
least-value-gap, and `case2Gap` projections.  These fields remain supplied or
corrected finite bookkeeping; they are not produced by the paired product
identity.

## Boundary Checks

- This is stronger than Aoyagi's displayed notation only in the harmless
  finite-coordinate direction: `Cprime` is taken as a free chart coordinate
  and the old following factor is reconstructed as `Q*Cprime`.
- The total source-coordinate following function is a finite representative
  obtained by zero outside the residual-column range.  It is not a theorem
  that Aoyagi's analytic chart produces all such functions.
- The package does not identify the free tail with an externally supplied
  next-layer source matrix, except as a named continuing-branch candidate.
- The nonemptiness of the next residual center remains a separate consequence
  of `J+2 <= prefixMinNat n (S+1)`.

## Formalisation Target

Lean should add a narrow package theorem, likely in the
`Case2DisplayedSuppliedChartFamilyBoundary` namespace, pairing:

```text
sourceDisplayedQP_constructedSourceFollowingFactor_paperQP
postPivotFreeCprimeNextSameStageProduct
```

and a concrete source-chart theorem pairing the same product package with
`of_sourceChartMap_case2Succ_updateSelected` corrected post-data.

The theorem name should say "constructed source" and "free Cprime" so it is
not mistaken for chart coverage or source production.

## Kill Conditions

- Do not claim affine chart coverage, arbitrary-pivot coverage, or
  source-production of all `Cprime`.
- Do not claim successor `C'^(S+1)` construction beyond the reindexed free
  tail candidate.
- Do not infer recurrence/exponent post-data from the product equality.
- Do not include terminal `(S+1,0)` relabeling.
- Do not compute Jacobians, normal crossings, pole order, or RLCT.
- Do not use the Lehalleur-Rimanyi/quiver paper or quiver Lean as evidence.
