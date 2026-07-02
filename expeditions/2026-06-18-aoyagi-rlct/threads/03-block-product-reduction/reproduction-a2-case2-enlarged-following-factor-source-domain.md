# Reproduction - A2 Case 2 enlarged following-factor source domain

Date: 2026-07-02.

Status: first enlarged-coordinate Lean slice; no source-image theorem yet.

## Source Boundary

Aoyagi's p.13 active retained-passive block has two factors in the two-edge
post-pivot window:

```text
C(0): residual columns -> free endpoint,
C(1): residual rows -> residual columns.
```

The old passive-theta source fills `C(1)` from selected-entry center
coordinates and also fixes `C(0)` to the following-factor tail attached to the
same successor selected-entry matrix.  This is a graph/section inside the
ambient active `C` tuple, not a full coordinate chart for that tuple.

The enlarged source must therefore add a free following-factor matrix

```text
F : Matrix (Case2ResidualColIndex n S (J+1)) τ ℝ.
```

This is equivalent to the missing head `C(0)` coordinate block for the
two-edge retained-passive tuple.

## Why Not Arbitrary Cprime

An arbitrary pivot-first `C'` has a top row and a lower tail.  The retained
two-edge family only reads the post-pivot following-factor tail, so the top
row would be invisible and would make a source/readback map non-injective.

The Lean constructor uses the normalized helper

```text
case2DisplayedPostPivotFreeCprimeOfFollowingFactor
```

which sets the ignored top row to zero and realizes exactly the supplied
following factor.

## Lean Slice

The new constructor is in

```text
DLNFibre.DLN.Aoyagi.RetainedPassiveCase2SelectedEntryChartBridge
```

and is named

```text
case2PostPivotSelectedEntryRetainedPassiveDataWithPassiveFollowingFactor
```

It takes:

- the same passive fields as `case2PostPivotSelectedEntryRetainedPassiveDataWithPassive`;
- selected-entry tail coordinates `yNext`;
- an independent following-factor matrix `F`;
- the successor column equivalence `eNext`.

It stores

```text
C := case2PostPivotFreeTwoEdgeFactorFamily
  (case2SuccessorSelectedEntrySourceResidual yNext eNext)
  (case2DisplayedPostPivotFreeCprimeOfFollowingFactor F).
```

The formalized support lemmas are:

```text
case2PostPivotSelectedEntryRetainedPassiveDataWithPassiveFollowingFactor_detChart
continuous_case2PostPivotSelectedEntryRetainedPassiveDataWithPassiveFollowingFactor
```

The determinant chart proof depends only on `Ctop` and passive `A1`, so the
free following factor introduces no new determinant condition.  The continuity
proof separates the two active `C` factors: `C(0)` is the continuous projection
to `F`, while `C(1)` is the selected-entry successor matrix restricted to the
tail block.

## Next Theorem

The next production theorem should introduce a parallel enlarged source type,
for example

```text
Case2PassiveThetaWithFollowingFactor :=
  Case2PassiveTheta ×
    Matrix (Case2ResidualColIndex n S (J+1)) τ ℝ,
```

with retained data given by the new constructor.  The first useful source
theorem should be a local chart-image/readback statement: open set, determinant
membership, source map, readback left inverse, injectivity, continuity, and
measurable image.  The density identity and bound remain separate obligations.

## Nonclaims

No source-image coverage, determinant-chart Haar transport, raw-Haar
pushforward, original-prior transport, Jacobian density identity, density
bound, normal-crossing theorem, pole order, or RLCT extraction is proved here.
