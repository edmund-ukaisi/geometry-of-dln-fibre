# Reproduction - A4 Case 2 selected-entry extraction handoff

Date: 2026-06-24.

Status: reproduced before Lean implementation.

## Source Anchor

Aoyagi PDF pp. 19-21 gives the Case 2 residual-block center

```text
d_ij = 0,    J+1 <= i <= M(S),    J+1 <= j <= M^(S+1),
```

and displays the selected-entry blow-up chart for the top-left pivot.  The
previous selected-entry multi-chart reproduction extends only the finite
selected-entry algebra to all pivots of this finite center.  Aoyagi PDF
pp. 5-6 is the normal-crossing extraction boundary: once a genuine
normal-crossing presentation has been supplied, the RLCT value and pole order
are read from the exponent minimum and the minimum-coordinate count.

This note does not construct the analytic normal-crossing presentation.  It
only records what follows from the explicit chart-level extraction hypothesis
already present in the A0 Lean interface.

## Finite Case 2 Certificate

Let

```text
E = case2ResidualBlockPivotEntries n S J.
```

Under the continuation assumptions

```text
1 <= S,
J + 1 <= prefixMinNat n (S + 1),
```

the displayed pivot lies in `E`, so `E` is nonempty.  The finite all-pivot
selected-entry certificate has one active coordinate in every pivot chart.
The already reproduced selected-entry calculation gives

```text
exponentMinimum =
  (((prefixMinNat n S - J) * (n(S+1) - J)) : Q) / 2,

exponentOrder = 1.
```

Here `exponentOrder = 1` is the local finite-family order of this selected-entry
certificate.  It is not Aoyagi Theorem 2's global pole-order formula.

## Extraction-Hypothesis Composition

Let `C` denote the concrete Case 2 residual-block all-pivot certificate.  The
chart-level extraction hypothesis is an explicit input:

```text
C.ExtractionHypothesis lambda poleOrder.
```

By definition of this interface it gives exactly

```text
lambda = C.exponentData.exponentMinimum,
poleOrder = C.exponentData.exponentOrder.
```

Substituting the finite Case 2 certificate equalities therefore yields

```text
lambda =
  (((prefixMinNat n S - J) * (n(S+1) - J)) : Q) / 2,

poleOrder = 1.
```

No lower-bound, chart-count, or source-production data are inferred in this
step.  They are all contained in, or prior to, the supplied extraction
hypothesis.

## Lean Target

Add a theorem in the namespace
`case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate`:

```text
lambda_and_poleOrder_eq_selectedCoordinateCount_div_two_and_one_of_extractionHypothesis
```

The proof should be two short `calc` chains:

1. `lambda` is the certificate's finite exponent minimum by the extraction
   hypothesis, then the finite minimum theorem rewrites it to the selected
   coordinate count divided by two.
2. `poleOrder` is the certificate's finite exponent order by the extraction
   hypothesis, then the finite order theorem rewrites it to `1`.

## Boundary

- The extraction hypothesis is consumed, not constructed.
- No analytic atlas coverage or transition regularity is proved.
- No source-coordinate production for arbitrary residual-block pivots is
  proved.
- No global A0 normal-crossing data is constructed.
- No Aoyagi Theorem 2 active-ratio lower bound or displayed-ratio chart-count
  theorem is proved.
- No global DLN RLCT theorem is proved.

## Kill Conditions

- If this theorem is cited without the explicit `ExtractionHypothesis`, it
  overclaims the normal-crossing boundary.
- If its `poleOrder = 1` conclusion is used as the global Theorem 2 order
  formula, it confuses a local finite selected-entry certificate with the
  full chart family.
- If it is used to justify arbitrary-pivot source formulas, it bypasses the
  separate A4 source-production frontier.
