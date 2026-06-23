# Reproduction - A4/A0 Case 2 exponent-minimum bridge

Date: 2026-06-23.

Status: reproduced, formalised, and reviewed.

Review:
`review-case2-a0-exponent-minimum-bridge-a4.md`.

## Source Anchor

Aoyagi PDF pp. 5-6 computes the learning coefficient from the finite minimum
of the ratios

```text
(h_j + 1) / (2 k_j)
```

over active normal-crossing chart coordinates.  The previous A4/A0 supplied
coordinate bridge proves that, if a supplied coordinate `p` of a later A0
finite exponent datum `D` corresponds to the displayed continuing Case 2
selected-entry step, then

```text
p in D.activePairs,
D.ratioAt p = card(case2ResidualBlockPivotEntries n S J) / 2.
```

This slice adds only the finite minimum step under an explicit global lower
bound over all active coordinates.

## Pen-and-Paper Calculation

Let

```text
q = card(case2ResidualBlockPivotEntries n S J) / 2.
```

Assume the supplied Case 2/A0 coordinate bridge for `p`, so `p` is active and
`D.ratioAt p = q`.  If, in addition, every active coordinate ratio is at least
`q`,

```text
for all p' in D.activePairs, q <= D.ratioAt p',
```

then `q` is both an active ratio and a lower bound for all active ratios.
Therefore the finite minimum is exactly

```text
D.exponentMinimum = q.
```

This is a finite `Finset.min'` certificate only.  It does not prove the lower
bound from Aoyagi's recursion; that lower bound remains a source/chart-family
obligation.

## Lean Target

Add to `Case2FiniteExponentBridge.lean`:

```text
Case2DisplayedContinuingA0ExponentCoordinateBridge.exponentMinimum_eq_centerCard_div_two_of_forall_le
```

The theorem should consume:

- the supplied Case 2/A0 exponent-coordinate bridge;
- an explicit lower bound
  `forall p' in D.activePairs, centerCard/2 <= D.ratioAt p'`.

It should prove:

```text
D.exponentMinimum =
  ((case2ResidualBlockPivotEntries n S J).card : Q) / 2
```

## Boundary

This slice does not prove:

- construction of the A0 exponent data `D`;
- construction of the coordinate `p`;
- the global lower bound itself;
- chart production or chart coverage;
- analytic Jacobian/volume-form control;
- an A0 normal-crossing chart certificate;
- exponent order or pole order;
- RLCT extraction.

## Kill Conditions

- Do not omit the explicit global lower-bound hypothesis.
- Do not read this as Aoyagi Theorem 2's final finite exponent formula unless
  the displayed Theorem 2 lambda equality and order-count data are also
  supplied.
- Do not use this to assert any analytic chart or Jacobian fact.
