# Reproduction - A4/A0 Case 2 exponent-coordinate bridge

Date: 2026-06-23.

Status: reproduced, formalised, and reviewed.

Review:
`review-case2-a0-exponent-coordinate-bridge-a4.md`.

## Source Anchor

Aoyagi PDF pp. 5-6 gives the normal-crossing finite ratio

```text
(h_j + 1) / (2 k_j)
```

for a chart coordinate whose loss monomial exponent is `2 k_j` and whose
Jacobian/prior monomial exponent is `h_j`.  In the displayed Case 2
selected-entry chart on PDF pp. 19-22, the selected residual-block square
factor contributes one square factor `u^2`, and the formal pivot-first
determinant calculation gives exponent

```text
h = |E \ {(J+1,J+1)}|,
```

where `E = case2ResidualBlockPivotEntries n S J`.  Since the displayed pivot
belongs to `E` under the continuation hypothesis,

```text
h + 1 = |E|.
```

The preceding A4 certificate formalised this finite arithmetic.  This slice
does not build a new artificial exponent-data object.  Instead, it records the
supplied bridge needed when a later A0 exponent datum `D` has a coordinate
`p` corresponding to this displayed Case 2 local step.

## Pen-and-Paper Calculation

Suppose a supplied A0 finite exponent datum `D` has coordinate `p` whose
exponent arrays match the displayed continuing Case 2 local step:

```text
D.lossExp p = 1,
D.jacobianPriorExp p = |E \ {(J+1,J+1)}|.
```

Then `p` is active, because its loss exponent is positive.  Its finite ratio
is

```text
D.ratioAt p
  = (D.jacobianPriorExp p + 1) / (2 * D.lossExp p)
  = (|E \ {(J+1,J+1)}| + 1) / 2
  = |E| / 2.
```

This is the useful A0-facing consequence of the local Case 2 calculation:
it supplies one active coordinate and its ratio.  It does not say this ratio
is the global minimum of `D`, and it does not say how many chart coordinates
attain the global minimum.

## Lean Target

Generic A0 helpers:

```text
AoyagiNormalCrossingExponentData.mem_activePairs_of_lossExp_eq_one
AoyagiNormalCrossingExponentData.ratioAt_eq_nat_div_two_of_lossExp_eq_one_of_jacobianPriorExp_add_one_eq
```

Case 2 supplied-coordinate bridge:

```text
Case2DisplayedContinuingA0ExponentCoordinateBridge
Case2DisplayedContinuingA0ExponentCoordinateBridge.activePair_and_ratioAt_eq_centerCard_div_two
Case2DisplayedContinuingA0ExponentCoordinateBridge.activePair
Case2DisplayedContinuingA0ExponentCoordinateBridge.ratioAt_eq_centerCard_div_two
```

## Boundary

This slice is finite exponent-coordinate bookkeeping only:

- no construction of the A0 exponent data `D`;
- no chart production;
- no analytic normal-crossing chart certificate;
- no differentiable Jacobian or volume-form theorem;
- no analytic unit neighbourhood;
- no chart coverage or transition regularity;
- no global active-ratio minimum over all Aoyagi charts;
- no Lemma 5 order count;
- no pole order or RLCT extraction.

## Kill Conditions

- Do not use the supplied bridge as if it constructed a coordinate of `D`.
- Do not read the local `|E|/2` equality as the final exponent minimum before
  all source chart ratios and global lower bounds are supplied.
- Do not use this as analytic validation of the formal determinant; that
  remains outside this finite interface.
