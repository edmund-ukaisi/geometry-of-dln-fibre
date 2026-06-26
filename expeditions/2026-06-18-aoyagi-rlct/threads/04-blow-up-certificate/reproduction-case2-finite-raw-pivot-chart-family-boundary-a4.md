# Reproduction - Case 2 finite raw-pivot chart-family boundary

Date: 2026-06-26.

## Source calculation

Aoyagi's Case 2 residual-block blow-up, pp. 19-22, uses the selected-entry
chart calculation for the displayed top-left pivot.  In finite residual-block
coordinates this has the elementary form

```text
z_p = u,
z_i = u y_i    for i != p.
```

The all-pivot finite version is the standard selected-entry completion of the
same calculation: choose any pivot `p` in the finite residual-block center and
use the same formula.  On the overlap from pivot `p` to pivot `q`, the
denominator is the normalised target coordinate `x_q`, not the ambient value
`u*x_q`.  The transition is

```text
u_q = u * x_q,
y_i = x_i / x_q.
```

This is finite affine overlap algebra.  It gives the chart-map equality,
inverse transition, self-transition, and cocycle identities already proved by
the selected-entry affine transition certificate.

## Lean implementation

File:

```text
lean/DLNFibre/DLN/Aoyagi/SelectedEntryNormalCrossing.lean
```

New predicates:

```text
case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate
  .Case2FiniteRawPivotChartRegular

case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate
  .Case2FiniteRawPivotTransitionRegular
```

The chart predicate records:

- pivot membership in `case2ResidualBlockPivotEntries n S J`;
- the standard selected-entry formula `x_p = u`, `x_q = u * y_q`;
- finite center-ideal principalization by the selected variable.

The transition predicate records:

- source and target pivot membership;
- the `SelectedEntryFiniteAffineTransitionRegularPair` obtained from the
  all-pivot finite transition family.

Main theorem:

```text
case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate
  .finiteRawPivotChartFamilyBoundary
```

It proves

```text
Case2ResidualBlockChartFamilyBoundary n S J
  (Case2FiniteRawPivotChartRegular n S J)
  (Case2FiniteRawPivotTransitionRegular (K := K) n hS hcont)
```

from the continuation hypotheses `hS : 1 <= S` and
`hcont : J + 1 <= prefixMinNat n (S + 1)`.

## Status Labels

Proved:

- finite residual-block pivot membership/nonemptiness under continuation;
- generic selected-entry chart formula;
- finite center-ideal principalization;
- finite affine overlap pair instantiated for every ordered pair of raw pivots;
- a nontrivial `Case2ResidualBlockChartFamilyBoundary` using those predicates.

Cited:

- Aoyagi's Case 2 displayed selected-entry blow-up calculation as the source
  anchor for the finite formula.

Deferred:

- analytic domains and coverage;
- analytic chart and transition regularity;
- source-produced successor matrices and suffixes;
- analytic Jacobian or volume-form compatibility;
- global normal crossings, pole order, and RLCT extraction.

## Nonclaims

This theorem does not construct an affine analytic atlas, source-produce
`Csucc` or `C'^(S+1)`, prove arbitrary-pivot Q/P reduced-block transitions,
identify a source measure or density, prove normal crossings, compute pole
order, or extract the RLCT.  It also does not say that Aoyagi printed every
non-displayed pivot chart; the all-pivot family is the finite selected-entry
completion of the displayed algebra.
