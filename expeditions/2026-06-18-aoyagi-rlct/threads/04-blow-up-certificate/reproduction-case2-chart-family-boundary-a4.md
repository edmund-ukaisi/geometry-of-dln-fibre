# A4 Case 2 Chart-Family Boundary

Status: reproduced a named assumption boundary for the remaining
chart-family obligations.

## Source Data

In Case 2, Aoyagi's center is the residual block

```text
J+1 <= i <= mu_S,
J+1 <= j <= n_(S+1).
```

The paper displays the top-left selected-entry chart

```text
d_(J+1,J+1) = u.
```

The formal finite center has one candidate selected-entry chart for every pair
in the residual block. The source text does not provide a fully formal atlas,
overlap, or source-order transition theorem for every non-displayed selected
entry.

## Boundary

The chart-family boundary records the remaining obligations as supplied
predicates:

```text
ChartRegular(p)
TransitionRegular(p,q)
```

for pivot entries `p,q` in the finite residual-block center. A boundary package
says:

```text
if p is in the center, then ChartRegular(p);
if p and q are in the center, then TransitionRegular(p,q).
```

This does not define what regularity or transition regularity mean. Later work
must instantiate these predicates with a source-appropriate chart model.

The only proved non-boundary fact is nonemptiness under the continuation
hypothesis: if `J+1 <= mu_(S+1)`, then the displayed pivot
`(J+1,J+1)` belongs to the finite residual-block center, so the center is
nonempty.

## Scope

This checkpoint proves:

- a generic finite selected-entry chart-family boundary package;
- a Case 2 residual-block specialization of that boundary;
- nonemptiness of the Case 2 residual-block pivot set under continuation;
- convenience projections from the Case 2 boundary for chart regularity,
  transition regularity, and displayed-pivot regularity.

It does not prove:

- chart regularity;
- transition regularity;
- affine blow-up atlas construction or chart coverage;
- source-order transition formulas for non-displayed pivots;
- chart-produced recurrence or exponent post-data;
- polynomial-coordinate Jacobians or analytic germ invariance;
- source comparability, normal crossings, or RLCT extraction.
