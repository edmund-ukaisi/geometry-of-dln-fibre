# Reproduction - A4 Case 2 transition-generated Q/P package

Date: 2026-06-24.

Status: pen-and-paper reproduced; Lean formalised; xhigh reviewed.

## Source Anchor

Aoyagi PDF pp. 20-21, Case 2, displays the selected-pivot coordinate change
and the associated `Q/P` lower-right Schur calculation.  This note records a
finite API package obtained by combining three already-reproduced elementary
pieces:

- selected-entry source-to-target transition data;
- the supplied source-selected `Q/P` identity for a chosen residual-block
  pivot;
- the denominator-cleared target Schur formula on the same overlap.

It does not assert that Aoyagi prints every non-top-left pivot chart, and it
does not prove analytic transition regularity, chart coverage, or source
production of successor objects.

## Reproduction

Let the Case 2 residual-block center be

```text
E = case2ResidualBlockPivotEntries n S J.
```

For source and target chart indices, write

```text
p = source pivot,
q = target pivot = (a,b).
```

In the source selected chart, write normalized residual-block coordinates

```text
x_rs = case2SourceSelectedNormalizedMapOfMem p_mem residual (r,s).
```

Assume the target normalized coordinate is nonzero:

```text
d = x_ab != 0.
```

The selected-entry transition-generated target chart data are

```text
targetU = u*d,
w_rs = x_rs/d.
```

Then the finite chart map in the target chart represents the same finite
center values as the source chart:

```text
targetU*w_rs = (u*d)*(x_rs/d) = u*x_rs.
```

This is exactly the already-formalised finite transition-point chart-map
identity.  Now instantiate the existing source-selected supplied-boundary
`Q/P` theorem at the target pivot `q`, with selected variable `targetU` and
residual function `w`.  This gives the same finite `Q/P` matrix identity as
the source-selected theorem, but fed by the transition-generated target chart
coordinates.

Finally, for target lower-right residual-row and residual-column subtype
indices `i,j`, the Schur block in that same target `Q/P` identity is

```text
S_ij(w) = w_ij - w_ib*w_aj.
```

Clearing the normalized denominator gives

```text
d^2*S_ij(w) = d*x_ij - x_ib*x_aj.
```

The package therefore records, for the same transition-generated target data:

1. finite chart-map equality;
2. the supplied target-pivot `Q/P` identity;
3. the denominator-cleared lower-right Schur formula.

## Lean Target

```text
case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate.sourceChartTransitionPoint_sourceSelectedQP_package_of_target_normalized_ne_zero
```

## Boundary

- This is finite selected-entry and `Q/P` residual-block coordinate algebra.
- The `Q/P` part is still a projection from the supplied
  `Case2SourceSelectedSuppliedChartFamilyBoundary`; the theorem does not
  produce chart-family regularity, transition regularity, recurrence post-data,
  exponent post-data, successor residual matrices, or following factors.
- It proves no analytic transition regularity, no open-neighbourhood gluing,
  no chart coverage, no source-displayed all-pivot atlas, no analytic
  Jacobian/volume theorem, no global normal crossings, no pole order, and no
  RLCT extraction.
- The nonzero hypothesis is the normalized target coordinate `d = x_ab`, not
  the finite center value `u*d`.

## Kill Conditions

- Do not replace `d != 0` by `(u*d) != 0`.
- Do not claim that the supplied target-pivot `Q/P` identity source-produces
  `Csucc`, `C'^(S+1)`, suffixes, or following factors.
- Do not promote the supplied `ChartRegular`/`TransitionRegular` fields to
  proved analytic regularity.
- Do not treat arbitrary chart-index pivots as source evidence that Aoyagi
  displayed every pivot chart.
