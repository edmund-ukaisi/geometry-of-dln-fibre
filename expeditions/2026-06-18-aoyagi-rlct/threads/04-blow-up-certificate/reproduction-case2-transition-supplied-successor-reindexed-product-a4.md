# Reproduction - A4 Case 2 transition supplied-successor reindexed product

Date: 2026-06-24.

Status: pen-and-paper reproduced; Lean formalised; xhigh reviewed.

## Source Anchor

Aoyagi PDF pp. 20-22, Case 2.  The displayed chart calculation chooses the
pivot `(J+1,J+1)`, writes the same finite point in displayed coordinates on
the overlap where this normalized coordinate is nonzero, and reindexes the
finite product into the next same-stage source-product shape.

Earlier Lean slices have separated two facts:

- on the displayed overlap, the displayed substitution block at the target
  data equals the original source selected substitution block;
- a supplied source-production obligation can restate the displayed reindexed
  product with a supplied successor object `Csucc`, provided it carries the
  explicit equality to the formula-level successor factor.

This note composes only those two finite consumers.

## Reproduction

Let `p` be the arbitrary selected-entry source pivot and let the displayed
target pivot be

```text
q = (J+1,J+1).
```

Write the source normalized coordinates as

```text
x_r = case2SourceSelectedNormalizedMapOfMem p_mem residual r
d   = x_q.
```

On the displayed overlap assume

```text
d != 0.
```

The transition-generated displayed target data are

```text
targetU        = u*d,
targetResidual_r = x_r/d.
```

For these target data, suppose a source-production obligation is supplied.  In
particular, it names an object `Csucc` and supplies

```text
Csucc =
  case2DisplayedSourceSuccessorFollowingFactor
    n hS hcont targetResidual C.
```

The supplied-obligation product consumer gives a witness `P` such that

```text
DisplayedReindexedProduct(DisplayedSub(targetU,targetResidual), Csucc).
```

Here `DisplayedSub(targetU,targetResidual)` is the lower-left substitution
block in the source side of the reindexed product.

The selected-entry transition formula gives

```text
DisplayedSub(targetU,targetResidual)
  = Sub_q(u*d, x/d)
  = Sub_p(u,x).
```

Substituting this block equality into the product consumer gives the same
witness `P` for

```text
DisplayedReindexedProduct(Sub_p(u,x), Csucc).
```

The right-hand side is still the target displayed post data:

- post state `pre.case2Succ targetU`;
- post-pivot residual block from `targetResidual`;
- supplied successor object `Csucc`, used only through the supplied equality;
- corrected exponent, level, least-value-gap, and recurrence-gap post-data
  inherited from the displayed boundary.

This is a finite composition step.  It does not construct the
`SourceProductionObligation`, does not construct `Csucc`, and does not prove
suffix/source production, successor chart existence, coverage, transition
regularity, analytic Jacobian control, normal crossings, pole order, or RLCT.

## Lean Target

Add a transition wrapper in
`lean/DLNFibre/DLN/Aoyagi/SelectedEntryNormalCrossing.lean` near the existing
displayed reindexed product source-substitution theorem.

Landed name:

```text
case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate.
  sourceChartTransitionPoint_displayed_reindexedNextSourceProduct_suppliedCsucc_sourceSubstitution_of_displayed_normalized_ne_zero
```

Inputs kept explicit:

- source chart, source coordinates `(u,residual)`, and displayed-overlap
  nonzero hypothesis;
- a displayed supplied chart-family boundary for the transition-generated
  target data `(targetU,targetResidual)`;
- a `SourceProductionObligation` for those same target data;
- the supplied objects `Csucc`, `Cterm`, source suffix data, and their index
  families.

Conclusion:

- the displayed target chart-map value equals the original source chart-map
  value;
- the displayed target substitution block equals the original source selected
  substitution block;
- the displayed reindexed next-source product holds with the lower-left block
  written as the original source selected substitution block and the
  right-hand side written using the supplied `Csucc`.

The focused module build has passed:

```text
lean/scripts/lb DLNFibre.DLN.Aoyagi.SelectedEntryNormalCrossing
```

Review:
`review-case2-transition-supplied-successor-reindexed-product-a4.md`.

## Boundary

- The denominator is the normalized displayed coordinate `d = x_(J+1,J+1)`,
  not `targetU = u*d`.
- `Csucc` remains supplied; the theorem only consumes the obligation.
- No source production, suffix production, chart construction, coverage,
  transition regularity, analytic Jacobian/volume theorem, normal crossings,
  pole order, or RLCT extraction is claimed.
- The all-pivot source chart is the finite wrapper; Aoyagi displays only the
  top-left chart.

## Kill Conditions

- If the statement can be read as constructing the obligation or `Csucc`,
  weaken or rename it.
- If the source substitution rewrite is applied to the target Schur block or
  post-pivot residual block, stop: the reproduction only rewrites the
  substitution block.
- If the theorem hides the supplied equality defining `Csucc`, expose it via
  `SourceProductionObligation`.
