# Reproduction - A4 Case 2 displayed Q/P source-substitution continuing handoff

Date: 2026-06-24.

Status: pen-and-paper reproduced; Lean formalised; xhigh reviewed.

## Source Anchor

Aoyagi PDF pp. 20-22, Case 2.  The displayed chart is the chart whose
selected residual-block entry is `(J+1,J+1)`.  This note combines two already
reproduced finite calculations:

- transition to the displayed selected-entry chart on the overlap
  `x_(J+1,J+1) != 0`;
- the target-pivot `Q/P` identity after rewriting only the substituted
  residual block by `Sub_q(u*d,x/d) = Sub_p(u,x)`.

The point is to package the displayed specialization used by the continuing
source-chart certificate, not to prove analytic transition regularity or
source production.

## Reproduction

Let `p` be the current all-pivot source chart and let the displayed target
pivot be

```text
q = (J+1,J+1).
```

Write the source-normalized residual-block coordinates as

```text
x_r = case2SourceSelectedNormalizedMapOfMem p_mem residual r.
```

Assume the displayed normalized coordinate is nonzero:

```text
d = x_q = x_(J+1,J+1) != 0.
```

The finite selected-entry transition to the displayed chart is

```text
targetU = u*d,
targetResidual_r = x_r/d.
```

Then the target chart map agrees with the source chart map because

```text
targetU * targetResidual_r = (u*d)*(x_r/d) = u*x_r,
```

and the displayed selected coordinate becomes `targetResidual_q = 1`.

The target-pivot `Q/P` identity, instantiated at these displayed target data,
has left substituted block

```text
Sub_q(targetU,targetResidual).
```

The transition substitution calculation gives

```text
Sub_q(u*d,x/d) = Sub_p(u,x),
```

so only this left substituted block may be rewritten to the original source
block.  The normalized block in the row-operation vector, the Schur block, the
successor weights, and the transported following factor are still the
displayed target-pivot objects.

For target lower-right indices `i,j`, the denominator-cleared Schur formula is
still

```text
d^2 * Schur_q(targetResidual)_(i,j)
  = d*x_(i,j) - x_(i,J+1)*x_(J+1,j).
```

Under the continuing guard

```text
J+2 <= prefixMinNat n (S+1),
```

the same transition-generated displayed data also satisfy the already-proved
displayed continuing reindexed source-chart certificate.  This is a packaging
step: it places the displayed `Q/P` source-substitution identity and the
continuing source-chart certificate on the same finite transition-generated
data.

## Lean Targets

```text
case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate.case2DisplayedSourceSubstitutionBlock_eq_sourceSelectedSubstitutionBlockOfMem_displayed
case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate.sourceChartTransitionPoint_displayed_QP_sourceSubstitution_frontierBoundaryPackages_of_displayed_normalized_ne_zero
case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate.sourceChartTransitionPoint_displayed_QP_sourceSubstitution_continuingCertificate_of_displayed_normalized_ne_zero
```

## Next Finite Target

The next, sharper finite theorem should push this substitution rewrite into
the displayed reindexed next-source product equality.  That theorem should
rewrite the left displayed `Q/P` substitution block to the original source
selected substitution block while keeping the right side as displayed
transition-generated data and formula-level successor following factor.  This
note does not claim that product-level theorem.

## Boundary

- The denominator is the normalized displayed coordinate `d = x_(J+1,J+1)`,
  not the finite center value `u*d`.
- Only the substituted residual block in the `Q/P` identity is rewritten to
  source coordinates.
- The normalized block, Schur block, successor weights, and transported
  following factor remain displayed target-pivot data.
- The continuing certificate is the existing finite displayed certificate
  instantiated at transition-generated displayed coordinates.
- The reindexed next-source product with the source-side substitution block is
  not proved in this slice.
- This proves no analytic transition regularity, no chart coverage, no
  source-displayed all-pivot atlas, no source-produced global successor object
  or suffixes, no analytic Jacobian/volume theorem, no global normal
  crossings, no pole order, and no RLCT extraction.

## Kill Conditions

- Do not replace `d != 0` by `(u*d) != 0`.
- Do not claim the target-pivot `Q/P` identity has become fully source-facing.
- Do not treat the displayed all-pivot chart index as evidence of analytic
  chart coverage.
- Do not read the continuing certificate as construction of `Csucc`, suffixes,
  successor charts, transition regularity, pole order, or RLCT data.
