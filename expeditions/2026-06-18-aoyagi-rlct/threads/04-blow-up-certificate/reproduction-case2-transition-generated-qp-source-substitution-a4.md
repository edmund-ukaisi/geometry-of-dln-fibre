# Reproduction - A4 Case 2 transition-generated Q/P source-substitution package

Date: 2026-06-24.

Status: pen-and-paper reproduced; Lean formalised; review pending.

## Source Anchor

Aoyagi PDF pp. 20-22, Case 2.  The selected-entry overlap changes from a
source pivot to a target pivot, then the target-pivot `Q/P` calculation uses
the target normalized block and its lower-right Schur expression.

This note records a finite reducer after the substitution-block rewrite has
been formalised.  Only the substituted residual block on the left side of the
target-pivot `Q/P` identity is rewritten back to source chart coordinates.
The target normalized block, target Schur expression, target successor weights,
and transported following factor remain target-pivot objects.

## Reproduction

Let the source pivot be `p` and the target pivot be `q = (a,b)`.  Write the
source-normalized residual-block coordinates as

```text
x_r = case2SourceSelectedNormalizedMapOfMem p_mem residual r.
```

Assume the target normalized coordinate is nonzero:

```text
d = x_q != 0.
```

The transition-generated target chart data are

```text
targetU = u*d,
targetResidual_r = x_r/d.
```

The already-formalised transition facts give:

1. the target chart map of the transition point equals the original source
   chart map;
2. the target substitution block equals the original source substitution
   block:

```text
Sub_q(u*d, x/d) = Sub_p(u, x).
```

Now instantiate the existing target-pivot source-selected `Q/P` identity at
the transition-generated data.  Its left substituted residual block is

```text
Sub_q(targetU, targetResidual).
```

Using the substitution-block equality, rewrite only that factor to

```text
Sub_p(u, x).
```

The normalized block in the row-operation vector and on the Schur side remains
the target block

```text
A = NormalizedBlock_q(targetResidual),
```

and the transported following factor remains

```text
Ctr = TransportedFollowingFactor_q(targetResidual, C).
```

For target lower-right indices `i,j`, the Schur term still satisfies the
denominator-cleared target-overlap formula

```text
d^2 * Schur_q(targetResidual)_(i,j)
  = d*x_(i,j) - x_(i,b)*x_(a,j).
```

Thus the package records four finite facts for the same transition-generated
target data:

1. chart-map equality;
2. substitution-block equality;
3. the target-pivot `Q/P` identity with its left substituted block rewritten
   to the original source substitution block;
4. the denominator-cleared target Schur formula.

## Lean Target

```text
case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate.sourceChartTransitionPoint_sourceSelectedQP_sourceSubstitution_package_of_target_normalized_ne_zero
```

## Boundary

- The denominator is the normalized target coordinate `d = x_q`, not the
  finite center value `u*d`.
- Only the substituted residual block on the left side is rewritten to source
  chart coordinates.
- The normalized block, target Schur block, target successor weights, and
  transported following factor remain target-pivot data.
- This does not turn the target-pivot `Q/P` identity into a source-pivot
  `Q/P` identity.
- This proves no analytic transition regularity, no open-neighbourhood
  gluing, no chart coverage, no source-displayed all-pivot atlas, no
  source-produced global successor object, no suffix production, no analytic
  Jacobian/volume theorem, no global normal crossings, no pole order, and no
  RLCT extraction.

## Kill Conditions

- Do not replace `d != 0` by `(u*d) != 0`.
- Do not describe this as fully source-facing; only the substituted block is
  source-side.
- Do not treat the target Schur formula as source production of successor
  residual matrices or following factors.
- Do not promote the supplied `ChartRegular`/`TransitionRegular` fields to
  proved analytic regularity.
- Do not use all-pivot chart indices as evidence that Aoyagi prints every
  pivot chart.
