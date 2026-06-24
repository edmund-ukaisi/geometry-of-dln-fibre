# Statement card - A4 Case 2 transition-generated Q/P source-substitution package

## Lean Artifact

File:

- `lean/DLNFibre/DLN/Aoyagi/SelectedEntryNormalCrossing.lean`

Name:

- `case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate.sourceChartTransitionPoint_sourceSelectedQP_sourceSubstitution_package_of_target_normalized_ne_zero`

## Claim

On a normalized source-to-target selected-entry overlap, the
transition-generated target-pivot `Q/P` identity may have its left substituted
residual block rewritten back to the original source substitution block.

With `d = x_q != 0`,

```text
Sub_q(u*d, x/d) = Sub_p(u, x),
```

and the target-pivot `Q/P` identity is restated with `Sub_p(u,x)` in that
left-side factor.

## Inputs Kept Explicit

- source and target all-pivot chart indices;
- source selected variable `u` and residual coordinates;
- nonzero target normalized coordinate;
- supplied Case 2 chart-family boundary;
- source recurrence/exponent/least-value data;
- following-factor parameter `C`.

## Not Proved

Only the substituted residual block is rewritten to source chart coordinates.
The normalized block, target Schur block, target successor weights, and
transported following factor remain target-pivot data.

No analytic transition regularity, no chart coverage, no open-neighbourhood
gluing, no source-displayed all-pivot atlas, no source production of a global
successor object or suffixes, no analytic Jacobian/volume theorem, no global
normal crossings, no pole order, and no RLCT extraction.

## Verification

Controller gates for this slice:

```text
lean/scripts/lb DLNFibre.DLN.Aoyagi.SelectedEntryNormalCrossing
lean/scripts/lb DLNFibre
lean/scripts/sorries
git diff --check
```

The sorry audit reports:

```text
Summary: 0 sorry, 0 #exit, 0 native_decide, 0 axiom
```

Independent review artifact:

```text
threads/04-blow-up-certificate/review-case2-transition-generated-qp-source-substitution-a4.md
```
