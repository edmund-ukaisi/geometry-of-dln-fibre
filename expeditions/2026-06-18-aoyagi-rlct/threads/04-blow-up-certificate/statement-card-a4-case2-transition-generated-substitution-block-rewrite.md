# Statement card - A4 Case 2 transition-generated substitution-block rewrite

## Lean Artifacts

Files:

- `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`
- `lean/DLNFibre/DLN/Aoyagi/SelectedEntryNormalCrossing.lean`

Names:

- `case2SourceSelectedSubstitutionBlockOfMem_transition_eq_of_target_normalized_ne_zero`
- `case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate.sourceChartTransitionPoint_sourceSelectedSubstitutionBlock_eq_of_target_normalized_ne_zero`

## Claim

On the overlap where a target selected-entry normalized coordinate is nonzero,
the transition-generated target selected variable and residual coordinates
give the same finite Case 2 residual-block substitution matrix as the original
source chart.

In source-normalized notation, with `d = x_q != 0`,

```text
Sub_q(u*d, x_/d) = Sub_p(u, x).
```

## Inputs Kept Explicit

- source residual-block pivot membership;
- target residual-block pivot membership;
- source selected variable `u` and residual coordinates;
- nonzero target normalized coordinate;
- chart-index wrapper data for the all-pivot certificate.

## Not Proved

No analytic transition regularity, no chart coverage, no open-neighbourhood
gluing, no source-displayed all-pivot atlas, no source production of a global
successor object or suffixes, no analytic Jacobian/volume theorem, no global
normal crossings, no pole order, and no RLCT extraction.

This is equality of finite substitution blocks.  It is not equality of
normalized blocks and not the target Schur-complement or `Q/P` reduced-block
rewrite.

## Verification

Passed:

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

Review artifact:

- `review-case2-transition-generated-substitution-block-rewrite-a4.md`

The full `DLNFibre` build completed with pre-existing Core/style warnings
outside this slice.
