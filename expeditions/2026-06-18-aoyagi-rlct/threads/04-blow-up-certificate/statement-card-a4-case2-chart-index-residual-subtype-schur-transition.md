# Statement card - A4 Case 2 chart-index residual-subtype Schur transition

## Lean Artifacts

File:

- `lean/DLNFibre/DLN/Aoyagi/SelectedEntryNormalCrossing.lean`

Name:

- `case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate.sourceSelectedBlock_schurComplement_transition_mul_sq`

## Claim

For source and target chart indices of the Case 2 all-pivot selected-entry
certificate, the target lower-right residual-block Schur coordinate satisfies
the denominator-cleared identity

```text
x_ab^2 * z_ij = x_ab*x_ij - x_ib*x_aj
```

under the explicit normalized-coordinate overlap hypothesis `x_ab != 0`.
Here `i` and `j` are residual-row and residual-column subtype complement
indices around the target pivot, read in source coordinates as `i.1.1` and
`j.1.1`.

## Inputs Kept Explicit

- source and target chart indices;
- the normalized nonzero denominator;
- residual-row and residual-column subtype complement indices;
- a total ambient residual-coordinate function.

## Not Proved

No analytic transition regularity, no chart coverage, no open-neighbourhood
gluing, no source-displayed all-pivot atlas, no successor residual/following
factor production, no analytic Jacobian/volume theorem, no global normal
crossings, no pole order, and no RLCT extraction.

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

The full-library build completes with pre-existing Core/style warnings outside
this slice.  Review:

```text
threads/04-blow-up-certificate/review-case2-chart-index-residual-subtype-schur-transition-a4.md
```
