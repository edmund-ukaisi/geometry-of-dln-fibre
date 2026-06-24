# Statement card - A4 Case 2 residual-subtype Schur transition

## Lean Artifact

File:

- `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`

Name:

- `case2SourceSelectedNormalizedBlockOfMem_schurComplement_transition_mul_sq`

## Claim

The Case 2 denominator-cleared selected-entry Schur transition formula also
holds for the residual-row and residual-column subtype complements used by the
target lower-right `Q/P` block:

```text
x_ab^2 * z_ij = x_ab*x_ij - x_ib*x_aj.
```

Here `i` and `j` are residual-block subtype complement indices around the
target pivot row and column, read in source coordinates as `i.1.1` and
`j.1.1`.

## Inputs Kept Explicit

- supplied source and target pivot memberships in
  `case2ResidualBlockPivotEntries n S J`;
- the normalised nonzero denominator `x_ab`;
- residual-row and residual-column subtype complement indices;
- a total ambient residual-coordinate function.

## Not Proved

No analytic transition regularity, no chart coverage, no open-neighbourhood
gluing, no source-displayed all-pivot atlas, no successor residual/following
factor production, no analytic Jacobian/volume theorem, no global normal
crossings, no pole order, and no RLCT extraction.

## Verification

The current gates passed:

```text
lean/scripts/lb DLNFibre.DLN.Aoyagi.BlowupArithmetic
lean/scripts/lb DLNFibre
lean/scripts/sorries
git diff --check
```

The sorry audit reported `0 sorry`, `0 #exit`, `0 native_decide`, and
`0 axiom`.  The full build has pre-existing unrelated Core/style warnings.
