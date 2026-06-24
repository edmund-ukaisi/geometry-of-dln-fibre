# Statement card - A4 Case 2 source-selected Schur complement

## Lean Artifacts

File:

- `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`

Names:

- `pivotFirstSchurComplement_apply`
- `selectedEntryNormalizedMap_schurComplement_transition_mul_sq`
- `case2SourceSelectedNormalizedBlockOfMem_schurComplement_apply`

## Claim

After a selected residual-block pivot has been normalised to `1`, the
lower-right block produced by Aoyagi's finite `Q/P` algebra has entry

```text
D_ij - x_i*y_j.
```

On a selected-entry overlap with target pivot coordinate `x_ab != 0`, the
target Schur coordinate satisfies

```text
x_ab^2 * z_ij^(q) = x_ab*x_ij - x_ib*x_aj.
```

The Case 2 wrapper states the same scalar `D - x*y` formula for source
coordinates attached to a supplied residual-block pivot.

## Inputs Kept Explicit

- the selected row and column pivots;
- off-pivot row and column complement indices;
- for the overlap formula, the nonzero normalised denominator
  `selectedEntryNormalizedMap sourcePivot residual targetPivot`;
- for the Case 2 wrapper, finite residual-block pivot membership.

## Not Proved

No chart coverage, no analytic transition regularity, no open-neighbourhood
statement, no source-displayed all-pivot atlas, no successor/suffix production,
no analytic Jacobian/volume theorem, no global normal crossings, no pole order,
and no RLCT extraction.

## Verification

Current focused check passed:

```text
lean/scripts/lb DLNFibre.DLN.Aoyagi.BlowupArithmetic
lean/scripts/lb DLNFibre
lean/scripts/sorries
git diff --check
```

Independent xhigh review passed with a source-access caveat; durable artifact:
`review-case2-source-selected-schur-complement-a4.md`.  The sorry audit
reported `0 sorry`, `0 #exit`, `0 native_decide`, and `0 axiom`.  The full
build still reports pre-existing unrelated Core/style warnings.
