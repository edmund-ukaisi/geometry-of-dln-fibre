# Review - A2 retained-passive lower-left L tail sum

Date: 2026-06-26.

Reviewer: xhigh read-only reviewer `Pauli the 3rd`.

## Scope

Audit the uncommitted Lean additions in
`lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinates.lean`:

```text
ChartLocalSuffixState.retainedPassiveLowerLeftTailSum
ChartLocalSuffixState.retainedPassiveLowerLeftTailSum_self
ChartLocalSuffixState.retainedPassiveLowerLeftTailSum_castSucc
ChartLocalSuffixState.suffixState_lowerLeftBlock_L_retainedPassiveFixedBaseEdgeMatrix_eq_tailSum
ChartLocalSuffixState.suffixState_lowerLeftBlock_L_retainedPassiveFixedBaseEdgeMatrix_zero_eq_tailSum
ChartLocalSuffixState.suffixState_Ctop_retainedPassiveFixedBaseEdgeMatrix
ChartLocalSuffixState.retainedPassiveLowerLeftProductTailSum
ChartLocalSuffixState.retainedPassiveLowerLeftProductTailSum_self
ChartLocalSuffixState.retainedPassiveLowerLeftProductTailSum_castSucc
ChartLocalSuffixState.retainedPassiveLowerLeftTailSum_eq_productTailSum
ChartLocalSuffixState.suffixState_lowerLeftBlock_L_retainedPassiveFixedBaseEdgeMatrix_eq_productTailSum
ChartLocalSuffixState.suffixState_lowerLeftBlock_L_retainedPassiveFixedBaseEdgeMatrix_zero_eq_productTailSum
```

The review checked indexing, signs, product order, terminal base case,
suffix-state field readback, and whether the statements overclaim beyond finite
algebra.

## Verdict

PASS.  No blocking findings.

## Checks

- `p.succ` is used for the next suffix-state residual block `D_{p+1}`, while
  `p.castSucc` is used for the current top block `Ctop_p`.
- The terminal lower-left tail is correctly zero because the terminal suffix
  state has `L=I`.
- The `Ctop` product theorem uses `residualFactorProduct` over the constant
  vertex family `rho`, with the same right-appending order as
  `residualFactorProduct_castSucc`.
- The product-tail `D` summand uses `residualFactorProduct C last p.succ`,
  excluding the current factor `C_p`, as required by the recurrence.
- No inverse of `D` or `C` is introduced.  The displayed `Ctop` inverse remains
  Lean's total matrix inverse expression.
- The equality theorems retain the `hA1` determinant-unit hypothesis and remain
  finite suffix-state algebra, not chart coverage or analytic extraction.

## Verification

The reviewer also checked that

```text
cd lean
lake env lean DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinates.lean
```

passes.  The controller separately runs the project `scripts/lb` checks before
the checkpoint commit.

## Nonclaims

No `A3_last` solve, no retained-passive coordinate-domain theorem, no
source-rank coverage, no source/image equality, no source-measure pushforward,
no density/Jacobian theorem, no normal crossings, no pole order, and no RLCT.
