# Review - A2 retained-passive lower-left L recursion

Date: 2026-06-26.

Reviewer: xhigh read-only reviewer `Plato the 3rd`.

## Scope

Audit the uncommitted Lean additions in
`lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinates.lean`:

```text
ChartLocalSuffixState.suffixState_lowerLeftBlock_L_retainedPassiveFixedBaseEdgeMatrix_castSucc
ChartLocalSuffixState.suffixState_lowerLeftBlock_L_retainedPassiveFixedBaseEdgeMatrix_castSucc_currentCtop
```

The review checked sign/order, use of the generic
`suffixState_L_eq_lowerUnitriangular` theorem, the current-`Ctop` rewrite, and
whether the statements overclaim beyond finite suffix-state algebra.

## Verdict

PASS.  No blocking findings.

## Checks

- The sign and multiplication order match the generic `step` formula:

  ```text
  -(D_{p+1} * A3_p * (Ctop_{p+1} * A1_p)^-1).
  ```

- Lower-unitriangular multiplication is used correctly: the lower-left block is
  `X + F3next`, where `X` is the negative contribution.  This is equivalent to
  `F3_{p+1} - ...`; the additive order is harmless.
- `suffixState_L_eq_lowerUnitriangular` is used only to witness that the next
  suffix-state `L` has form `[I,0;F3next,I]` and then recover
  `lowerLeftBlock S.L = F3next`.
- The current-`Ctop` rewrite is correct: it uses
  `Ctop_p = Ctop_{p+1} * A1_p` only under the displayed inverse and makes no
  extra cancellation claim.
- The statements remain finite suffix-state algebra.  They do not claim an
  iterated sum, solve `A3_last`, or assert source-chart/coverage results.

## Caveat

Lean's matrix inverse is total.  These recurrence statements therefore do not
themselves expose a separate determinant-unit side condition for the displayed
`Ctop_p^-1`.  This is consistent with the existing algebraic style, but any
analytic or chart-regularity use must still combine the recurrence with the
already-proved determinant-unit theorem for suffix-state `Ctop`.

## Nonclaims

No iterated `F3_0` sum, no `A3_last` solve, no retained-passive
coordinate-domain theorem, no source-rank coverage, no source/image equality,
no source-measure pushforward, no density/Jacobian theorem, no normal
crossings, no pole order, and no RLCT.
