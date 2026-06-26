# Review - A2 product-step A1 formal inverse

Date: 2026-06-26.

Reviewer: xhigh independent explorer `Avicenna the 2nd`.

## Verdict

PASS, no blocking issues.

## Checked Lean Scope

The reviewer checked `ProductReduction.lean` around the new inverse lemmas.
The extracted theorems

```text
productReductionStepCoordinate_left_inverse_of_isUnit_A1
productReductionStepCoordinate_right_inverse_of_isUnit_A1
```

are scoped as record-level formal inverse statements.  The previous
determinant-chart inverse names remain wrappers, so the analytic chart/domain
API is unchanged.

## Checked Algebra

The proofs use only `IsUnit A1.det`.  The `C1` and `Ctop` determinant-unit
hypotheses appear only in the older wrapper theorems for determinant-chart and
regular-expression scope.

The signs and block roles match the Aoyagi pp. 10-13 coordinate substitution:
the Schur residual is `A4 - A3 A1^{-1} A2`, `F2 = -A1^{-1} A2`, and no inverse
of the passive residual block `D` appears.

## Scope Check

No overclaim was found.  The new theorems do not assert analytic charts,
source/image equality, measure transport, normal crossings, pole order, or
RLCT extraction.

## Verification

The controller ran the repo build wrapper:

```text
cd lean
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre.DLN.Aoyagi.ProductReduction
```

The focused build passed on 2026-06-26.
