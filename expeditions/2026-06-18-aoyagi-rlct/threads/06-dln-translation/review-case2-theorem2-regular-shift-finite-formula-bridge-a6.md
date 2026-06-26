# Review - Case 2 regular-shift finite formula bridge

Date: 2026-06-26.

Reviewer: xhigh subagent `Meitner the 2nd`.

Verdict: pass; no findings.

## Checks

- The new theorems use the shifted equality

  ```text
  card(case2ResidualBlockPivotEntries n S J)/2
    + aoyagiTheorem2RegularTerm Lthm H r
  = aoyagiTheorem2Lambda_fromCeilData Lthm ell H r m data
  ```

  rather than the older raw reduced-ratio/full-lambda equality.

- The conclusion is the finite formula hypothesis for

  ```text
  D.jacobianPriorLossShift
    (aoyagiTheorem2RegularVariableCount Lthm H r)
  ```

  not for the reduced datum `D`.

- The chart-count theorem derives the reduced order equality first and then
  passes it through the regular-variable shift, matching the underlying
  `exponentOrder_jacobianPriorLossShift` API.

- Endpoint rank bounds, active-ratio lower bounds, shifted lambda equality,
  and reduced order/chart-count obligations are explicit hypotheses.

- The reproduction and statement card correctly warn not to identify the
  reduced Case 2 ratio alone with the full Theorem 2 lambda.

## Build

Reviewer ran:

```text
lake env lean DLNFibre/DLN/Aoyagi/Case2Theorem2FiniteExponentBridge.lean
```

and reported a clean pass.  Controller separately ran the focused `scripts/lb`
module build.
