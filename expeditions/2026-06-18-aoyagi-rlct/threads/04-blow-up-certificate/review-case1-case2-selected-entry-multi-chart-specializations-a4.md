# Review - A4 Case 1/Case 2 selected-entry multi-chart specializations

Date: 2026-06-23.

Reviewer: xhigh independent reviewer `Mendel`.

Verdict: pass, no blocking findings.

## Scope Reviewed

- `lean/DLNFibre/DLN/Aoyagi/SelectedEntryNormalCrossing.lean`
- `lean/DLNFibre/DLN/Aoyagi/Case1FiniteExponentBridge.lean`
- `threads/04-blow-up-certificate/reproduction-case1-case2-selected-entry-multi-chart-specializations-a4.md`

The review focused on formalisation accuracy, mathematical scope, import-cycle
risk, hidden dependence on the quiver paper, and citation-boundary leakage.

## Findings

No blocking issues were found.

The main risk was the Case 2 theorem
`case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate.localExponentCoordinateBridge_anyChart`.
The proof relates an arbitrary finite pivot chart to the displayed continuing
bridge only by equality of erased-center cardinalities.  This is acceptable
because the returned structure records only exponent-array equalities, not a
source-chart identity.  The Lean docstring explicitly says this is only an
exponent-array adapter and does not identify non-displayed pivots with
Aoyagi's displayed source chart.

The reviewer also checked that the all-pivot Case 1 and Case 2 wrappers stay
finite/bookkeeping-only in their documentation, and that the Case 1 bridge
caveat similarly avoids source-production claims for arbitrary pivots.

## Boundary Confirmed

The slice does not use the quiver paper, does not add a new cited boundary,
and does not claim:

- arbitrary-pivot source-coordinate formulas;
- source-produced `Q/P` transport;
- analytic chart coverage;
- transition regularity;
- analytic Jacobian or volume-form control;
- global A0 active-ratio lower bounds or full chart-count/order theorems;
- pole order or RLCT extraction.

## Reviewer Verification

The reviewer ran:

```text
lean/scripts/lb DLNFibre.DLN.Aoyagi.Case1FiniteExponentBridge
git diff --check
```

Both passed.
