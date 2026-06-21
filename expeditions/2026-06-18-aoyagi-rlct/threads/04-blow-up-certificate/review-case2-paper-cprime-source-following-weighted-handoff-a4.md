# Review - A4 Case 2 paper-Cprime source-following weighted handoff

Status: reviewed and formalised.

## Scope Check

The target specializes the source-side weighted lower-row handoff to the paper
transported factor `C' = Q^-1 C` and rewrites the lower tail as the next
same-stage source following factor.  It adds no chart production claim.

## Risks

- The theorem name must not suggest source production of the full successor
  matrix `C'^(S+1)`.
- The theorem must keep the lower-row diagonal weights.
- The theorem must not include the pivot row.
- The theorem must keep corrected post-data as supplied/concrete data, not
  coordinate-derived data.

## Verdict

Source review accepts this as a finite Aoyagi Case 2 lower-row calculation,
and Lean formalisation landed with the source-side `P_q` row operation, the
successor lower-row diagonal, and no identification of the full transported
factor or full next `C'^(S+1)` with the next source following factor.

## Xhigh Checks

Source checker `Rawls` accepted the target as source-faithful finite algebra
from Aoyagi Case 2 pp. 19-22.  The review required one wording fix: Aoyagi's
source display carries the common chart factor `u_{S,J+1}`; the displayed
`P diag(b') D'' C' = diag(b') D''' C'` line in the reproduction is the
isolated finite row-operation identity after the common factor is accounted
for in the weight data.

Lean API scout `Lorentz` typechecked the helper and theorem shape with
`lake env lean --stdin`.  The landed theorem name is:

```text
Case2DisplayedSuppliedChartFamilyBoundary.sourceChartMap_paperCprimeWeightedLowerRows_withCorrectedPostData
```
