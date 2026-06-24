# Statement card - A4 Case 2 displayed transition microcertificate contribution

## Lean Artifact

File:

- `lean/DLNFibre/DLN/Aoyagi/SelectedEntryNormalCrossing.lean`

Name:

- `case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate.sourceChartTransitionPoint_displayed_microcertificateContribution_summary_of_displayed_normalized_ne_zero`

## Claim

On the overlap where the displayed normalized coordinate
`x_(J+1,J+1)` is nonzero, transition an arbitrary source chart from our finite
all-pivot selected-entry wrapper to Aoyagi's displayed Case 2 chart and
package:

- the displayed continuing finite center-square/formal-Jacobian certificate
  for the transition-generated displayed data;
- source-facing finite loss evaluation and loss monomial identity;
- target displayed loss-unit and formal Jacobian/prior determinant identities;
- the displayed chart's finite ratio/minimum/count/order contribution summary.

## Proved

Finite selected-entry chart algebra and finite exponent bookkeeping for the
displayed transition point.  The ratio/minimum is

```text
((prefixMinNat n S - J) * (n(S+1) - J)) / 2,
```

and the displayed chart count/minimum-count/order fields in the local finite
certificate are all `1`.

## Assumed

The theorem assumes:

- stage and ambient bounds `hS : 1 <= S`, `hSL : S <= L`;
- continuation and next-center bounds `hcont : J+1 <= prefixMinNat n (S+1)`
  and `hnext : J+2 <= prefixMinNat n (S+1)`;
- a recurrence state `pre`;
- the existing exponent, level, and least-value-gap hypotheses
  `exponentPre`, `levelInv`, and `leastValueGap`;
- a source chart index `sourceChart`;
- the displayed normalized-coordinate nonzero hypothesis `hdisplayed`.

## Cited

None in Lean.

## Deferred

Analytic chart construction, transition regularity, chart coverage, source
production of successor/following data, global A0 normal crossings, pole
order, and RLCT extraction.

## Verification

Focused build passed:

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

Independent review artifact:

```text
threads/04-blow-up-certificate/review-case2-displayed-transition-microcertificate-contribution-a4.md
```
