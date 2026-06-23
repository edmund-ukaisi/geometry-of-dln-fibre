# Review - A4 Case 2 continuing reindexed source-chart certificate

Date: 2026-06-23.

Verdict: PASS.

Reviewers:

- source/math fidelity: `Einstein the 2nd`, xhigh;
- Lean/API: `Popper the 2nd`, xhigh.

## Source/Math Findings

No blocking source/math issue was found.  The new package stays A4-local.

`Case2DisplayedReindexedNextSourceProductEq` is only a finite reindexed product
equality.  The successor following factor is explicitly the formula-level
`case2DisplayedSourceSuccessorFollowingFactor`, not a source-produced object.

`Case2DisplayedContinuingReindexedSourceChartCertificate` packages the
displayed selected-entry chart facts, finite center principalization,
corrected post-data, next-center nonemptiness under `hnext`, and the reindexed
source product.  It does not expose chart coverage, transition regularity,
Jacobian/unit/loss monomial data, normal crossings, pole order, or RLCT data.

`sourceChartMap_continuingReindexedSourceChartCertificate` correctly requires
`J+2 <= prefixMinNat n (S+1)` for the continuing residual center and uses the
corrected post-weight convention.

Aoyagi pp. 19-22 support only the displayed top-left Case 2 selected-entry
chart and the `Q/P` reindex algebra used here.  Aoyagi p. 6 is only context
for why A0 still needs actual loss/Jacobian monomial identities and unit
fields.  The printed `b'_i = u b_i` line and the later outside `u diag(b')`
display remain flagged as not simultaneously literal.

## Lean/API Findings

No blocking API issue was found.  The certificate is proof-only and scoped
correctly.  The existential row-operation witness `q` inside the Prop-valued
structure is acceptable for the current proof-facing API; it would only be a
problem if downstream code needed computational access to the witness.

Non-vacuity is explicit: the constructor requires `hnext`, and
`nextCenter_nonempty` is the finite-set form of the same continuing guard.

Minor residual risk: `Case2DisplayedReindexedNextSourceProductEq` duplicates a
long definitional matrix equality, and the constructor relies on
`simpa [Case2DisplayedReindexedNextSourceProductEq]`.  This is not a
correctness issue, but the proof may be brittle under upstream statement
normalization changes.

## Checks

Reviewers and controller ran:

```text
cd lean && lake env lean DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean
cd lean && lake build DLNFibre.DLN.Aoyagi.BlowupArithmetic
git diff --check
```

Additional aggregate checks were run by the controller before commit.
