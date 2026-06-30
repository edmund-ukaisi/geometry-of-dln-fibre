# Review - A2 Case 2 passive theta relative raw-order endpoint sector

Date: 2026-06-30.

Status: PASS.

## Source and Scope Review

Reviewer: Newton, xhigh effort.

Result: PASS.

Newton checked that the theorem stays within the intended local chart-produced
slice: one shrink carries endpoint-sector measurability, pointwise
raw-order/source-chart identities, and measure pushforward equalities.  The
review found no determinant-chart Haar transport, raw-order Haar transport,
source-prior identification, exact passive-sector pushforward, source-image
equality, source-rank coverage, normal-crossing, pole-order, or RLCT
overclaim.

Residual noted by Newton: the original prose said the result held for every
source measure, while the first version of the Lean statement fixed
`sourceMeasure` before choosing `V`.  The theorem has since been strengthened:
`V` is now chosen first, and the pushforward clause quantifies over every
`sourceMeasure`.

## Lean/API Review

Reviewer: Goodall, xhigh effort.

Initial result: FAIL, documentation/API mismatch.

Goodall found that the reproduction note listed endpoint topology-tuple
determinant-chart membership among the recorded pointwise facts, while the
first version of the exported theorem used that membership internally but did
not return it in the pointwise package.

Resolution: the theorem has been strengthened to include endpoint
topology-tuple determinant-chart membership in the returned pointwise package.
The statement card now lists this fact explicitly.

First re-review: Lean/API PASS, documentation FAIL.  Goodall confirmed that
the revised theorem chooses `V` before the final `forall sourceMeasure`
clause, exports determinant-chart membership in the pointwise package, and has
sound a.e. measurability plus map-map/map-congr bookkeeping.  The only
remaining issue was that the statement card's Assumed section still described
`sourceMeasure` as an assumption rather than a later quantified variable.

Resolution: the Assumed section now states that `sourceMeasure` is not used to
choose `V` and is quantified afterward in the final pushforward clause.

Final re-review: PASS.  Goodall found no remaining issues.

## Verification

Focused Lean checks passed after the fixes:

```text
lake env lean -E warning DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaSourceMeasure.lean
```

Final full verification suite passed:

```text
lake env lean -E warning DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaSourceMeasure.lean
env LEAN_NUM_THREADS=3 lake build DLNFibre.DLN.Aoyagi.RetainedPassiveCase2PassiveThetaSourceMeasure
lake env lean -E warning DLNFibre.lean
./scripts/sorries
git diff --check
```

`./scripts/sorries` reported a clean placeholder/debug-marker inventory.
Touched-file marker scans returned no matches.
