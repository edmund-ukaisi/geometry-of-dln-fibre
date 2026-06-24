# Review - Theorem 2 rank-width regular-shift bridge

Reviewer: xhigh `Ramanujan the 3rd`.

Status: passed, with scope correction incorporated.

## Verdict

The rank-width final bridge is legitimate and is the right source-hypothesis
reduction.  It should be callable without the A2-specific parameters
`W`, `B`, `Cedge`, `rEdge`, `x`, and `hH`; the full source-range rank-width
hypothesis `hr` is the correct input.

## Scope Correction

Endpoint rank-width bounds suffice only for the finite regular-variable
shift.  The final Definition 3 handoff still needs the full `hr` hypothesis
because selected-width side facts use rank-width at every selected cutpoint.
The Lean bridge keeps full `hr` and passes it to both the Definition 3
source-data final handoff and the finite regular-variable shift constructor.

## API Check

The new rank-width bridge is placed in
`Theorem2RankWidthRegularShiftBridge.lean`.  The existing source-rank bridge
now derives `hr` from `paperEndpointFixedBaseSourceRankStratum_sourceRangeRankWidth`
and delegates to the rank-width bridge.

## Nonclaims

The shifted extraction hypothesis remains supplied.  No regular-suspension
chart construction, analytic ideal transport, Aoyagi Lemma 1, active-ratio
bound, chart-count theorem, normal-crossing production, pole-order theorem, or
RLCT extraction is proved here.
