# Statement card - A4 Case 1 J-increment payload

## Lean Artifacts

File: `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`.

Names:

- `DLNFibre.DLN.Aoyagi.Case1DisplayedRowStripJIncrementPayload`
- `DLNFibre.DLN.Aoyagi.Case1DisplayedRowStripSuppliedTransitionBoundary.post_weight_eq_new_mul_factoredBase_weight_of_ge`
- `DLNFibre.DLN.Aoyagi.Case1DisplayedRowStripSuppliedTransitionBoundary.jIncrementPayload`
- `DLNFibre.DLN.Aoyagi.Case1DisplayedRowStripSelectedOldPullbackBoundary.post_weight_eq_new_mul_factoredBase_weight_of_ge`
- `DLNFibre.DLN.Aoyagi.Case1DisplayedRowStripSelectedOldPullbackBoundary.jIncrementPayload`
- `DLNFibre.DLN.Aoyagi.Case1DisplayedRowStripSelectedOldSuppliedChartFamilyBoundary.post_weight_eq_new_mul_factoredBase_weight_of_ge`
- `DLNFibre.DLN.Aoyagi.Case1DisplayedRowStripSelectedOldSuppliedChartFamilyBoundary.jIncrementPayload`

## Statement

Lean now packages the finite payload for Aoyagi's displayed Case 1(2)
continuation branch where `J` is increased by one.

The payload records:

- `J+1 <= prefixMinNat n (S+1)`;
- actual-width validity of the fresh label `(S,J+1)`;
- membership of `(S,J+1)` in the new introduced-label domain;
- nonmembership of `(S,J+1)` in the previous introduced-label domain;
- the finite-domain insertion equality;
- the one-step domain cardinality increment;
- post-step exponent certificates over `(S,J+1)`.

The companion recurrence projection states that for every `i >= J+1`,

```text
post.weight i = u * factoredBase.weight i.
```

## Source Role

This is the conservative Lean counterpart of Aoyagi PDF p. 18: after the
displayed Case 1(2) `Q/P` calculation and under the continuation guard
`J+1 <= M(S+1)`, the inductive statement proceeds with `J` increased by one.

The recurrence projection matches the displayed assignments
`b'_(J+1), ..., b'_M(S)` after factoring the old selected variable and
inserting the fresh label. The comparison is with the factored-old base state,
not the substituted source state.

## Proved

- The supplied Case 1(2) boundary exposes the continuation bound.
- The fresh label `(S,J+1)` is actual-width valid.
- The introduced-label finite domain changes by inserting exactly `(S,J+1)`.
- The domain cardinality increases by one.
- The supplied exponent post-data extends the exponent certificate domain to
  `(S,J+1)`.
- The supplied recurrence post-data gives
  `post.weight i = u * factoredBase.weight i` for `i >= J+1`.

## Assumed

- `Case1FirstJumpHypotheses`.
- Actual source column bound `J+1 <= n(S+1)`.
- Supplied factored-base and post recurrence states.
- Supplied recurrence post-data.
- Supplied exponent pre/post data and level-tail invariants.
- Supplied selected-old pullback and chart-family data for the higher wrappers.

## Not Proved

- No construction of the displayed chart or post-state.
- No full Case 1 transition invariant.
- No chart coverage, regularity, transition regularity, or Jacobian formula.
- No Lemma 5 upper-bound classifier, injection, no-extra theorem, or
  back-to-label map.
- No pole order, normal crossings, or RLCT extraction.

## Reproduction and Review

- Reproduction artifact:
  `reproduction-case1-j-increment-payload-a4.md`.
- Review artifact:
  `review-case1-j-increment-payload-a4.md`.

## Verification

- From `lean/`: `lake env lean DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`
  passed.
- From `lean/`: `lake build DLNFibre` passed, with only pre-existing Core
  warnings.
- From `lean/`: `scripts/sorries`: `0 sorry`, `0 #exit`,
  `0 native_decide`, `0 axiom`.
- From repository root: `git diff --check` passed.
- Xhigh review passed after low documentation wording was corrected.
