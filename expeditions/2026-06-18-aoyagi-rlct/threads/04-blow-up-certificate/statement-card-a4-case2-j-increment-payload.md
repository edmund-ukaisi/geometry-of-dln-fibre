# Statement card - A4 Case 2 J-increment payload

## Lean Artifacts

File: `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`.

Names:

- `DLNFibre.DLN.Aoyagi.Case2DisplayedJIncrementPayload`
- `DLNFibre.DLN.Aoyagi.Case2DisplayedSuppliedChartFamilyBoundary.post_weight_eq_new_mul_pre_weight_of_ge`
- `DLNFibre.DLN.Aoyagi.Case2DisplayedSuppliedChartFamilyBoundary.jIncrementPayload`

## Statement

Lean now packages the finite payload for Aoyagi's displayed Case 2
continuation branch where `J` is increased by one.

The payload records:

- `J+1 <= prefixMinNat n (S+1)`;
- the corrected Case 2 new-label certificate for `(S,J+1)`;
- actual-width validity of the fresh label `(S,J+1)`;
- membership of `(S,J+1)` in the new introduced-label domain;
- nonmembership of `(S,J+1)` in the previous introduced-label domain;
- the finite-domain insertion equality;
- the one-step domain cardinality increment;
- corrected numerator identities for the new label;
- post-step exponent certificates over `(S,J+1)`.

The companion recurrence projection states that for every `i >= J+1`,

```text
post.weight i = u * pre.weight i.
```

## Source Role

This is the conservative Lean counterpart of Aoyagi PDF p. 21: after the
displayed Case 2 `Q/P` calculation and under the continuation guard
`J+1 <= M(S+1)`, the inductive statement proceeds with `J` increased by one.

Unlike Case 1(2), Case 2 has the recorded printed-vector mismatch. This slice
therefore uses the corrected Case 2 exponent post-data already isolated in
Lean and does not claim that the printed vector supplies the corrected
terminal exponent.

## Proved

- The displayed Case 2 boundary exposes the non-strict next-state bound.
- The fresh label `(S,J+1)` is actual-width valid.
- The introduced-label finite domain changes by inserting exactly `(S,J+1)`.
- The domain cardinality increases by one.
- The supplied recurrence post-data gives
  `post.weight i = u * pre.weight i` for `i >= J+1`.
- The supplied corrected exponent post-data gives the corrected new-label
  numerator and extends the exponent certificate domain to `(S,J+1)`.

## Assumed

- Supplied displayed Case 2 boundary data.
- Supplied recurrence post-data.
- Supplied corrected Case 2 exponent post-data.
- Supplied exponent pre-data, level invariants, and least-value gap.
- Supplied chart-family regularity data.

## Not Proved

- No proof that Aoyagi's printed Case 2 vector has the corrected numerator.
- No construction of the displayed chart or post-state.
- No nonempty residual block after the increment.
- No successor chart-family construction or full next `C'^(S+1)`.
- No transition invariant, Jacobian formula, normal crossings, pole order, or
  RLCT extraction.

## Reproduction and Review

- Reproduction artifact:
  `reproduction-case2-j-increment-payload-a4.md`.
- Review artifact:
  `review-case2-j-increment-payload-a4.md`.

## Verification

- From `lean/`: `lake env lean DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`
  passed.
- From `lean/`: `lake build DLNFibre` passed, with only pre-existing Core
  warnings.
- From `lean/`: `scripts/sorries`: `0 sorry`, `0 #exit`,
  `0 native_decide`, `0 axiom`.
- From repository root: `git diff --check` passed.
- Xhigh review passed with no math or Lean blockers.
