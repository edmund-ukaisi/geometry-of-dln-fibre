# Statement card - A4 Case 1 source-substituted local handoff

## Lean Artifacts

File: `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean` @
`54d9148b68be9354574f4fc1225e76efb96c336d`.

Names:

- `DLNFibre.DLN.Aoyagi.Case1DisplayedRowStripSuppliedTransitionBoundary.sourceOrder_identity_substitutedSourceWeights`

## Statement

Lean now combines the selected-old source substitution boundary with the
displayed row-strip local handoff.

The resulting theorem states the displayed top-left Case 1(2) source-order
identity with the left diagonal written directly as substituted source
recurrence weights:

```text
source.weight (case2ResidualRowLevel n S J i).
```

The right diagonal remains the supplied post-state recurrence weights.

## Source Role

This is the source-facing form of the printed Case 1(2) displayed row-strip
handoff on Aoyagi PDF p. 17. It replaces the explicit recurrence
`mulStepAt factoredBase.step u (J+J1)` by a supplied substituted source state
whose step function is identified with that recurrence using supplied
selected-old factorisation data, first-jump data, and
`level = factoredBase.level`.

## Proved

- The local handoff theorem can be rewritten from explicit `mulStepAt`
  source weights to substituted `source.weight` row weights.
- The rewrite uses supplied selected-old factorisation data and an explicit
  equality between the local level map and `factoredBase.level`.

## Assumed

- The displayed row-strip supplied transition boundary.
- Supplied selected-old factored-base data for the substituted source
  recurrence.
- `level = factoredBase.level`.
- A normalized displayed pivot block with pivot entry equal to `1`.

## Not Proved

- No construction of the substituted source state.
- No selected-old chart construction.
- No construction of the factored-base or post states.
- No hidden old-label source-validity theorem beyond the supplied data.
- No chart coverage, regularity, transition regularity, or Jacobian formula.
- No normal crossings or RLCT extraction.

## Reproduction and Review

- Reproduction artifact:
  `reproduction-case1-source-substituted-local-handoff-a4.md`.
- Review artifact:
  `review-case1-source-substituted-local-handoff-a4.md`.

## Verification

- From `lean/`: `lake env lean DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`
  passed.
- From `lean/`: `lake build DLNFibre` passed.
- From `lean/`: `./scripts/sorries`: `0 sorry`, `0 #exit`,
  `0 native_decide`, `0 axiom`.
- From repository root: `git diff --check` passed.
- Xhigh review passed with minor documentation wording cleanup.
