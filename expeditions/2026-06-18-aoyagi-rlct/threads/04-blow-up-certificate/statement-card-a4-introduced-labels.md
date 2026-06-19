# Statement card - A4 introduced labels

## Lean artifacts

File: `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`.

Names:

- `DLNFibre.DLN.Aoyagi.introducedLabel`
- `DLNFibre.DLN.Aoyagi.actualWidthLabel_of_introducedLabel`
- `DLNFibre.DLN.Aoyagi.introducedLabel_of_lt_stage`
- `DLNFibre.DLN.Aoyagi.introducedLabel_of_eq_stage_le`
- `DLNFibre.DLN.Aoyagi.introducedLabel_mono_J`
- `DLNFibre.DLN.Aoyagi.not_introducedLabel_case2_new_before`
- `DLNFibre.DLN.Aoyagi.introducedLabel_case2_new_after`
- `DLNFibre.DLN.Aoyagi.introducedLabel_case2_new_after_of_prefixBound`

## Statement

At state `(S,J)`, Lean defines an introduced label by

```text
actualWidthLabel L n s k
and
(s < S or (s = S and k <= J)).
```

Thus all labels from earlier layers have been introduced, and the current layer
has been introduced exactly through `J`. Lean proves that increasing `J`
preserves introducedness, that `(S,J+1)` is not introduced at state `(S,J)`,
and that `(S,J+1)` is introduced after advancing to state `(S,J+1)` whenever
it is a valid actual-width label. It also records that Aoyagi's stronger
continuation bound `J+1 <= mu_(S+1)` implies this actual-width label result.

## Source role

This formalizes the source's active exceptional variables at state `(S,J)`:

```text
u_(s,k), 1 <= s <= S-1, 1 <= k <= n_(s+1),
u_(S,k), 1 <= k <= J.
```

The labels still use actual widths, not prefix minima.

## Proved

- Introduced labels are actual-width source labels.
- Earlier-layer labels are introduced.
- Current-layer labels are introduced exactly up to `J`.
- Introducedness is monotone in `J`.
- The new pivot label `(S,J+1)` is not introduced before the pivot advance and
  is introduced afterward under the actual-width bound.
- The source continuation bound gives the same introduced-label conclusion.

## Not proved

- No full finite vector invariant.
- No assertion that the actual-width bound is enough for the algorithm to
  continue at `(S,J+1)`; that requires the stronger prefix-minimum continuation
  bound.
- No assertion that all introduced labels have assigned vector/exponent data.
- No Case 1/2 transition theorem.
- No pivot-chart coverage, termination proof, normal-crossing certificate, or
  RLCT extraction.

## Status

- Sorry-free.
- Commit SHA pin pending until the Lean-theorem commit exists.

## Verification

- `lake build DLNFibre.DLN.Aoyagi.BlowupArithmetic`
