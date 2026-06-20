# Review - A4 Case 1(1) Selected-Old Erased-Base Source Model

Reviewers: xhigh Lean/API reviewer `Tesla the 3rd`; xhigh source/math
reviewer `Ohm the 3rd`.

Status: passed after creating this review artifact.

## Findings

No Lean/API or source/math soundness findings.

Both reviewers initially found one low documentation issue: the statement card
and theorem ledger pointed to this review file before it existed. This file
resolves that pointer.

## Lean/API Verdict

The erased base is genuinely the introduced-label recurrence product with the
selected old label removed:

```text
(introducedLabelFinset L n S J).erase (Sigma.mk s0 k0)
```

The direction of the erased-base equality is correct:

```text
post.erasedStep s0 k0 = pre.erasedStep s0 k0.
```

It follows from non-selected level and variable agreement, with `pre` as the
reference assignment and `post` as the changed assignment. This is exactly the
direction needed to prove:

```text
post.step = mulStepAt (pre.erasedStep s0 k0) u J.
```

The constructor
`Case1SelectedOldLoweredRecurrenceBoundary.of_levelMoveData` specializes the
existing lowered boundary to `baseStep = pre.erasedStep s0 k0` and does not
claim chart construction or coverage.

## Source/Math Verdict

The pen-and-paper derivation matches Aoyagi PDF pp. 15-16. Case 1 fixes an old
exceptional variable `u_(s,k)` with `tilde_t = J+J1`. In Case 1(1), the row
strip is divided by that same old variable, and the selected old label's level
is lowered to `J`. No `(S,J+1)` label or displayed Case 1(2) pivot is
introduced.

The model correctly treats the base recurrence as the finite product over all
introduced labels except the selected old label. The selected variable is then
reinserted at level `J+J1` for the pre-state and at level `J` for the
post-state.

## Residual Risks

- The moved-level recurrence data are still supplied; Lean does not construct
  them from raw chart coordinates.
- The selected source label `(s0,k0)` is not inferred from the `Unit` finite
  center token.
- No chart coverage, regularity from coordinates, Jacobian accounting, normal
  crossings, RLCT extraction, or full transition invariant is proved.

## Verification

- `lake env lean DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`
- `lake build DLNFibre`
- `lean/scripts/sorries`
- forbidden-token scan over `lean/DLNFibre/DLN/Aoyagi`
- `git diff --check`
