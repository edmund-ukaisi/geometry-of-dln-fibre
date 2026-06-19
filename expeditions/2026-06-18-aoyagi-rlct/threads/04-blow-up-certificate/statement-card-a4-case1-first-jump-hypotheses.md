# Statement card - A4 Case 1 first-jump hypotheses

## Lean artifacts

File: `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean` @ `a853794`.

Names:

- `DLNFibre.DLN.Aoyagi.componentwiseLEOn`
- `DLNFibre.DLN.Aoyagi.Case1FirstJumpHypotheses`
- `DLNFibre.DLN.Aoyagi.Case1FirstJumpHypotheses.rowBound`
- `DLNFibre.DLN.Aoyagi.Case1FirstJumpHypotheses.lt_selectedLevel`
- `DLNFibre.DLN.Aoyagi.Case1FirstJumpHypotheses.selectedLevel_int`
- `DLNFibre.DLN.Aoyagi.Case1FirstJumpHypotheses.not_selected_in_gap`
- `DLNFibre.DLN.Aoyagi.Case1FirstJumpHypotheses.selected_componentwiseLE_self`
- `DLNFibre.DLN.Aoyagi.Case1FirstJumpHypotheses.stripRows_subset_residualBlockRows`
- `DLNFibre.DLN.Aoyagi.Case1FirstJumpHypotheses.stripEntries_subset_residualBlockEntries`

## Statement

Lean packages finite Case 1 first-jump data after a selected old exceptional
label has been chosen. The package records:

```text
1 <= J1,
J + J1 < mu_S,
the selected label (s,k) is already introduced at state (S,J),
level(s,k) = J + J1,
no introduced label has level J+1, ..., J+J1-1,
the selected vector is componentwise minimal on 1..L among labels at level J+J1.
```

The strict bound `J+J1 < mu_S` is the finite nonterminal boundary needed for
the source expression `b_(J+J1+1)`. It derives the weaker row-strip bound
`J+J1 <= mu_S` used by the row-containment lemmas.

## Source role

Aoyagi Case 1 assumes equality of the recurrence factors through
`b_(J+J1)`, a strict next jump at `b_(J+J1+1)`, a gap of empty intermediate
levels, and a selected level-`J+J1` label with minimal exponent vector. This
Lean package records the finite source-side hypotheses needed before proving a
Case 1 chart transition.

The `level` field is natural-valued because the source levels are recurrence
indices. The theorem `selectedLevel_int` only casts the selected-level equality
into the integer convention used by exponent certificates; it does not identify
`level` with a certificate `leastValue`.

## Proved

- The strict first-jump boundary implies `J+J1 <= mu_S`.
- The selected level is strictly above `J`.
- The selected level equality can be cast to an integer equality.
- The selected label is not in the forbidden intermediate gap.
- The selected label is componentwise minimal against itself as an immediate
  specialization of the minimality hypothesis.
- The strict boundary gives Case 1 row-strip row and entry containment through
  the existing containment lemmas.

## Not proved

- No construction or existence theorem for the selected label.
- No proof that a finite set of level-`J+J1` labels has a minimal element.
- No proof of the monomial recurrence equalities
  `b_(J+1)=...=b_(J+J1)` or inequality
  `b_(J+J1+1) != b_(J+J1)`.
- No theorem relating `level` to the integer `leastValue` field of
  `LabelExponentCertificate`.
- No proof that the selected label satisfies the flat-tail hypothesis or old
  least value needed by the Case 1 exponent update.
- No link between the anonymous `Unit` center generator and the concrete
  label `(s,k)`.
- No selected-entry chart construction, chart coverage, `Q/P` transition,
  regularity/Jacobian fact, exponent update, transition invariant,
  termination proof, normal-crossing certificate, or RLCT extraction.

## Status

- Sorry-free and xhigh source-scope reviewed at `a853794`.

## Verification

- `lake build DLNFibre.DLN.Aoyagi.BlowupArithmetic`
- `lake build DLNFibre`
- `./scripts/sorries`
- `git diff --check`
