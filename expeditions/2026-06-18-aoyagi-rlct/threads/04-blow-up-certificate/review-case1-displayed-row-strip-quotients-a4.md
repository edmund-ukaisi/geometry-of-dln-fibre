# Review - A4 Case 1 displayed row-strip quotients

Status: reviewed; no blockers found.

## Reviewers

- Source scout: `Zeno the 3rd`.
- Pen-and-paper scout: `Maxwell the 3rd`.
- Lean/API scout: `Einstein the 3rd`.
- Implementation reviewer: `Feynman the 3rd`.

## Source And Math Review

The source scout checked Aoyagi PDF pp. 15-18.  Aoyagi defines

```text
b_i = (product over tilde_t = i-1) b_(i-1)
```

and in Case 1(2) displays `P` entries using `b'_i / b'_(J+1)` for
`i=J+2..M(S)`.  The paper calls `P` regular but does not spell out the
divisibility proof.  The first-jump equality gives trivial quotients on the
row strip, and ordinary recurrence tail divisibility gives quotient witnesses
below the strip.

The pen-and-paper scout reproduced the quotient witnesses with the selected
variable counted once.  With `B_i = u * c_i`, where `c_i` is the recurrence
using the factored old variable `u'_(s,k)`, every row has

```text
B_i = q_i * B_(J+1).
```

This uses only commutativity and right-oriented divisibility witnesses; it
does not cancel `u`.

## Lean/API Review

The Lean/API scout recommended the displayed top-left pivot only.  The
implemented theorems follow that boundary: the displayed pivot row has level
`J+1`, every residual row level is at least `J+1`, and the quotient witnesses
are supplied by existing monomial recurrence divisibility lemmas.

The implementation reviewer found no blocker.  In particular:

- the proof uses `case2ResidualRowLevel_ge`, not a false conversion of the
  Case 1 first-jump gap into a full Case 2 gap;
- the selected variable `u` remains on both sides of the quotient equation;
- the source-order wrapper remains finite algebra with supplied matrix, strip,
  and following-factor data.

One wording issue was fixed before commit: the statement card now says
"corresponding witnesses" after multiplying by `u`, not "the same witnesses".

## Caveats

- This is not a Case 1 transition theorem.
- The displayed chart, hidden old-label factorisation, source-coordinate
  transport, and post-data remain supplied.
- No arbitrary row-strip pivot theorem is proved.
- No chart construction, chart coverage, regularity, Jacobian formula,
  normal crossings, or RLCT extraction is proved.

## Verification

- From `lean/`: `lake env lean DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`:
  passed.
- From `lean/`: `lake build DLNFibre`: passed, with only pre-existing Core
  warnings.
- From `lean/`: `./scripts/sorries`: `0 sorry`, `0 #exit`,
  `0 native_decide`, `0 axiom`.
- From the worktree root: `git diff --check`: passed.
- Forbidden-token scan over `lean/DLNFibre/DLN/Aoyagi` and the expedition
  directory found no Lean forbidden-token use; hits are existing prose
  mentions in expedition notes and statement cards.
