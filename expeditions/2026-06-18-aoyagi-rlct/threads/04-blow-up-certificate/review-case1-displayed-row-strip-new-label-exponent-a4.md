# Review - A4 Case 1 displayed row-strip new-label exponent

Status: reviewed; no blockers found.

## Reviewers

- Source scout: `Confucius the 3rd`.
- Pen-and-paper scout: `Dewey the 3rd`.
- Lean/API scout: `Parfit the 3rd`.
- Implementation reviewer: `Lorentz the 3rd`.

## Source And Math Review

The source scout checked Aoyagi PDF pp. 15-19. In Case 1(2), after factoring
the old selected variable as

```text
u_(s,k) = u_(S,J+1) u'_(s,k),
```

Aoyagi adds a new label `(S,J+1)` with the old selected prefix before `S`,
constant tail `J` from `S` through `L`, least value `J`, and numerator
increment

```text
M'_(S,J+1) = M_(s,k) + J1 * (M^(S+1) - J).
```

The pen-and-paper scout reproduced the terminal-exponent calculation. If the
old selected vector is flat at `J+J1` from `S-1` through `L`, then lowering the
tail to `J` changes only the `j=S` terminal-exponent summand. The increment is

```text
(J+J1-J) * (n_(S+1)-J) = J1 * (n_(S+1)-J).
```

The least value is `J`, witnessed at component `S`, and old components before
`S` stay at least `J` because the old least value is `J+J1`.

## Lean/API Review

The Lean/API scout recommended a separate new-label theorem, not reuse of the
same-domain selected-label update as a transition theorem. The implemented
boundary follows this:

- `displayedRowStrip_newLabelExponentCertificate` reuses only the
  terminal-exponent and least-value fields from the old selected lower-tail
  certificate.
- The `introduced` field is replaced by the post-state actual-width proof for
  `(S,J+1)`.
- `Case1DisplayedRowStripExponentPostData` assumes old introduced labels are
  preserved and assigns only the new label.
- The concrete update-data theorem preserves old labels because `(S,J+1)` is
  not introduced at state `(S,J)`.

The implementation reviewer found no blocker. The assumptions are explicit:
`2 <= S`, `S <= L`, `J+1 <= n(S+1)`, the level-to-least-value bridge, and
`FlatTailFromPred`. Names and comments do not claim chart production,
recurrence production, Jacobian accounting, normal crossings, or a full
transition.

One mild naming note is inherited from existing infrastructure:
`introducedLabel_case2_new_after` is a generic current-layer successor-label
fact despite its Case 2 name.

## Caveats

- This is not a Case 1 transition theorem.
- The chart production of the supplied post-data remains external.
- The `S=1` endpoint remains outside the theorem.
- Hidden old-label validity, recurrence bookkeeping, chart regularity,
  Jacobian formula, normal crossings, and RLCT extraction remain deferred.

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
