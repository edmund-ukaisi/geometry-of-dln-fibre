# Review - A4 Case 2 identity-following actual-width boundary

Reviewed objects:

- `sourceChart_actualWidth_terminalOriginalRowsIdentityFollowingBoundary`
- `reproduction-case2-identity-following-actual-width-a4.md`
- `statement-card-a4-case2-identity-following-actual-width.md`

Verdict: no blocking source/math or Lean API issue found.

The theorem is exactly the `F = 1` specialization of the arbitrary supplied
following boundary.  It calls
`sourceChart_actualWidth_terminalOriginalRowsSuppliedSuffixBoundary` with
`(1 : Matrix tau tau R)` and then uses unit simplification to remove the
rightmost following factor.

The statement keeps the load-bearing actual-width hypothesis
`n(S+1)=J+1` and does not assert terminal-last suffix emptiness, source
production of `C'^(S+1)`, or the row-exhausted branch.

The docs match the Lean boundary: this is the algebraic identity-following
shape after a separate result has identified a following factor with the
identity.  It does not itself prove that a source suffix is empty; that remains
the separate `sourceSuffixProduct_terminalLast_eq_cast_one` theorem.

Nonblocking documentation suggestions were applied:

- the statement card no longer lists "a supplied following matrix has already
  been identified with the identity" as a Lean assumption;
- the statement card records the finite following-column typeclass needed for
  the arbitrary-following boundary; decidable equality is local to the proof.
