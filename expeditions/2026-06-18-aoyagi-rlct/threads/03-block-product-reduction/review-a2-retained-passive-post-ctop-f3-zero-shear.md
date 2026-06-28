# Review: A2 retained-passive post-`Ctop` `F3` zero-tail shear

Reviewer: xhigh `Nietzsche the 2nd`.

Verdict: PASS.

## Checked

- The `F3` focus regrouping matches raw tuple order
  `(A1passive, F2, A3passive, C, Ctop, F3)`.
- The `M = 0` shear fixes all fields except `F3` and applies exactly
  `F3 |-> F3 + coord.F3 * Ctop`.
- The determinant-one proof is by conjugation through the `F3` focus to the
  existing `linearEquivUpperShear` determinant theorem.
- The zero-tail bridge uses the existing `Ctop` zero-tail and `F3` zero-tail
  target-staged theorems and proves only terminal component equality.
- Public names remain zero-tail/component scoped.  There is no new positive-tail
  bridge, full tuple equality, Frechet determinant equality, measure transport,
  normal-crossing, pole-order, or RLCT claim.
- The reproduction note marks positive-tail `dEarly_postC` as future
  implementation work and states the nonclaims explicitly.

## Reviewer Gates

- `git diff --check -- <two requested files>` passed.
- `cd lean && lake env lean DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesJacobian.lean`
  passed.

## Controller Gates

- Focused `scripts/lb DLNFibre.DLN.Aoyagi.RetainedPassiveCoordinatesJacobian`
  passed.
- Full `scripts/lb DLNFibre` passed with pre-existing warning noise.
- `scripts/sorries` reported zero forbidden Lean constructs.
- `git diff --check` passed.
- Direct axiom audit for the new public theorem names reported
  `[propext, Classical.choice, Quot.sound]`.
