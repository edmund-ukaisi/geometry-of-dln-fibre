# Review - A2 source-dependent product family small-ball coordinate identities

Date: 2026-06-25.

Scope: determinant-small-ball wrapper for coordinate identities of the
source-dependent multi-edge p.13 product family.

## Checklist

- The only shrinking argument is determinant continuity for `Ctop(u)` near
  `u = 0`.
- The resulting radius is bounded by the caller's `Rmax`.
- The pointwise coordinate readout theorem is applied only after obtaining
  `IsUnit(det(Ctop(u)))`.
- The eventual source-filter conclusion is obtained from a pointwise-in-`x`
  statement, not from any hidden openness or coverage claim for the source
  stratum.
- The theorem stays multi-edge and does not cover the one-edge endpoint
  collapse.

## Verdict

Accepted at the stated coordinate-identity scope.  The Lean theorem chooses a
small radius using the existing determinant-neighborhood theorem, then applies
the pointwise source-dependent product-family readout at each `x` and `u`.
The source-filter conclusion is correctly obtained by `eventually_of_forall`,
so it does not smuggle in source-stratum openness or coverage.
