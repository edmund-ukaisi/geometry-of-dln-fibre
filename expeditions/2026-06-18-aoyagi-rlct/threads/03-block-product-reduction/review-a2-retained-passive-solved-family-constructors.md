# Review - A2 retained-passive solved family constructors

Date: 2026-06-26.

Reviewer: xhigh read-only reviewer `Bohr the 3rd`.

## Scope

Audit the solved-family constructor rung in
`lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinates.lean`:

```text
ChartLocalSuffixState.retainedPassiveSolvedA1
ChartLocalSuffixState.retainedPassiveA1TailAfterFirst_solvedA1
ChartLocalSuffixState.retainedPassiveSolvedA1_zero_eq_tail_inv_mul
ChartLocalSuffixState.retainedPassiveSolvedA1_passive_det_isUnit
ChartLocalSuffixState.retainedPassiveSolvedA3
ChartLocalSuffixState.retainedPassiveA3WithoutLast_solvedA3
ChartLocalSuffixState.retainedPassiveSolvedA3_last_eq_target
ChartLocalSuffixState.retainedPassiveSolvedFixedBaseEdgeMatrix_readbacks_eq_targets
```

The review checked sign/order, tail invariance, determinant-unit transport,
use of the fixed-base readback package, and the nonclaim boundary.

## Verdict

PASS.

## Checks

The solved `A1` family uses the correct order:

```text
A1_0 = Tail^-1 * Ctop.
```

The theorem `retainedPassiveA1TailAfterFirst_solvedA1` proves that the passive
tail ignores the solved value at `p=0`, so the solved family satisfies the
endpoint equation consumed by the fixed-base package.

The solved `A3` family uses the retained-passive lower-left sign convention:

```text
A3_last = -(F3 - earlyTail) * CtopLast.
```

This matches the signed product-tail convention in the fixed-base package.
The theorem `retainedPassiveA3WithoutLast_solvedA3` proves that zeroing the
final block erases the seed/solved difference.

The passive determinant-unit hypothesis is transported only for `p != 0`; the
full `A1` unit family is still derived by the reused endpoint package from
`det(Ctop)` and the solved endpoint equation.

## Nonclaims

The reviewed Lean does not define a bundled coordinate domain and does not
prove a two-sided local inverse.  It proves no source coverage, source/image
equality, source-measure pushforward, density/Jacobian theorem, normal
crossings, pole order, or RLCT extraction.
