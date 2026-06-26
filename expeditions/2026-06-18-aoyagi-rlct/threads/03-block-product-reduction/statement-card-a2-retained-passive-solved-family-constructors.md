# Statement Card - A2 retained-passive solved family constructors

## Lean File

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinates.lean
```

## Lean Names

```text
DLNFibre.DLN.Aoyagi.ChartLocalSuffixState.retainedPassiveSolvedA1
DLNFibre.DLN.Aoyagi.ChartLocalSuffixState.retainedPassiveSolvedA1_zero_eq_tail_inv_mul
DLNFibre.DLN.Aoyagi.ChartLocalSuffixState.retainedPassiveSolvedA1_passive_det_isUnit
DLNFibre.DLN.Aoyagi.ChartLocalSuffixState.retainedPassiveSolvedA3
DLNFibre.DLN.Aoyagi.ChartLocalSuffixState.retainedPassiveA3WithoutLast_solvedA3
DLNFibre.DLN.Aoyagi.ChartLocalSuffixState.retainedPassiveSolvedA3_last_eq_target
DLNFibre.DLN.Aoyagi.ChartLocalSuffixState.retainedPassiveSolvedFixedBaseEdgeMatrix_readbacks_eq_targets
```

## Reproduction

```text
reproduction-a2-retained-passive-solved-family-constructors.md
```

## Claim

Lean now defines solved full retained-passive families from passive seed data.

For top-left blocks, `retainedPassiveSolvedA1 A1seed Ctop` keeps `A1seed_p`
for `p != 0` and sets

```text
A1_0 = Tail(A1seed)^-1 * Ctop.
```

Lean proves the passive tail is unchanged after solving `A1_0`, so the solved
family satisfies the endpoint equation consumed by the fixed-base package:

```text
A1sol_0 = Tail(A1sol)^-1 * Ctop.
```

For lower-left blocks, `retainedPassiveSolvedA3 A1 A3seed C F3` keeps
`A3seed_p` for `p != last` and sets

```text
A3_last = -(F3 - EarlyTail) * CtopLast.
```

Lean proves the final-zeroed family is unchanged by this solve, so the solved
family satisfies the endpoint equation consumed by the fixed-base package.

The wrapper theorem
`retainedPassiveSolvedFixedBaseEdgeMatrix_readbacks_eq_targets` applies these
solved families to the fixed-base edge constructor and proves the active
source-left readbacks plus all per-edge transformed-edge readbacks, without
taking `A1_0` or `A3_last` equations as hypotheses.

## Method

The `A1` proof uses reverse product induction to show that the passive tail
after the first edge ignores the solved value at `0`.  The determinant-unit
passive hypothesis is transported to the solved family away from `0`, and the
existing endpoint package derives the solved `A1_0` unit from `det(Ctop)`.

The `A3` proof defines the final block using the tail with final block zeroed.
The theorem `retainedPassiveA3WithoutLast_solvedA3` shows that zeroing the
final block erases the difference between the seed and solved `A3` family, so
the endpoint equation is exactly the prior one.

## Role

This is the first explicit constructor-side source-map layer for the
retained-passive p.13 chart.  It replaces the two endpoint equations in the
readback package by definitions from passive seed data.

## Nonclaims

No bundled retained-passive coordinate-domain structure is defined.  No
two-sided local inverse, source-rank coverage, source/image equality, measure
pushforward, density/Jacobian theorem, normal crossings, pole order, or RLCT
extraction is proved.

## Verification

Focused check:

```text
cd lean
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre.DLN.Aoyagi.RetainedPassiveCoordinates
```

This focused check passed on 2026-06-26.

Full check:

```text
cd lean
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre
```

also passed on 2026-06-26, with pre-existing warnings outside the touched
module.  `scripts/sorries` and `git diff --check` also passed.

Review:

```text
threads/03-block-product-reduction/review-a2-retained-passive-solved-family-constructors.md
```
