# Statement Card - A2 retained-passive `A3_last` prefix target

## Lean File

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinates.lean
```

## Lean Names

```text
DLNFibre.DLN.Aoyagi.ChartLocalSuffixState.retainedPassiveA3WithoutLast
DLNFibre.DLN.Aoyagi.ChartLocalSuffixState.retainedPassiveA3WithoutLast_last
DLNFibre.DLN.Aoyagi.ChartLocalSuffixState.retainedPassiveA3WithoutLast_eq_of_ne
DLNFibre.DLN.Aoyagi.ChartLocalSuffixState.retainedPassiveLowerLeftProductTailSum_withoutLast_last
DLNFibre.DLN.Aoyagi.ChartLocalSuffixState.retainedPassiveLowerLeftProductTailSum_eq_withoutLast_add_last
DLNFibre.DLN.Aoyagi.ChartLocalSuffixState.retainedPassiveLowerLeftProductTailSum_zero_eq_target_of_A3_last_eq
```

## Reproduction

```text
reproduction-a2-retained-passive-a3-last-prefix-target.md
```

## Claim

Let `A3early` be the `A3` family with the final edge replaced by zero, and let

```text
EarlyTail = Tail_0(A3early).
```

Lean proves:

```text
Tail_0(A3) = EarlyTail + Tail_last(A3).
```

If `det(Ctop_last)` is a unit and

```text
A3_last = -(F3 - EarlyTail) * Ctop_last,
```

then

```text
Tail_0(A3) = F3.
```

## Method

The proof uses reverse induction on the existing recursive tail:

- at the final edge, the zeroed `A3early_last` makes the final tail zero;
- for every earlier edge, `A3early_p=A3_p`;
- therefore the full tail splits into the signed earlier tail plus the final
  tail;
- the previous endpoint-cancellation theorem supplies
  `Tail_last(A3)=F3-EarlyTail`;
- additive cancellation gives `EarlyTail+(F3-EarlyTail)=F3`.

## Role

This is the finite algebraic bridge from the local final-edge solve to the
active source coordinate `F3`.  It is the next piece needed before packaging a
retained-passive coordinate-domain source map.

## Nonclaims

No retained-passive coordinate-domain theorem is proved.  No active `Ctop_0`
or `A1_0` reconstruction, determinant-unit neighborhood theorem, source-rank
coverage, source/image equality, measure pushforward, density/Jacobian theorem,
normal crossings, pole order, or RLCT extraction is proved.

## Verification

Focused check:

```text
cd lean
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre.DLN.Aoyagi.RetainedPassiveCoordinates
```

This focused check passed on 2026-06-26 before review.
