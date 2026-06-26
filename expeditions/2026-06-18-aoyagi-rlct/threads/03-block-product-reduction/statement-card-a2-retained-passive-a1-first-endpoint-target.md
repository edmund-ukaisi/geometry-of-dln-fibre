# Statement Card - A2 retained-passive `A1_0` endpoint target

## Lean File

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinates.lean
```

## Lean Names

```text
DLNFibre.DLN.Aoyagi.ChartLocalSuffixState.retainedPassiveA1TailAfterFirst
DLNFibre.DLN.Aoyagi.ChartLocalSuffixState.retainedPassiveA1TailAfterFirst_mul_first
DLNFibre.DLN.Aoyagi.ChartLocalSuffixState.retainedPassiveA1TailAfterFirst_det_isUnit_of_passive
DLNFibre.DLN.Aoyagi.ChartLocalSuffixState.retainedPassiveCtopProduct_zero_eq_target_of_A1_zero_eq
DLNFibre.DLN.Aoyagi.ChartLocalSuffixState.retainedPassiveA1_zero_det_isUnit_of_A1_zero_eq_tail_inv_mul
DLNFibre.DLN.Aoyagi.ChartLocalSuffixState.retainedPassiveA1_det_isUnit_of_A1_zero_eq_tail_inv_mul
DLNFibre.DLN.Aoyagi.ChartLocalSuffixState.suffixState_Ctop_retainedPassiveFixedBaseEdgeMatrix_zero_eq_target_of_A1_zero_eq
```

## Reproduction

```text
reproduction-a2-retained-passive-a1-first-endpoint-target.md
```

## Claim

For a nonempty retained-passive edge family, define

```text
Tail = A1_last * ... * A1_1.
```

Lean represents this as `retainedPassiveA1TailAfterFirst A1` and proves

```text
residualFactorProduct A1 last 0 = Tail * A1_0.
```

If `det(Tail)` is a unit and

```text
A1_0 = Tail^-1 * Ctop,
```

then the full top-left product is the active endpoint:

```text
residualFactorProduct A1 last 0 = Ctop.
```

If `det(Ctop)` is also a unit, then the solved `A1_0` is determinant-unit.  If
all passive `A1_p` for `p != 0` are determinant-unit, Lean first proves the
passive tail is determinant-unit, then packages the full family
determinant-unit hypothesis and proves for retained-passive fixed-base edges

```text
(suffixState E last 0).Ctop = Ctop.
```

## Method

The proof is a single first-edge unfold of `residualFactorProduct`, followed by
matrix inverse cancellation:

```text
Tail * (Tail^-1 * Ctop) = (Tail * Tail^-1) * Ctop = Ctop.
```

The passive-tail determinant-unit statement is a reverse induction over the
tail product.  The solved-first-block determinant-unit statement then uses
multiplicativity of determinant and Mathlib's determinant-unit theorem for
`Tail^-1`.

## Role

This is the top-left endpoint half of the retained-passive coordinate-domain
inverse.  Together with the existing `A3_last` prefix target, it supplies the
two omitted endpoint variables needed before packaging a fixed-base
retained-passive source map/readback theorem.

## Nonclaims

No full retained-passive coordinate-domain theorem is proved.  No `F2`
readback packaging, no combined `A3_last`/`F3` source-map theorem, no
source-rank coverage, no source/image equality, no measure pushforward, no
density/Jacobian theorem, no normal crossings, no pole order, and no RLCT
extraction is proved.

## Verification

Focused check:

```text
cd lean
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre.DLN.Aoyagi.RetainedPassiveCoordinates
```

This focused check passed on 2026-06-26 before review.
