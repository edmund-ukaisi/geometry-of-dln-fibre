# Statement Card - A2 retained-passive A1 readback

## Lean File

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinates.lean
```

## Lean Name

```text
DLNFibre.DLN.Aoyagi.ChartLocalSuffixState.retainedPassiveFixedBaseEdgeMatrix_A1_eq_suffixState_Ctop_inv_mul_Ctop
```

## Claim

For retained-passive fixed-base edges built from a full determinant-unit family
`A1`, adjacent deterministic suffix-state top blocks recover each supplied
factor:

```text
A1_p = Ctop_{p+1}^-1 * Ctop_p.
```

Equivalently, in Lean notation,

```text
A1 p =
  ((suffixState E last p.succ).Ctop)^-1 *
    (suffixState E last p.castSucc).Ctop.
```

The hypotheses are the same as the prior retained-passive suffix-state rung:

```text
F2_last = 0,
IsUnit det(A1_p) for every edge p.
```

## Method

The proof uses the already-proved Ctop recurrence

```text
Ctop_p = Ctop_{p+1} * A1_p
```

and the determinant-unit propagation theorem for `Ctop_{p+1}`.  Left
multiplication by `Ctop_{p+1}^-1` then gives the readback formula.  The order is
essential: the theorem proves `Ctop_{p+1}^-1 * Ctop_p`, not
`Ctop_p * Ctop_{p+1}^-1`.

## Role

This is a finite constructor-side readback lemma for the retained-passive
source-map skeleton.  At `p=0`, it is the algebraic identity underlying the
future active endpoint formula

```text
A1_0 = Ctop_1^-1 * Ctop_0.
```

## Nonclaims

This is not yet the retained-passive coordinate-domain theorem.  In this
statement, `A1_0` is still part of the input family `A1`, and the hypothesis
`hA1` assumes `det(A1_0)` is a unit.  No theorem yet constructs `A1_0` from an
active `Ctop_0 = I + X` and passive `A1_p` for `p > 0`.

No `A3_last` recovery, no source-rank coverage, no source/image equality, no
source-measure pushforward, no Jacobian/prior density theorem, no normal
crossings, no pole order, and no RLCT extraction are proved here.

## Verification

Focused check:

```text
cd lean
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre.DLN.Aoyagi.RetainedPassiveCoordinates
```

Full aggregator check:

```text
cd lean
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre
```

Both passed on 2026-06-26, with only pre-existing warnings outside the touched
module and long-line warnings in `DLNFibre.lean`.  `git diff --check` and
`scripts/sorries` also passed.
