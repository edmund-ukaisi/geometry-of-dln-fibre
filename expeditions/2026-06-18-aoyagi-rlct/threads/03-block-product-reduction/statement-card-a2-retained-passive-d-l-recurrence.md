# Statement Card - A2 retained-passive D and L recurrences

## Lean File

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinates.lean
```

## Lean Names

```text
DLNFibre.DLN.Aoyagi.ChartLocalSuffixState.schurResidualBlock_retainedPassiveTransformedEdge
DLNFibre.DLN.Aoyagi.ChartLocalSuffixState.step_retainedPassiveFixedBaseEdgeMatrix_D
DLNFibre.DLN.Aoyagi.ChartLocalSuffixState.suffixState_D_retainedPassiveFixedBaseEdgeMatrix_castSucc
DLNFibre.DLN.Aoyagi.ChartLocalSuffixState.suffixState_D_retainedPassiveFixedBaseEdgeMatrix
DLNFibre.DLN.Aoyagi.ChartLocalSuffixState.step_retainedPassiveFixedBaseEdgeMatrix_L
DLNFibre.DLN.Aoyagi.ChartLocalSuffixState.step_retainedPassiveFixedBaseEdgeMatrix_lowerLeftBlock_L
```

## Claim

For the retained-passive transformed block

```text
M_p =
  [ A1_p       -A1_p * F2_p
    A3_p        C_p - A3_p * F2_p ],
```

the Schur residual is the prescribed residual block:

```text
schurResidualBlock(M_p) = C_p.
```

Consequently the deterministic suffix-state residual field satisfies

```text
D_p = D_{p+1} * C_p,
D_i = residualFactorProduct C last i.
```

The same one-step calculation updates the left multiplier by

```text
L_p =
  [I,0; -(D_{p+1} * A3_p * (Ctop_{p+1} * A1_p)^-1), I] * L_{p+1}.
```

If `L_{p+1} = [I,0;F3_{p+1},I]`, Lean also proves the lower-left block update

```text
lowerLeft(L_p) =
  -(D_{p+1} * A3_p * (Ctop_{p+1} * A1_p)^-1) + F3_{p+1}.
```

Using the previously proved `Ctop_p = Ctop_{p+1} * A1_p`, this is the finite
one-step algebra behind the paper-note recurrence

```text
F3_p = F3_{p+1} - D_{p+1} * A3_p * Ctop_p^-1.
```

## Method

The Schur residual proof expands the block definition and cancels
`A1_p^-1 * A1_p`.  The `D` recurrence then follows from the definition of
`step`, and the suffix product theorem uses the existing generic
`suffixState_D_eq_residualProduct` plus
`residualProduct_eq_residualFactorProduct_of_residualBlock_eq`.

The `L` statement is one-step only.  It unfolds `step` after the
retained-passive transformed-edge cancellation and then uses the existing
lower-unitriangular multiplication lemma.

## Role

This is the finite residual-field and one-step lower-unitriangular bookkeeping
needed before solving for the omitted right-endpoint variable `A3_last`.

## Nonclaims

This does not yet prove the iterated finite-sum formula for `F3_0`, does not
solve for `A3_last`, and does not construct the retained-passive coordinate
domain.  It assumes a full determinant-unit `A1` family, including `A1_0`.

No source-rank coverage, source/image equality, source-measure pushforward,
Jacobian/prior density theorem, normal crossings, pole order, or RLCT
extraction is proved here.

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
module and long-line warnings in `DLNFibre.lean`.  `scripts/sorries` and
`git diff --check` also passed.
