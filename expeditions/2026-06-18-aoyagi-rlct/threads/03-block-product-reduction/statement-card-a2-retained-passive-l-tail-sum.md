# Statement Card - A2 retained-passive lower-left L tail sum

## Lean File

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinates.lean
```

## Lean Names

```text
DLNFibre.DLN.Aoyagi.ChartLocalSuffixState.retainedPassiveLowerLeftTailSum
DLNFibre.DLN.Aoyagi.ChartLocalSuffixState.retainedPassiveLowerLeftTailSum_self
DLNFibre.DLN.Aoyagi.ChartLocalSuffixState.retainedPassiveLowerLeftTailSum_castSucc
DLNFibre.DLN.Aoyagi.ChartLocalSuffixState.suffixState_lowerLeftBlock_L_retainedPassiveFixedBaseEdgeMatrix_eq_tailSum
DLNFibre.DLN.Aoyagi.ChartLocalSuffixState.suffixState_lowerLeftBlock_L_retainedPassiveFixedBaseEdgeMatrix_zero_eq_tailSum
DLNFibre.DLN.Aoyagi.ChartLocalSuffixState.suffixState_Ctop_retainedPassiveFixedBaseEdgeMatrix
DLNFibre.DLN.Aoyagi.ChartLocalSuffixState.retainedPassiveLowerLeftProductTailSum
DLNFibre.DLN.Aoyagi.ChartLocalSuffixState.retainedPassiveLowerLeftProductTailSum_self
DLNFibre.DLN.Aoyagi.ChartLocalSuffixState.retainedPassiveLowerLeftProductTailSum_castSucc
DLNFibre.DLN.Aoyagi.ChartLocalSuffixState.retainedPassiveLowerLeftTailSum_eq_productTailSum
DLNFibre.DLN.Aoyagi.ChartLocalSuffixState.suffixState_lowerLeftBlock_L_retainedPassiveFixedBaseEdgeMatrix_eq_productTailSum
DLNFibre.DLN.Aoyagi.ChartLocalSuffixState.suffixState_lowerLeftBlock_L_retainedPassiveFixedBaseEdgeMatrix_zero_eq_productTailSum
```

## Review

```text
review-a2-retained-passive-l-tail-sum.md
```

## Claim

For retained-passive fixed-base edges and deterministic suffix states
`S_i = suffixState E last i`, Lean proves the iterated lower-left formula

```text
lowerLeft(S_i.L) = Tail_i,
```

where `Tail_last=0` and

```text
Tail_p =
  -(S_{p+1}.D * A3_p * S_p.Ctop^-1) + Tail_{p+1}.
```

Lean also proves the same theorem with the suffix-state fields read back as
explicit ordered products:

```text
D_{p+1}    = residualFactorProduct C last p.succ,
Ctop_p     = residualFactorProduct A1 last p.castSucc.
```

## Method

The proof uses:

- the one-edge current-`Ctop` lower-left recurrence;
- terminal `L=I`, so the terminal lower-left block is zero;
- reverse induction over the same natural index used by `suffixState`;
- the existing `D=residualFactorProduct C` theorem;
- a new analogous `Ctop=residualFactorProduct A1` theorem over the constant
  vertex family `rho`.

## Role

This is the finite iterated `F3` formula needed before formalising the omitted
endpoint variable `A3_last`.  It deliberately remains in recursive tail-sum
form rather than a `Finset` display, because that matches the existing suffix
state definitions and avoids reindexing noise.

## Nonclaims

No `A3_last` solve, no retained-passive coordinate-domain theorem, no
source-rank coverage, no source/image equality, no source-measure pushforward,
no Jacobian/prior density theorem, no normal crossings, no pole order, and no
RLCT extraction are proved.

Lean's matrix inverse is total.  Analytic or chart-regularity uses must still
combine the displayed inverses with determinant-unit propagation for `Ctop`.

## Verification

Focused check:

```text
cd lean
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre.DLN.Aoyagi.RetainedPassiveCoordinates
```

Focused/full build, `scripts/sorries`, and `git diff --check` passed on
2026-06-26 before the checkpoint commit.  The full build still emits
pre-existing warnings outside the touched Aoyagi module.
