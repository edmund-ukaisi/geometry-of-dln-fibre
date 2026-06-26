# Statement Card - A2 retained-passive lower-left L recursion

## Lean File

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinates.lean
```

## Lean Names

```text
DLNFibre.DLN.Aoyagi.ChartLocalSuffixState.suffixState_lowerLeftBlock_L_retainedPassiveFixedBaseEdgeMatrix_castSucc
DLNFibre.DLN.Aoyagi.ChartLocalSuffixState.suffixState_lowerLeftBlock_L_retainedPassiveFixedBaseEdgeMatrix_castSucc_currentCtop
```

## Review

```text
review-a2-retained-passive-l-lowerleft-recursion.md
```

## Claim

For retained-passive fixed-base edges and deterministic suffix states
`S_p = suffixState E last p`, the lower-left block of the left multiplier
satisfies the one-edge recurrence

```text
lowerLeft(S_p.L)
  = -(S_{p+1}.D * A3_p * (S_{p+1}.Ctop * A1_p)^-1)
      + lowerLeft(S_{p+1}.L).
```

Using the already-proved `S_p.Ctop = S_{p+1}.Ctop * A1_p`, Lean also proves the
source-facing form

```text
lowerLeft(S_p.L)
  = -(S_{p+1}.D * A3_p * S_p.Ctop^-1)
      + lowerLeft(S_{p+1}.L).
```

## Method

The proof uses:

- the retained-passive transformed-edge cancellation and `B=-F2` tracking;
- the one-step `L` formula from the previous D/L recurrence rung;
- the generic theorem `suffixState_L_eq_lowerUnitriangular`, which gives
  `S_{p+1}.L = [I,0;F3next,I]`;
- lower-unitriangular multiplication;
- the retained-passive Ctop recurrence for the current-`Ctop` rewrite.

## Role

This is the recursive lower-left `L` bookkeeping needed before formalising the
iterated `F3_0` sum and solving for the omitted endpoint variable `A3_last`.

## Nonclaims

No iterated finite-sum formula for `F3_0`, no `A3_last` solve, no
retained-passive coordinate-domain theorem, no source-rank coverage, no
source/image equality, no source-measure pushforward, no Jacobian/prior density
theorem, no normal crossings, no pole order, and no RLCT extraction are proved.

Lean's matrix inverse is total.  Analytic or chart-regularity uses of the
displayed `Ctop_p^-1` must still cite the existing determinant-unit theorem for
suffix-state `Ctop`; this recurrence alone is finite algebra.

## Verification

Focused check:

```text
cd lean
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre.DLN.Aoyagi.RetainedPassiveCoordinates
```

Full target:

```text
cd lean
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre
```

Hygiene:

```text
cd lean
scripts/sorries
git diff --check
```

All passed on 2026-06-26 before the checkpoint commit.  The full build still
emits pre-existing warnings outside the touched Aoyagi module.
