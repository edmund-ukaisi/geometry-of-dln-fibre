# Statement Card - A2 retained-passive Ctop determinant chart

## Lean File

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinates.lean
```

## Lean Names

```text
DLNFibre.DLN.Aoyagi.ChartLocalSuffixState.step_retainedPassiveFixedBaseEdgeMatrix_Ctop
DLNFibre.DLN.Aoyagi.ChartLocalSuffixState.suffixState_Ctop_retainedPassiveFixedBaseEdgeMatrix_castSucc
DLNFibre.DLN.Aoyagi.ChartLocalSuffixState.suffixState_Ctop_det_isUnit_retainedPassiveFixedBaseEdgeMatrix
```

## Claim

For retained-passive transformed blocks

```text
M_p = [ A1_p   -A1_p * F2_p
        A3_p    C_p - A3_p * F2_p ],
```

and fixed-base edge matrices

```text
E_p = [I, F2_{p+1}; 0, I] * M_p,
```

the deterministic suffix-state top block satisfies the one-edge recurrence

```text
Ctop_p = Ctop_{p+1} * A1_p
```

along the recursive `suffixState E last` chain.  Consequently, if every
`det(A1_p)` is a unit, then every recursively produced suffix-state `Ctop`
has unit determinant.

The hypotheses are:

```text
F2_last = 0,
IsUnit det(A1_p) for every edge p.
```

## Method

Lean first proves the local step formula from the already established
retained-passive transformed-edge cancellation.  The prior suffix-state
`B=-F2` tracking theorem supplies the hypothesis needed to identify the
transformed edge at each recursive step.  The determinant-unit statement is
then a reverse induction from the terminal state `Ctop=1`, using

```text
det(Ctop_{p+1} * A1_p) = det(Ctop_{p+1}) * det(A1_p).
```

## Role

This is the determinant-chart part of the retained-passive finite source-map
skeleton.  It records that the candidate fixed-base reconstruction keeps the
recursive accumulated top block inside the determinant-unit chart whenever the
full reconstructed family of `A1_p` blocks is already assumed or proved to
have unit determinants.

This is a prerequisite for later endpoint readback of the omitted active
variable

```text
A1_0 = Ctop_1^-1 * Ctop_0.
```

## Nonclaims

No endpoint recovery for `A1_0` or `A3_last`, no retained-passive
coordinate-domain theorem with active `Ctop_0` plus passive `A1_p` for
`p > 0`, no formula for `Ctop_0` as a chosen active coordinate, no source-rank
coverage, no source/image equality, no source-measure pushforward, no
Jacobian/prior density theorem, no normal crossings, no pole order, and no
RLCT extraction are proved here.

## Verification

Focused check:

```text
cd lean
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre.DLN.Aoyagi.RetainedPassiveCoordinates
```

passed on 2026-06-26.

Full aggregator check:

```text
cd lean
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre
```

also passed on 2026-06-26, with only pre-existing warnings in other modules and
`DLNFibre.lean`.

`git diff --check` and `scripts/sorries` also passed on 2026-06-26.

Xhigh read-only reviewer `Mill the 3rd` passed the slice in
`review-a2-retained-passive-ctop-det-chart.md`.
