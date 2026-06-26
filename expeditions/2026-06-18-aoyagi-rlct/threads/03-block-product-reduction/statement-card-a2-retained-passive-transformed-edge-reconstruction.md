# Statement Card - A2 retained-passive transformed-edge reconstruction

## Lean File

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinates.lean
```

## Lean Names

```text
DLNFibre.DLN.Aoyagi.ChartLocalSuffixState.retainedPassiveTransformedEdge
DLNFibre.DLN.Aoyagi.ChartLocalSuffixState.retainedPassiveFixedBaseEdgeMatrix
DLNFibre.DLN.Aoyagi.ChartLocalSuffixState.transformedEdge_retainedPassiveFixedBaseEdgeMatrix_of_B_eq
DLNFibre.DLN.Aoyagi.ChartLocalSuffixState.step_retainedPassiveFixedBaseEdgeMatrix_B
DLNFibre.DLN.Aoyagi.ChartLocalSuffixState.suffixState_B_retainedPassiveFixedBaseEdgeMatrix
DLNFibre.DLN.Aoyagi.ChartLocalSuffixState.retainedPassiveFixedBaseEdgeMatrices_transformedEdge_eq
```

## Claim

For any finite chain of edge count `N`, retained-passive chart blocks

```text
M_p = [ A1_p   -A1_p * F2_p
        A3_p    C_p - A3_p * F2_p ],
```

and fixed-base edge matrices

```text
E_p = [I, F2_{p+1}; 0, I] * M_p,
```

the deterministic suffix-state recursion sees exactly the prescribed
transformed edge:

```text
transformedEdge E p (suffixState E last p.succ) = M_p.
```

The hypotheses are:

```text
F2_last = 0,
IsUnit det(A1_p) for every edge p.
```

## Method

Lean first proves the local cancellation

```text
[I,-F2_{p+1};0,I] * ([I,F2_{p+1};0,I] * M_p) = M_p,
```

using the existing upper-unitriangular cancellation lemma.  The suffix-state
`B` field is then tracked by reverse induction along `suffixState`: the
terminal state has `B=0=-F2_last`, and one retained-passive step updates
`B=-F2_{p+1}` to `B=-F2_p` by the formula
`B := A1_p^{-1} * (-A1_p * F2_p)`.

## Role

This is the first Lean algebraic skeleton for the retained-passive p.13 source
map.  It verifies that the candidate fixed-base reconstruction has the
intended transformed one-step chart blocks, so later local inverse/readback
statements can target these blocks.

## Nonclaims

No active endpoint reconstruction for `A1_0` or `A3_last`, no source-rank
coverage, no source/image equality, no source-measure pushforward, no
Jacobian/prior density theorem, no normal crossings, no pole order, and no
RLCT extraction are proved here.

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

Both passed on 2026-06-26.  The full build reported only pre-existing warnings
in other modules and long-line warnings in `DLNFibre.lean`.

Xhigh read-only reviewer `Hooke the 3rd` audited the statement against the
reproduction note and passed: the theorem proves exactly the finite
transformed-edge reconstruction claim, with honest hypotheses and no analytic
overclaim.
