# Statement Card - A2 retained-passive coordinate-data source map

## Lean File

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinates.lean
```

## Lean Names

```text
DLNFibre.DLN.Aoyagi.ChartLocalSuffixState.RetainedPassiveCoordinateData
DLNFibre.DLN.Aoyagi.ChartLocalSuffixState.RetainedPassiveCoordinateData.solvedA1
DLNFibre.DLN.Aoyagi.ChartLocalSuffixState.RetainedPassiveCoordinateData.solvedA3
DLNFibre.DLN.Aoyagi.ChartLocalSuffixState.RetainedPassiveCoordinateData.edgeMatrix
DLNFibre.DLN.Aoyagi.ChartLocalSuffixState.RetainedPassiveCoordinateData.edgeMatrix_readbacks_eq_targets
```

## Reproduction

```text
reproduction-a2-retained-passive-coordinate-data-source-map.md
```

## Claim

Lean now bundles the retained-passive finite coordinate fields into
`RetainedPassiveCoordinateData`.  The fields are:

```text
A1seed, F2, A3seed, C, Ctop, F3.
```

The associated projections define the solved full families

```text
solvedA1 = retainedPassiveSolvedA1(A1seed,Ctop),
solvedA3 = retainedPassiveSolvedA3(solvedA1,A3seed,C,F3),
```

and the fixed-base edge family

```text
edgeMatrix = retainedPassiveFixedBaseEdgeMatrix(solvedA1,F2,solvedA3,C).
```

Under the finite side conditions

```text
F2_last = 0,
det(A1seed_p) is a unit for p != 0,
det(Ctop) is a unit,
```

Lean proves the source-left active readbacks and all per-edge transformed-edge
readbacks for `edgeMatrix`.

## Method

The proof is a packaging theorem.  It unfolds the bundled projections and
calls `retainedPassiveSolvedFixedBaseEdgeMatrix_readbacks_eq_targets`.

## Role

This is the first named finite retained-passive source-map object: coordinate
data plus the edge family it constructs.  It is the algebraic layer needed
before adding local inverse, coverage, or measure structure.

## Nonclaims

No open coordinate domain, topology, measure, or Jacobian is defined.  No
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
threads/03-block-product-reduction/review-a2-retained-passive-coordinate-data-source-map.md
```
