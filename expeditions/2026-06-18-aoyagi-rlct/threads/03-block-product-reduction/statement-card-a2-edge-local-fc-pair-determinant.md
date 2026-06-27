# Statement card - A2 edge-local `(F,C)` pair determinant

Status: reproduced, Lean-proved, and reviewed.

## Claim

For fixed matrices

```text
A : Matrix rho rho K
H : Matrix rho mu K
G : Matrix mu rho K,
```

over a `CommRing K`, with finite index types `rho`, `mu`, and `kappa`
and the `DecidableEq rho` assumption used by the square determinant, the
linear map on

```text
Matrix rho kappa K x Matrix mu kappa K
```

given by

```text
(F, C) |->
  (-(A + H*G) * F + H * C,
   -G * F + C)
```

has determinant

```text
det(-A)^(|kappa|)
```

in the displayed `(F,C)` input and `(Y12,Y22)` output order.

## Lean status

Proved in `lean/DLNFibre/DLN/Aoyagi/MatrixLinearDeterminant.lean`, as a
reusable finite matrix-linear determinant theorem for the edge-local pair map.

Final theorem:

```text
LinearMap.det (edgeLocalFCPairLinearMap A H G)
  = (-A).det ^ Fintype.card kappa.
```

Supporting names:

```text
edgeLocalFCPairLinearMap_apply
edgeLocalFCPairLowerShear_det_eq_one
edgeLocalFCPairUpperShear_det_eq_one
edgeLocalFCPairDiagonal_det_eq
```

Review:
`review-a2-edge-local-fc-pair-determinant.md`.

## Dependencies

- rectangular left-multiplication determinant theorem
  `linearMap_det_mulLeftLinearMap`;
- product-map determinant bookkeeping;
- determinant-one product shear bookkeeping.

## Caveats

This is not the full retained-passive raw-order determinant formula, not an
analytic `fderiv` theorem, not a density or pushforward theorem, not normal
crossings, not pole order, and not RLCT.  It is one edge-local determinant
factor in a fixed product-coordinate ordering.

## Verification

Focused `MatrixLinearDeterminant` and downstream
`ProductReductionStepJacobian` builds passed.  Full `DLNFibre` build passed
with the existing warning profile.  `scripts/sorries` reported zero forbidden
markers, `git diff --check` passed, and the axiom audit for the new determinant
theorem reported `[propext, Classical.choice, Quot.sound]`.
