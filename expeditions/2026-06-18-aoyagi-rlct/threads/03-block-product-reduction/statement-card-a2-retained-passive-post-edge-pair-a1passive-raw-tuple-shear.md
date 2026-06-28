# Statement card: A2 retained-passive post-edge-pair `A1passive` raw-tuple shear

## Claim

After the full raw-tuple target edge-pair shear, there is a determinant-one
raw-tuple linear equivalence that changes only `A1passive` and fixes
`(F2,A3passive,C,Ctop,F3)`.

The shear computes the successor `F2` family from the already-normalised
post-edge-pair `(F2,C)` pair by applying

```text
(retainedPassiveFormalRawF2CLinearEquivAt hz).symm.
```

It does not use `retainedPassiveTargetRecoveredSuccessorF2At z w` as its
definition, because that recurrence reads the raw `A1` field and is not the
triangular post-edge-pair object.

## Lean Surface

```text
retainedPassivePostEdgePairA1passiveShearRawTupleLinearEquivAt
retainedPassivePostEdgePairA1passiveShearRawTupleLinearEquivAt_apply
retainedPassivePostEdgePairA1passiveShearRawTupleLinearEquivAt_symm_apply
retainedPassivePostEdgePairA1passiveShearRawTupleLinearEquivAt_det_eq_one
retainedPassivePostEdgePairA1passiveShearRawTupleLinearEquivAt_abs_det_eq_one
```

Private implementation helpers may package the raw tuple as
`A1passive × rest` and the correction as a linear map `rest -> A1passive`.

The next target, not proved by this card, is the composed edge-pair-then-`A1`
wrapper and partial actual-derivative bridge.

## Hypotheses

Use the finite-index hypotheses of the target edge-pair layer, plus

```text
hz : z ∈ topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ')
```

for the formal `(F2,C)` inverse.

## Lean Status

Proved in `lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCoordinatesJacobian.lean`.
The generic inverse formula
`linearEquivUpperShear_symm_apply` was added to
`lean/DLNFibre/DLN/Aoyagi/MatrixLinearDeterminant.lean`.

Focused builds of
`DLNFibre.DLN.Aoyagi.MatrixLinearDeterminant` and
`DLNFibre.DLN.Aoyagi.RetainedPassiveCoordinatesJacobian` passed.

## Proof Plan

1. Define the rest tuple
   `(F2,A3passive,C,Ctop,F3)` and the linear correction `L(rest)`.
2. Package the equivalence as the product shear
   `(A1passive, rest) |-> (A1passive - L(rest), rest)`.
3. Prove determinant one from `linearEquivUpperShear_det_eq_one`; prove the
   absolute determinant wrapper by taking absolute values.

## Nonclaims

This is not the full target normaliser.  It does not prove the composed
edge-pair-then-`A1` actual-derivative bridge; does not prove formal agreement
for `A3passive`, `Ctop`, or `F3`; does not prove actual raw-order determinant
equality; and does not prove source-prior transport, inverse-density
pushforward, normal crossings, pole order, or RLCT.
