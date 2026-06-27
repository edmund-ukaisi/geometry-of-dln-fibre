# Statement card - A2 retained-passive formal block determinant

Status: Lean-proved; review pending.

## Claim

In the determinant-friendly block order

```text
(passive A1, passive A3, Ctop, edge-local (F,C), terminal F3),
```

the formal retained-passive block Jacobian has determinant

```text
det(Tail^{-1})^(|rho|)
* product_{p : Fin (M+1)} det(-A p)^(|kappa' p.castSucc|)
* det(-LastTop)^(|kappa' (Fin.last (M+1))|).
```

When `LastTop` is instantiated as the terminal residual-factor product, that
endpoint product satisfies

```text
LastTop = A (Fin.last M).
```

## Lean status

Proved in
`lean/DLNFibre/DLN/Aoyagi/RetainedPassiveFormalLinearDeterminant.lean`.

Main theorem:

```text
retainedPassiveTotalFormalBlockJacobian_det_eq
```

Supporting theorem:

```text
edgeLocalFCPairPiLinearMap_det_eq
```

New generic determinant API in
`lean/DLNFibre/DLN/Aoyagi/MatrixLinearDeterminant.lean`:

```text
linearMap_det_piMap_eq_prod
```

## Dependencies

- edge-local `(F,C)` determinant;
- rectangular left and right multiplication determinant lemmas;
- dependent finite product determinant helper;
- `ChartLocalSuffixState.residualFactorProduct_one_edge_eq_factor`.

## Caveats

This theorem is not yet the explicit determinant formula for the analytic
derivative of `topologyTupleEdgeRawOrder`.  It avoids the raw tuple product
order, so a later signed raw-order theorem must include the coordinate
permutation sign.  The absolute determinant formula is insensitive to that
sign.
