# A2 retained-passive source-readback residual readout

## Boundary

This slice is finite algebra inside the already constructed retained-passive
and fixed-base p.13 coordinate systems.  It does not construct a source chart,
prove source/image equality, prove a measure pushforward or Jacobian formula,
compare with the original DLN loss, prove normal crossings, compute pole
order, or extract an RLCT.

## Pen-and-paper reproduction

Fix a retained-passive-shaped fixed-base edge family

```text
E_p : rho + kappa_{p+1} -> rho + kappa_p
```

for `p = 0, ..., M`.  The fixed-base residual coordinate map in
`RegularSuspensionCoordinates.lean` is defined by running the deterministic
suffix recursion from the terminal vertex to the source vertex:

```text
S_0 := suffixState E (last M+1) 0,
residualCoordinateMap(E) = entries(S_0.D).
```

The existing fixed-base readout theorem states this as

```text
residualCoordinateMap(E)
  = entries(residualProduct E (last M+1) 0).
```

The retained-passive source-readback data are defined from the same suffix
recursion.  Its residual block field is

```text
(sourceReadback E).C_p
  = schurResidualBlock(transformedEdge E p S_{p+1}).
```

The deterministic suffix theorem says

```text
S_0.D = residualProduct E (last M+1) 0.
```

The retained-passive readback theorem says the same `D` block is also the
ordered factor product of the readback residual blocks:

```text
S_0.D
  = residualFactorProduct (sourceReadback E).C (last M+1) 0.
```

Therefore

```text
residualCoordinateMap(E)
  = entries(residualFactorProduct (sourceReadback E).C (last M+1) 0).
```

The proof uses no determinant-chart hypothesis.  It is an identity about the
suffix recursion and the definitions of `sourceReadback` and the fixed-base
residual coordinate map.

## Kill conditions

- If the fixed-base residual coordinate map used a different suffix endpoint
  than `sourceReadback`, the theorem would be false or need reindexing.
- If `sourceReadback.C` were not defined as the Schur residual block of the
  same transformed edge used by `residualProduct`, the factor-product rewrite
  would not apply.
- If the theorem were used as a selected-entry readout without an entrywise
  identification of the resulting residual-factor product with the
  selected-entry chart coordinates, it would overclaim.
