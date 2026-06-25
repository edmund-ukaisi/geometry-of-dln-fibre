# Statement Card - A2 residual-factor product two-edge unfold

## Claim

For an explicit residual-factor family over two edges, the endpoint residual
factor product is the right factor followed by the left factor:

```text
residualFactorProduct C (Fin.last 2) 0 = C_1 * C_0.
```

The Lean statement casts the two factors to the canonical middle endpoint
`(1 : Fin 3)` because the adjacent `Fin 2` endpoint expressions are not
definitionally identical.

## Lean Name

```text
ChartLocalSuffixState.residualFactorProduct_fin_two_eq_mul
```

## Boundaries

Generic finite product API only.  No Case 2 source production, no concrete
global `Cfac`, no residual-index equivalence, no selected-entry matrix
identity, no source/image equality, no normal crossings, no pole order, and no
RLCT.
