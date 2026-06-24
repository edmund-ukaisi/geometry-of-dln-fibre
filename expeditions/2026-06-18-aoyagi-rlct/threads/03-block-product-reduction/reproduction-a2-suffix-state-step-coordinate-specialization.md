# Reproduction - A2 suffix-state step coordinate specialization

Status: pen-and-paper reproduction before Lean specialization.

## Source Anchor

The previous suffix-state adapter proved the p. 13 coordinate identities for
an arbitrary chart-local suffix state

```text
S : ChartLocalSuffixState rho kappa K j p.succ
```

provided `S.BlockDiagonal P hpj`, a lower-unitriangular witness for `S.L`, and
the determinant chart for `transformedEdge E p S`.

This slice specializes that arbitrary state to the actual recursive state

```text
S = suffixState E j p.succ hpj.
```

It is still finite block algebra.  It does not add chart coverage, analytic
coordinate status, ideal transport, normal crossings, pole order, or RLCT.

## Recursive State Inputs

Let

```text
S = suffixState E j p.succ hpj
M = transformedEdge E p S.
```

The one-step p. 13 wrapper needs three inputs:

```text
S.BlockDiagonal P hpj
S.L = [I 0; F3prev I]
identityCornerDetChart M.
```

The first and third are kept as hypotheses in the specialization.  This keeps
the theorem local to one recursive step: global recursion hypotheses such as
`hself`, proof-object irrelevance for `P`, and the full chart family are only
needed by callers that derive `S.BlockDiagonal P hpj`.

The second input is supplied by the already-proved recursive-state fact

```text
suffixState_L_eq_lowerUnitriangular E hpj :
  exists F3prev, S.L = [I 0; F3prev I].
```

Thus the new specialization is existential in `F3prev`.

## Product Matrix

The matrix used in the p. 13 product wrapper is the suffix product

```text
T = P p.castSucc j ((Fin.castSucc_le_succ p).trans hpj).
```

It is not the raw edge `E p`, and it is not the transformed edge `M`.  The
transformed edge supplies the raw coordinate corners `A1`, `A2`, `A3`, and
`A4`; the suffix product is the matrix being triangularly changed.

The recursion law

```text
P p.castSucc j = P p.succ j * E p
```

is still required because the generic adapter uses it to turn
`S.BlockDiagonal P hpj` into the prior product hypothesis.

## Resulting Coordinates

For the chosen witness `F3prev`, define

```text
x = stepRawCoordinates E p S F3prev
y = x.toChart.
```

The generic adapter then gives

```text
[I 0; y.F3 I] T [I y.F2; 0 I] = [y.Ctop 0; 0 y.D*y.C].
```

Subtracting the rank-model block gives the signed p. 13 block

```text
[I 0; y.F3 I] (T - [I 0; 0 0]) [I y.F2; 0 I]
  = [y.Ctop - I, -y.F2; -y.F3, y.D*y.C - y.F3*y.F2].
```

The lower-right correction is `F3*F2`.  No inverse of `S.D` or `y.D` is used.

## Lean Plan

Add two wrappers in `ProductReduction.lean`, inside
`ChartLocalSuffixState` after the recursive block-diagonal invariant:

```text
suffixState_stepRawCoordinates_triangularBlockProduct
suffixState_stepRawCoordinates_productDifference
```

Both wrappers:

- set `S = suffixState E j p.succ hpj`;
- transport the supplied `hS` and `hM` across that local abbreviation;
- choose `F3prev` from `suffixState_L_eq_lowerUnitriangular`;
- apply the corresponding generic `stepRawCoordinates_*` theorem.

## Nonclaims

This does not prove `S.BlockDiagonal P hpj`; callers can use
`suffixState_blockDiagonal` for that.  It does not prove chart coverage,
exact-rank/source-rank openness, analytic coordinate-chart construction,
regular-suspension construction, ideal transport, normal crossings, pole
order, or RLCT extraction.
