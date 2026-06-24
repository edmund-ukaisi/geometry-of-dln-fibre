# Reproduction - A2 regular-suspension coordinate index

Date: 2026-06-24.

Status: reproduced before Lean implementation.

## Source Anchor

Aoyagi PDF p. 13 identifies three regular block families after product
reduction:

```text
C1 - Er,    F2,    F3.
```

Their displayed scalar count is

```text
r^2 + r(H^(L+1)-r) + (H^(1)-r)r.
```

This count is the finite regular-variable count already formalised as
`aoyagiTheorem2RegularVariableCount L H r`.

## Coordinate Index

Let

```text
ι = rank-r through-coordinate index,
μ = source residual-coordinate index,
ν = target residual-coordinate index.
```

The scalar regular coordinates are the disjoint union

```text
(ι x ι)       -- entries of Ctop - 1
⊔ (ι x ν)     -- entries of F2
⊔ (μ x ι).    -- entries of F3
```

Lean records this as

```text
AoyagiRegularBlockCoordinateIndex ι μ ν.
```

The corresponding coordinate-value map sends this disjoint union to entries of
three supplied matrices

```text
X : Matrix ι ι R,  F2 : Matrix ι ν R,  F3 : Matrix μ ι R.
```

## Count

The cardinality is immediate finite bookkeeping:

```text
card = card ι * card ι + card ι * card ν + card μ * card ι.
```

If the three endpoint-cardinality identifications are supplied,

```text
card ι = r,
card μ = H 1 - r,
card ν = H (L+1) - r,
```

then this is exactly

```text
aoyagiTheorem2RegularVariableCount L H r.
```

For the fixed-base endpoint complements used by the canonical product-difference
certificate, Lean also proves the endpoint counts.  If `U0` is complementary
to the total kernel, then the endpoint complement at a reversed vertex `j` has
cardinality

```text
finrank(reverseVertex W j) - finrank(U0).
```

The proof is finite linear algebra: the transported through-subspace and the
chosen endpoint complement are complementary subspaces of the ambient vertex,
and the through-subspace has the same finrank as `U0` because `U0` is disjoint
from the relevant suffix-kernel composite.

With the base product-rank equality

```text
finrank(range paperTotalMap) = r
```

and the source dimension convention

```text
H(k+1) = finrank(W k),
```

the reversed endpoint `Fin.last N` gives the source residual count `H 1 - r`,
and the reversed endpoint `0` gives the target residual count `H(N+1)-r`.
Thus the local source certificate carries enough basepoint rank data to identify
the endpoint-compatible scalar coordinate count with
`aoyagiTheorem2RegularVariableCount N H r`.

## Local-Certificate Projection

The already proved canonical product-difference local certificate contains
centered continuity for the block fields

```text
S.Ctop - 1,   -S.B,   lowerLeftBlock S.L,   S.D.
```

The regular-coordinate index uses only the first three fields.  Lean projects
the existing blockwise centered-continuity package to every scalar coordinate
of

```text
S.Ctop - 1,   -S.B,   lowerLeftBlock S.L.
```

The residual field `S.D` is intentionally excluded from the regular-coordinate
index.

## Nonclaims

- No construction of analytic regular coordinates.
- No construction of `Cfull`.
- No analytic ideal or germ transport theorem.
- No chart coverage theorem.
- No Jacobian compatibility theorem.
- No exponent-shift proof.
- No normal-crossing production, pole-order theorem, or RLCT theorem.
- No claim that these scalar coordinates by themselves split the four-block
  ideal or supply a regular-suspension chart.
