# Reproduction - A2 canonical product-difference coefficient fields

Date: 2026-06-24.

Source context: Aoyagi 2023 preprint, p. 13, immediately after Theorem 3's
product reduction.  This note refines the already checked product-difference
entry-ideal calculation by fixing the coefficient blocks as deterministic
fields of the Lean suffix-state recursion.  It uses only Aoyagi's elementary
block calculation and the formalized suffix-state product reduction; it does
not use the quiver paper.

## Deterministic suffix-state blocks

For a suffix from `i` to `j`, the Lean recursion carries

```text
S = suffixState E j i hij
```

with fields

```text
S.L     : lower endpoint multiplier,
S.B     : accumulated right upper block,
S.Ctop  : top-left product block,
S.D     : lower-right transformed residual product.
```

The block-diagonal invariant says

```text
S.L * P(i,j) * [ I  -S.B ]
                   [ 0    I ]
  = [ S.Ctop  0 ]
    [ 0       S.D ].
```

The earlier triangular endpoint wrappers only exposed witnesses `F2`, `F3`,
and `Ctop`.  Here the intended canonical choices are

```text
F2    := -S.B,
F3    := lowerLeftBlock S.L,
Ctop  := S.Ctop,
D     := S.D.
```

These are deterministic functions of the input edge family and the chosen
suffix.  The lower-left choice is legitimate because the suffix recursion has
already been proved lower unitriangular:

```text
S.L = [ I  0 ]
      [ F3 I ].
```

Taking the lower-left block gives `F3 = lowerLeftBlock S.L`.

## Product-difference calculation with canonical fields

Let

```text
T  := P(i,j),
T0 := [ I 0 ]
      [ 0 0 ],
L  := [ I 0 ]
      [ lowerLeftBlock S.L  I ],
R  := [ I  -S.B ]
      [ 0    I ].
```

The block-diagonal invariant rewrites as

```text
L * T * R = [ S.Ctop 0 ]
            [ 0      S.D ].
```

Both `L` and `R` are determinant-unit triangular matrices, independently of
rank hypotheses.  Therefore the already formalized entry-ideal transport gives

```text
I(T - T0)
  = < entries(S.Ctop - I),
      entries(-S.B),
      entries(lowerLeftBlock S.L),
      entries(S.D) >.
```

This is the same algebra as the earlier p. 13 product-difference calculation:
the intermediate displayed lower-right block is

```text
S.D - (lowerLeftBlock S.L) * (-S.B),
```

and the product term is redundant modulo the entries of the two off-diagonal
blocks.

## Fixed-base endpoint specialization

For the endpoint fixed-base theorem, take

```text
i = 0,       j = Fin.last N,
E = paperEndpointFixedBaseEdgeMatrixOfReverseEdges ...
P = paperEndpointFixedBaseTotalMatrixOfReverseEdges ...
S = suffixState E (Fin.last N) 0 ...
```

The existing fixed-base product-reduction certificate supplies exactly the
block-diagonal invariant for this `S`.  Hence the endpoint product-difference
entry ideal has the deterministic generators

```text
S.Ctop - I,  -S.B,  lowerLeftBlock S.L,  S.D.
```

This theorem is rank-free.  It should not be bundled with source-rank
conclusions unless a downstream consumer explicitly needs that conjunction.

## Boundary

This is a scalar matrix-entry-ideal equality and a deterministic-field naming
handoff.  It does not assert exact-rank openness, source-rank neighborhood
construction, analytic germ-ideal transport, analytic regularity, chart
coverage, normal crossings, pole order, or RLCT.  It also does not identify
`S.D` with a raw product of untransformed lower-right edge blocks.
