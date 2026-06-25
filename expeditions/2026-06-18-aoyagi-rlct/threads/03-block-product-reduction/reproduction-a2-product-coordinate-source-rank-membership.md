# Reproduction - A2 product-coordinate source-rank membership

Date: 2026-06-25.

Status: implemented in Lean; xhigh review passed for the stated
source-rank-membership scope.

## Source Anchor

Aoyagi PDF p. 13 writes the product-reduction coordinates after Theorem 3 as

```text
C1 - Er,   F2,   F3,   product_s C^(s).
```

The current fixed-base Lean product-coordinate constructor realizes the same
shape edgewise.  In a chain with regular corner size `r`, its raw edge
matrices have the three endpoint/middle forms

```text
[ I   0  ],       [ I   0 ],       [ Ctop   -Ctop F2 ],
[-F3  Cj ]        [ 0   Cj]        [ 0       Cj      ].
```

Here `Cj` is the transformed Schur residual block from the base source edge
family, and the left endpoint requires `det Ctop` to be a unit.

## Calculation

The product-coordinate constructor should preserve Aoyagi's source edge ranks
once the base family is already in the product-reduction chart and in the
source-rank stratum.

The rank calculations are elementary block algebra.

For the right endpoint,

```text
[ I  0 ] [ I   0  ] = [ I  0 ],
[ F3 I ] [-F3  Cj ]   [ 0  Cj]
```

and the left multiplier is block-unitriangular.  Therefore

```text
rank [ I   0  ] = r + rank(Cj).
     [-F3  Cj ]
```

For a middle edge the matrix is already block diagonal:

```text
rank [ I  0 ] = r + rank(Cj).
     [ 0  Cj]
```

For the left endpoint,

```text
[ Ctop  -Ctop F2 ] [ I  F2 ] = [ Ctop  0 ],
[ 0      Cj      ] [ 0  I  ]   [ 0     Cj]
```

and the right multiplier is block-unitriangular.  Since `det Ctop` is a unit,
`rank(Ctop)=r`, hence again

```text
rank [ Ctop  -Ctop F2 ] = r + rank(Cj).
     [ 0      Cj      ]
```

Now suppose the base source point `x` is in
`paperEndpointFixedBaseSourceRankStratum ... r rEdge`, and suppose the base
edge family has a product-reduction certificate at `x`.  The existing
source-rank residual theorem gives

```text
rank(Cj) = rEdge j - r.
```

The source-rank stratum also records `r <= rEdge j`, so

```text
r + rank(Cj) = r + (rEdge j - r) = rEdge j.
```

Finally, fixed-base edge matrix rank is the finrank of the underlying edge
map's range.  Thus the product-coordinate edge family at `(x,u)` has the same
edge ranks `rEdge j`.  The base product rank and source inequalities are
constant fields of the source-rank stratum, so the product-coordinate point is
again in the source-rank stratum.

For a local source statement, choose the regular-coordinate radius small
enough that `det Ctop(u)` is a unit throughout the Euclidean ball; the existing
small-radius determinant theorem supplies this.

## Lean Target

The intended Lean increment is:

```text
ChartLocalSuffixState.rank_productCoordinateRightEndpointMatrix
ChartLocalSuffixState.rank_productCoordinateMiddleMatrix
ChartLocalSuffixState.rank_productCoordinateLeftEndpointMatrix

paperEndpointFixedBaseMultiEdgeProductCoordinateEdgeFamilyOfBaseEdgeFamilyEuclidean_mem_sourceRankStratum
exists_pos_radius_le_multiEdgeProductCoordinateEdgeFamilyOfBaseEdgeFamilyEuclidean_mem_sourceRankStratum_nhdsWithin_source
```

The pointwise source-rank theorem should require:

- a base product-reduction certificate for the base edge family at `x`;
- membership of `x` in the base source-rank stratum;
- `IsUnit det(Ctop(u))`.

The local theorem should combine the existing small-radius `Ctop` unit theorem
with eventual base product-reduction certificates.

## Nonclaims

- No proof that the product-coordinate map is locally surjective onto the
  source-rank stratum.
- No equality between the source-rank stratum and the image of the product
  chart.
- No exact-rank openness theorem.
- No analytic inverse-function theorem.
- No Jacobian determinant or density computation.
- No ideal-germ transport, normal crossings, pole order, or RLCT extraction.

## Kill Conditions

- Deriving residual factor ranks from source-rank membership alone, without a
  product-reduction/determinant-chart certificate.
- Treating the local radius as an exact-rank neighborhood rather than only a
  `Ctop` determinant-unit neighborhood.
- Reading source-rank image membership as source coverage or source equality.

## Review and Verification

Review:
`review-a2-product-coordinate-source-rank-membership.md`.

The Lean implementation proves exactly the three block-rank calculations and
the product-coordinate source-rank image-membership statements above.  The
reviewers accepted the slice under the explicit nonclaim boundary: it is
source-rank preservation for the constructed product-coordinate family, not a
source chart, local image equality, density/Jacobian transport, normal
crossing construction, pole-order theorem, or RLCT theorem.
