# A2 p.13 Original-Prior Full-Product Domination

## Source calculation

Aoyagi separates two elementary measure effects in the p.13 / Case 2
calculation.

First, the selected-entry blow-up chart is finite-dimensional.  For a residual
block index set

```text
I = {J+1,...,M(S)} x {J+1,...,M(S+1)}
```

with chosen pivot `p`, write the source variables as

```text
x_p = u,
x_q = u y_q  for q != p.
```

With the pivot coordinate first, the derivative matrix is block triangular:

```text
[ 1      0 ]
[ y_q  u I ]
```

Hence the absolute Jacobian factor is `|u|^(card I - 1)`.  In the Lean
selected-entry API this is the density

```text
SelectedEntrySignedBox.CenterCoord.sourceDensity pivot y
  = |y none| ^ ((center.erase pivot).card : R),
```

and the already-landed pushforward theorem identifies the weighted signed-box
source measure with Lebesgue measure on the selected-entry chart image.  This
is Aoyagi's p.15 differential-form factor and p.20 Case 2 update
`M'_{S,J+1} = card I`.

Second, Aoyagi p.13 treats the remaining regular variables `(Ctop - I, F2,
F3)` as a product Euclidean factor.  In Lean this factor is represented by an
arbitrary right measure `nu`; the p.13 regular-coordinate use case is obtained
by taking

```text
nu : Measure (EuclideanSpace R (AoyagiRegularBlockCoordinateIndex rho mu nuIndex)).
```

## Lean target

The existing one-factor theorem proves, on a p.13 chart piece,

```text
originalPrior.restrict chartPiece
  <= (ofReal Kprior * cHaar^{-1}) • muP13,
```

where `muP13` is the formal-product p.13 chart measure

```text
map p13SourceChart
  ((m.restrict detChart).withDensity formalProductAbsDet)
  restricted to chartPiece.
```

The full-product calculation is just product monotonicity on the regular
variables:

```text
(originalPrior.restrict chartPiece).prod nu
  <= (ofReal Kprior * cHaar^{-1}) • (muP13.prod nu).
```

This is the exact handoff needed by full p.13 regular-coordinate finite
integral sockets: the regular variables are present in the measure statement,
but no claim is made that the original full DLN prior has already been
transported through the whole product-coordinate map.

## Boundary and kill conditions

- This proves a full product-measure domination, not an exact full
  source-prior pullback density.
- The prior-density upper bound on the original edge-family chart piece remains
  explicit.
- The tuple-side Haar scalar remains explicit; it is not normalized to `1`.
- The formal-product p.13 measure is the existing chart measure; this theorem
  does not identify it with a passive-theta source-image reference.
- This theorem does not prove source coverage, chart-image equality,
  source-rank coverage, determinant/raw Haar transport, source-density
  positivity, normal crossings, pole order, or RLCT.
