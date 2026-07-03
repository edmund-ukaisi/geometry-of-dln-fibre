# A2 with-following raw patch active containment with eventual source density

Date: 2026-07-03.

## Claim

The active-containment raw-patch handoff can consume a topological lower bound

```text
eventually z near z0, epsilon <= sourceDensity(z)
```

instead of requiring the caller to supply the a.e. lower bound on the final
returned neighborhood.

The endpoint-patch side conditions remain unchanged: for each
`P subset rawSourceSet`, the endpoint patch

```text
rawDetChart inter rawOrderOnEndpoint^{-1}(P)
```

must be null-measurable for `rawHaar`, and it must be contained in

```text
activeWriteback '' (activeChart '' (V inter sourceCylinder)).
```

The scalar remains existential and finite.

## Pen-and-paper chain

Suppose

```text
eventually z near z0, epsilon <= sourceDensity(z).
```

Choose an open neighborhood `H` of `z0` on which the inequality holds.  Apply
the active-containment source-density theorem to `G inter H`.  It returns an
open `V` with

```text
z0 in V,
V subset G inter H.
```

Since `V subset H`, every point of `V` satisfies
`epsilon <= sourceDensity(z)`.  Therefore the same inequality holds almost
everywhere for `baseJ.restrict V` by restriction to the measurable open set
`V`.

The active-containment source-density theorem then applies with this a.e.
lower bound.  It returns a finite scalar `Cdet` and the domination

```text
rawHaar.restrict P
  <= (Cdet * epsilon^{-1})
       * Measure.map rawMap (coordinateSourceMeasure.restrict V).
```

## Boundary

This only converts an eventual source-density lower bound to the a.e. lower
bound required by the local raw-patch handoff.  It does not prove
endpoint-patch null-measurability, source-density positivity, active endpoint
containment, exact raw-Haar pushforward, Haar normalization, determinant-chart
Haar transport, source coverage, source-rank coverage, normal crossings, pole
order, or RLCT extraction.
