# Reproduction - A2 measurable local source from source certificate

Date: 2026-06-25.

## Source Target

Aoyagi pp. 10-13 work locally on a source-shaped rank stratum before the p.13
regular-product coordinates are used.  In Lean this source condition is
encoded as

```text
paperEndpointFixedBaseSourceRankStratum W B Cedge r rEdge.
```

The fixed-base local source certificate already gives the canonical
product-difference/source-rank conclusion in a relative neighborhood of `x0`
within this stratum.  The missing packaging step is to turn that relative
neighborhood into an explicit measurable local source set usable by the
local-source finite-integral sockets.

## Calculation

Let

```text
S = paperEndpointFixedBaseSourceRankStratum W B Cedge r rEdge.
```

The certificate supplies

```text
eventually, in nhdsWithin x0 S,
  PaperEndpointFixedBaseCanonicalProductDifferenceSourceRanks ...
```

and basepoint membership `x0 in S`.  Expanding `nhdsWithin`, choose an ordinary
neighborhood `U0loc in nhds x0` such that every point of `U0loc inter S`
satisfies the canonical source-rank conclusion.  Since `U0loc` is a
neighborhood, choose an open set `U` with

```text
x0 in U,   U subset U0loc.
```

Define the local source

```text
source = U inter S.
```

Then:

- `x0 in source`, because `x0 in U` and the certificate gives `x0 in S`;
- `source subset S`, by the second projection;
- if `S` is measurable, then `source` is measurable because `U` is open and
  hence measurable;
- every `x in source` satisfies the canonical product-difference source-rank
  conclusion, because `x in U subset U0loc` and `x in S`.

If the fixed-base edge-matrix family is measurable, the existing finite-rank
stratum theorem gives measurability of `S`, so the same construction produces
a measurable local source from the edge-matrix measurability hypothesis.

For regular-coordinate source data, the same construction is applied to
`sourceData.localSourceCertificate`.  Since `U in nhds x0`,

```text
nhdsWithin x0 (U inter S) = nhdsWithin x0 S.
```

Thus source-stratum-local lower bounds already proved for the regular
coordinate data can be reused on the explicit local source without changing
their filter statement.

## Lean Statement Shape

The certificate layer proves:

```text
PaperEndpointFixedBaseCanonicalProductDifferenceLocalSourceCertificate.exists_measurable_localSource

PaperEndpointFixedBaseCanonicalProductDifferenceLocalSourceCertificate.exists_measurable_localSource_of_measurable_edgeMatrix
```

The source-data layer proves:

```text
PaperEndpointFixedBaseRegularCoordinateSourceData.exists_measurable_localSource_nhdsWithin_of_measurable_edgeMatrix
```

The source-data theorem returns `source` and `U`, proves measurability,
basepoint membership, source-stratum inclusion, source-rank conclusions on
`source`, and the `nhdsWithin` equality above.

## Nonclaims

This slice does not construct a signed-box chart, prove a chart image/source
coverage theorem, prove a weighted pushforward, compute a Jacobian or
source-density factor, produce residual or source-density monomial-unit
identities, prove normal crossings, compute pole order, or extract an RLCT.
It is only the measurable local-source package sitting before those chart
obligations.
