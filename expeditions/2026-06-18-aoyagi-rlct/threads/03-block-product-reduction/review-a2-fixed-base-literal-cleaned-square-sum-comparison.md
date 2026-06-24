# Review - A2 fixed-base literal-cleaned square-sum comparison

Date: 2026-06-24.

Reviewer: xhigh scout `Linnaeus the 4th`.

Status: passed; recommended API implemented with one literal coordinate-map
definition, conjunction theorem, and directional wrappers.

## Reviewed Shape

The reviewer recommended adding

```text
paperEndpointFixedBaseLiteralProductDifferenceCoordinateMap
```

immediately after the cleaned fixed-base product-difference coordinate map.
This avoids restating the suffix-state `E`/`S` expression in downstream
theorems and centralises the p. 13 sign convention.

The literal map is exactly

```text
literalValue (S.Ctop - 1) (-(S.B)) (lowerLeftBlock S.L) S.D.
```

The review emphasised that `F2 = -(S.B)` is the correct cleaned coordinate
field; using `S.B` would be a sign error.

## Proof Check

The implemented proof follows the reviewed route:

1. use the fixed-base `F2/F3` smallness theorem from source data;
2. unfold the fixed-base regular-coordinate map at each nearby point to obtain
   the finite smallness hypothesis for `-(S.B)` and `lowerLeftBlock S.L`;
3. apply the existing finite factor-`2` comparison theorems;
4. finish by unfolding the cleaned and literal fixed-base coordinate maps;
5. derive relative source-rank-stratum versions by filter weakening.

Directional wrappers were added as projections from the conjunction theorem,
matching the reviewer's API recommendation.

The focused build passed:

```text
lean/scripts/lb DLNFibre.DLN.Aoyagi.RegularSuspensionCoordinates
```

## Nonclaims

This proves only finite square-sum comparability on an eventual neighborhood.
It does not prove analytic ideal transport, chart construction, source
coverage, source-rank openness, normal crossings, pole order, or RLCT.
