# Statement Card - A2 regular-suspension coordinate index

Date: 2026-06-24.

Lean file:
`lean/DLNFibre/DLN/Aoyagi/RegularSuspensionCoordinates.lean`

## Lean Names

```text
AoyagiRegularBlockCoordinateIndex
AoyagiRegularBlockCoordinateIndex.card
AoyagiRegularBlockCoordinateIndex.value
AoyagiRegularBlockCoordinateIndex.value_centered_continuousAt
AoyagiRegularBlockCoordinateIndex.card_eq_aoyagiTheorem2RegularVariableCount
paperEndpointEndpointComplementIndex_card_eq_layerSubRank
paperEndpointRegularBlockCoordinateIndex_card_eq_regularVariableCount
PaperEndpointFixedBaseCanonicalProductDifferenceLocalCertificate.regularBlockScalarCoordinates_centered_continuousAt
PaperEndpointFixedBaseCanonicalProductDifferenceLocalCertificate.regularBlockCoordinateIndex_card_eq_regularVariableCount
```

## Statement Shape

`AoyagiRegularBlockCoordinateIndex ι μ ν` is the finite disjoint union of
entries of the three regular p. 13 blocks:

```text
(ι x ι) ⊔ (ι x ν) ⊔ (μ x ι).
```

Its cardinality is

```text
card ι * card ι + card ι * card ν + card μ * card ι.
```

Under explicit endpoint-cardinality hypotheses

```text
card ι = r,
card μ = H 1 - r,
card ν = H (L+1) - r,
```

Lean rewrites the coordinate count to
`aoyagiTheorem2RegularVariableCount L H r`.

For the endpoint-compatible fixed-base index, Lean derives the needed endpoint
cardinalities from the complement construction.  The local source-certificate
version uses the basepoint product-rank field and the dimension convention
`H(k+1)=finrank(W k)` to prove the same count with
`L = N`.

The local-certificate theorem projects
`PaperEndpointFixedBaseCanonicalProductDifferenceLocalCertificate` to centered
continuous scalar coordinates for `S.Ctop - 1`, `-S.B`, and
`lowerLeftBlock S.L`.

## Scope

Finite scalar-coordinate bookkeeping and componentwise continuity only.

## Nonclaims

No analytic regular-coordinate construction, `Cfull` construction, ideal
transport, coverage, Jacobian compatibility, exponent shift, normal crossings,
pole order, or RLCT.  The scalar-coordinate index also does not prove the
four-block ideal split.
