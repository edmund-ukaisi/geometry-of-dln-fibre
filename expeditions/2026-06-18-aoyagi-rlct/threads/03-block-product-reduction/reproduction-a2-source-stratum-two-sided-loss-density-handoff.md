# Reproduction - A2 source-stratum two-sided loss-density handoff

Date: 2026-06-29.

Status: pen-and-paper checked; Lean formalised as a source-stratum wrapper.

## Source Anchor

Aoyagi PDF p. 13 uses the source-rank stratum as the base locus for the
regular/residual square model.  The previous checkpoint proved the local-source
filter-to-product-measure handoff for four supplied two-sided loss and density
bounds.  The present step specializes that handoff to

```text
paperEndpointFixedBaseSourceRankStratum (K := R) W B Cedge r rEdge.
```

It adds no new analytic content: the source-rank stratum is used as the
restriction set in the measure, not proved to be open, covered by a chart, or
equal to a chart image.

## Calculation

Let

```text
S = paperEndpointFixedBaseSourceRankStratum (K := R) W B Cedge r rEdge.
```

Assume that in `nhdsWithin x0 S`, uniformly for all regular coordinates `u` in
`ball(0,R)`, the four bounds are supplied:

```text
cL * model(x,u) <= loss(x,u),
loss(x,u) <= CL * model(x,u),
dRho <= density(x,u),
density(x,u) <= DRho.
```

The local-source theorem applies with `source := S`, giving an open `U` with
`x0 in U` and the four corresponding a.e. facts over

```text
(mu.restrict (U inter S)).prod nu.
```

The wrapper only expands `S` back to the source-rank-stratum expression in the
statement and conclusion.

## Lean Shape

Lean formalises this in

```text
lean/DLNFibre/DLN/Aoyagi/RegularSuspensionLocalMeasure.lean
```

with:

```text
exists_open_ae_restrict_source_prod_p13RegularCoordinates_two_sided_loss_density_bounds
```

The proof introduces the local abbreviation `sourceStratum`, calls

```text
exists_open_ae_restrict_localSource_prod_p13RegularCoordinates_two_sided_loss_density_bounds
```

with `source := sourceStratum`, and rewrites the witness back by `simpa
[sourceStratum]`.

Focused build:

```text
cd lean
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre.DLN.Aoyagi.RegularSuspensionLocalMeasure
```

passed.

## Nonclaims

- No proof of the four supplied comparison bounds.
- No positivity assumptions or conclusions for `R`, `cL`, `CL`, `dRho`, or
  `DRho`.
- No proof that the source-rank stratum is open, a neighborhood, chart-covered,
  or a chart image.
- No selected-entry image equality, local inverse, source-prior transport,
  Jacobian/density transport, or product-measure transport.
- No proof of residual positivity, residual boundedness, residual
  measurability, or residual negative-power integrability.
- No finite integral, integrability iff, normal-crossing theorem, pole-order
  theorem, or RLCT extraction.
