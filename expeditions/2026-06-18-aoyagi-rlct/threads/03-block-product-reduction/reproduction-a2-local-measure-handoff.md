# Reproduction - A2 local measure handoff

Date: 2026-06-25.

Status: small support theorem formalised in Lean.

## Motivation

Several p.13 source-side results are stated as relative-neighborhood facts:

```text
forall eventually x in nhdsWithin x0 sourceStratum, P(x).
```

The product-measure finite-side integrability adapters consume a.e.
hypotheses.  A chart construction should eventually provide the actual
coordinate map and product measure, but one elementary handoff is independent
of that chart: if a property holds throughout a relative neighborhood, then
it holds almost everywhere for any measure restricted to a sufficiently small
measurable source neighborhood.

## Derivation

Assume

```text
hP : forall eventually x in nhdsWithin x0 S, P(x).
```

By the definition of `nhdsWithin`, there exists an open set `U` with
`x0 in U` such that

```text
U inter S subset {x | P(x)}.
```

If `S` is measurable and open sets are measurable for the topology, then
`U inter S` is measurable.  Mathlib's restricted-measure lemma gives

```text
forall almost every x with respect to mu.restrict (U inter S), x in U inter S.
```

Composing with the subset above gives

```text
forall almost every x with respect to mu.restrict (U inter S), P(x).
```

For a product measure over an auxiliary coordinate space, the same base
restricted-measure a.e. fact pulls back along first projection:

```text
forall almost every z with respect to (mu.restrict (U inter S)).prod nu,
  P(z.1).
```

This is exactly `Measure.quasiMeasurePreserving_fst`.

## Lean Shape

Lean proves this in

```text
lean/DLNFibre/DLN/Aoyagi/LocalMeasureHandoff.lean
```

with names

```text
exists_open_ae_restrict_inter_of_eventually_nhdsWithin
exists_open_ae_restrict_inter_prod_fst_of_eventually_nhdsWithin
```

## Boundary

This theorem does not construct the p.13 product chart, identify source
coordinates with residual-base plus regular-fiber coordinates, compare losses,
transport density/Jacobian factors, prove integrability, produce normal
crossings, or extract RLCT.  It only turns a relative-neighborhood property
into an a.e. property after restricting the base measure to a small measurable
source neighborhood.
