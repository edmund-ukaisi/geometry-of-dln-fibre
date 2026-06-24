# Statement card - A2 canonical product-difference local certificate

Status: Lean implementation landed and reviewed.

Reproduction:
`reproduction-a2-canonical-product-difference-local-certificate.md`.

Review:
`review-a2-canonical-product-difference-local-certificate.md`.

## Target

Package the p. 13 canonical product-difference fields in the local shape
needed by later regular-suspension work: centered continuous coefficient
fields at the self-base chain, plus pointwise canonical product-difference
entry-ideal and residual-rank conclusions on the source-rank stratum
neighborhood.

## Lean Artifacts

New declarations in
`lean/DLNFibre/DLN/Aoyagi/ProductReductionEntryIdealBoundary.lean`:

```text
PaperEndpointFixedBaseCanonicalProductDifferenceSourceRanks

PaperEndpointFixedBaseProductReductionCertificate
  .toCanonicalProductDifferenceSourceRanks

paperEndpointFixedBaseCanonicalProductDifferenceSourceRanks_selfBase_mem_nhdsWithin_source

PaperEndpointFixedBaseCanonicalProductDifferenceLocalCertificate

paperEndpointFixedBaseCanonicalProductDifferenceLocalCertificate_of_isCompl

PaperEndpointCanonicalProductDifferenceLocalCertificate

exists_paperEndpointCanonicalProductDifferenceLocalCertificate
```

The pointwise source-rank predicate uses the deterministic suffix-state fields

```text
S.Ctop - 1,
-S.B,
lowerLeftBlock S.L,
S.D.
```

in the matrix-entry ideal equality, not existential triangular witnesses.

The fixed-base local certificate contains the centered-continuity theorem for
the same four fields and a `nhdsWithin` conclusion relative to
`paperEndpointFixedBaseSourceRankStratum`.

## Scope

This is a local elementary/topological boundary only.  It does not assert that
exact-rank or source-rank strata are open.  It does not prove analytic
regularity, analytic ideal or germ transport, chart coverage, a
regular-suspension certificate, normal crossings, pole order, or RLCT.

## Verification

Controller verification passed:

```text
cd lean && LEAN_NUM_THREADS=1 ~/.elan/bin/lake env lean DLNFibre/DLN/Aoyagi/ProductReductionEntryIdealBoundary.lean
cd lean && LEAN_NUM_THREADS=1 ~/.elan/bin/lake build DLNFibre.DLN.Aoyagi.ProductReductionEntryIdealBoundary
```
