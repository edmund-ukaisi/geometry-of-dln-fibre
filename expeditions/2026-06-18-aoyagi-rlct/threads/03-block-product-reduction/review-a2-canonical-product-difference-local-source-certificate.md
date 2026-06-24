# Review - A2 canonical product-difference local source certificate

Date: 2026-06-24.

Reviewer: xhigh read-only reviewer `Euclid the 3rd`.

## Verdict

PASS after documentation wording fixes.

## Findings Resolved

The reproduction originally called the `exists_source_neighborhood` projection
an "ordinary source neighborhood".  That overstated the theorem: Lean returns
an ordinary ambient neighborhood `U ∈ nhds x0`, while source-rank membership
remains an explicit antecedent for points in `U`.  The reproduction now calls
this an ordinary ambient neighborhood with a source-stratum guard.

The reproduction also used the old field name `local`; the Lean field is
`localCertificate`.  The wording now matches the Lean structure.

## Checked Lean Scope

The Lean statements correctly avoid exact-rank/source-rank openness.  The
existing local predicate remains a `nhdsWithin` statement relative to
`paperEndpointFixedBaseSourceRankStratum`, and the new projection keeps
source-stratum membership as an explicit guard.

The basepoint membership inputs are exactly the supplied source rank data:

```text
rank(paperTotalMap B) = r,
rank(reverseEdge B p) = rEdge p,
r <= rEdge p.
```

These feed directly into
`paperEndpointFixedBaseSourceRankStratum_selfBase_mem`, so the package is
nonvacuous at the base parameter without proving rank-stratum openness.

## Verification

The reviewer reported:

```text
lake env lean DLNFibre/DLN/Aoyagi/ProductReductionEntryIdealBoundary.lean
```

passed.  The reviewer could not run `scripts/lb ...` because the shared
`~/.lake-shared/slots` files are read-only in this environment.

