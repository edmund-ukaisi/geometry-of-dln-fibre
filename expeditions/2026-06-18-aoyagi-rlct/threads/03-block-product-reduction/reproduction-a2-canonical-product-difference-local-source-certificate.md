# Reproduction - A2 canonical product-difference local source certificate

Date: 2026-06-24.

Status: pen-and-paper reproduction before Lean implementation.

## Question

The canonical product-difference local certificate is relative to Aoyagi's
source-shaped rank stratum.  That relative statement is the right topology:
exact-rank strata are not open in general.  But the package is vacuous if the
source stratum is empty.

Can we add the elementary source-rank input that proves the base parameter is
inside the source stratum, without claiming the stratum is open?

## Source Anchor

Aoyagi Theorem 3 and the paragraph after it, PDF pp. 11-13, work at a base
chain whose total product has rank `r` and whose layer maps have ranks
`rEdge p`.  The local product-reduction calculation is then performed on that
source rank locus.

The existing Lean source-shaped stratum records exactly these ingredients:

```text
rank(total product of B) = r,
rank(Cedge x p) = rEdge p for every p,
r <= rEdge p for every p.
```

## Reproduction

Fix a base paper chain `B`, a continuous reversed-edge family `Cedge`, and a
base parameter `x0` with

```text
Cedge x0 p = reverseEdge B p
```

for every edge `p`.

Assume the source rank data at the base chain:

```text
rank(paperTotalMap B) = r,
rank(reverseEdge B p) = rEdge p,
r <= rEdge p.
```

Then the base parameter is in the source-shaped rank stratum.  The proof is
only substitution: at `x0`, each `Cedge x0 p` is the base edge, so its rank is
`rEdge p`; the total product rank and inequalities are supplied.

Combine this basepoint membership with the existing canonical product-
difference local certificate:

```text
PaperEndpointFixedBaseCanonicalProductDifferenceLocalCertificate
```

which already contains:

- centered continuous canonical fields
  `S.Ctop - 1`, `-S.B`, `lowerLeftBlock S.L`, and `S.D`;
- a `nhdsWithin` conclusion relative to the source-shaped rank stratum whose
  pointwise predicate has the canonical product-difference entry-ideal
  equality and residual-rank formulas.

The new package is therefore nonvacuous at the base point when Aoyagi's source
rank data is supplied, while still remaining relative to the rank stratum.

## Lean Shape

Add in
`lean/DLNFibre/DLN/Aoyagi/ProductReductionEntryIdealBoundary.lean`:

```text
PaperEndpointFixedBaseCanonicalProductDifferenceLocalSourceCertificate

paperEndpointFixedBaseCanonicalProductDifferenceLocalSourceCertificate_of_isCompl

PaperEndpointFixedBaseCanonicalProductDifferenceLocalSourceCertificate.exists_source_neighborhood

PaperEndpointCanonicalProductDifferenceLocalSourceCertificate

exists_paperEndpointCanonicalProductDifferenceLocalSourceCertificate
```

The fixed-base structure should contain:

- `localCertificate : PaperEndpointFixedBaseCanonicalProductDifferenceLocalCertificate ...`
- `source_basepoint : x0 ∈ paperEndpointFixedBaseSourceRankStratum ...`

The projection theorem should unpack the existing `nhdsWithin` statement into
an ordinary ambient neighborhood with a source-stratum guard:

```text
∃ U ∈ nhds x0, x0 ∈ U ∧
  ∀ x ∈ U, x ∈ sourceRankStratum -> canonical source-rank conclusion at x.
```

## Kill Conditions

- If the theorem asserts the exact-rank or source-rank stratum is open, it is
  too strong.
- If it drops the explicit base product/layer rank hypotheses, it becomes
  source-unsound.
- If it changes the local certificate's `nhdsWithin` statement into an
  ordinary neighborhood statement, it is wrong.
- If it claims analytic regularity, ideal or germ transport, regular
  suspension, normal crossings, pole order, or RLCT, it is too strong.
