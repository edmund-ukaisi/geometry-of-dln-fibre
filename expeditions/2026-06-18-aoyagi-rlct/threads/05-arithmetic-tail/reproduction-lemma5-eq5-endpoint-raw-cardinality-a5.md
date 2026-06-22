# Reproduction - Lemma 5 Eq5 endpoint raw branch cardinality

Date: 2026-06-22.

Scope: one-coordinate finite cardinality for the supplied Eq5 endpoint raw
branch set.  This is below the chart-family/source boundary: it assumes the
strict branch records, endpoint records, value formulas, alpha-domain coverage,
and value injectivity data.  It does not construct Aoyagi's branch records,
prove source-label legality, prove base-filter survival, prove no-extra
coverage, prove a Lemma 5 order count, prove pole order, prove normal
crossings, or extract RLCT data.

## Raw Branch Set

At an interior coordinate `j in {1,...,ell-1}`, the raw endpoint set is

```text
strict Eq5 branches at j
+ supplied upper endpoint
+ supplied lower endpoint if j <= a and j <= ell-a.
```

In Lean this is

```text
aoyagiLemma5Eq5EndpointRawBranches ell a strictBranches upper lower j.
```

The previous endpoint coverage slice proved:

```text
(raw_j.image value) = aoyagiHtildeIntervalValueSetNat ell a M m j.
```

The same-coordinate Htilde value set has cardinality

```text
aoyagiLemma5IntervalSize ell a j
```

for `j < ell+1`.

## Count Calculation

Assume `value` is injective on `raw_j`.  Then finite image cardinality gives

```text
|raw_j| = |raw_j.image value|.
```

Using the already-proved value-image equality:

```text
|raw_j.image value|
  = |aoyagiHtildeIntervalValueSetNat ell a M m j|.
```

Since `j` is an interior coordinate, `j < ell+1`, so the existing value-set
cardinality theorem gives:

```text
|aoyagiHtildeIntervalValueSetNat ell a M m j|
  = aoyagiLemma5IntervalSize ell a j.
```

Therefore:

```text
|raw_j| = aoyagiLemma5IntervalSize ell a j.
```

The alpha-injective wrapper supplies the raw value injectivity using the
previous theorem

```text
aoyagiLemma5Eq5EndpointRawBranches_value_injective_of_alpha_injective.
```

This keeps strict alpha injectivity explicit.  It does not prove strict alpha
injectivity from Aoyagi's source.

## Boundary Cases

The theorem is deliberately interior-coordinate.  It does not assert the same
cardinality at `j=0` or at the terminal coordinate.  At `j=0`, upper and lower
endpoint values can coincide, so the alpha-injective raw value-injectivity
argument is not valid in that form.

## Lean Targets

```text
aoyagiLemma5Eq5EndpointRawBranches_card_eq_intervalSize_of_value_injective
aoyagiLemma5Eq5EndpointRawBranches_card_eq_intervalSize_of_alpha_injective
```

## Nonclaims

- No construction of strict Eq5 or endpoint branch records.
- No source-label legality.
- No source-produced endpoint coordinate or value map.
- No endpoint base-filter survival theorem.
- No filtered nonbase branch cardinality theorem.
- No terminal-minimum exactness, no-extra coverage, pole order, normal
  crossings, or RLCT extraction.
