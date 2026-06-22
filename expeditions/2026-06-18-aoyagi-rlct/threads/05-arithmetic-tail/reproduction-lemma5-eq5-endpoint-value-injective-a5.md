# Reproduction - Lemma 5 Eq5 endpoint raw value injectivity

Date: 2026-06-22.

Scope: finite one-coordinate injectivity bookkeeping for the Eq5 endpoint raw
branch set.  This does not construct Aoyagi's branch records, prove source
production, prove source-label legality, prove base-value survival, construct a
classifier, prove no-extra coverage, prove pole order, prove normal crossings,
or extract RLCT data.

## Raw branch set

For an interior coordinate `j in Finset.Icc 1 (ell - 1)`, the endpoint raw
branch set is

```text
raw_j =
  if j <= a and j <= ell-a then
    insert (upper j) (insert (lower j) (strictBranches j))
  else
    insert (upper j) (strictBranches j).
```

The strict Eq5 branch records carry an alpha parameter.  The supplied data for
one coordinate is

```text
image alphaOf (strictBranches j) = Eq5AlphaDomain(ell,a,j),
value b = Htilde'_j - alphaOf b      for b in strictBranches j,
value (upper j) = Htilde'_j,
value (lower j) = Htilde_j           in the rising case,
alphaOf injective on strictBranches j.
```

The strict alpha domain is

```text
1 <= alpha <= min(intervalExcess(ell,a,j), j-1).
```

Equivalently, the strict branch value image is the Eq5 offset-value set

```text
{ Htilde'_j - alpha | alpha in Eq5AlphaDomain(ell,a,j) }.
```

## Strict-strict case

If `b,c in strictBranches j` and `value b = value c`, then

```text
Htilde'_j - alphaOf b = Htilde'_j - alphaOf c,
```

so `alphaOf b = alphaOf c`.  The supplied injectivity of `alphaOf` on
`strictBranches j` gives `b=c`.

## Upper endpoint versus strict branches

The upper endpoint value `Htilde'_j` is not in the Eq5 offset-value set:
reaching it would require alpha `0`, while the strict domain has `1 <= alpha`.
Thus `upper j` cannot have the same value as any strict branch record, unless
the supplied hypotheses are inconsistent, in which case the injectivity goal is
vacuous.

## Lower endpoint in the rising case

The lower endpoint is explicitly inserted only when `j <= a` and
`j <= ell-a`.  In that region the interval excess is `j`, so the lower endpoint
would require offset alpha `j`.  The strict Eq5 domain only has `alpha < j`.
Therefore `Htilde_j` is not in the Eq5 offset-value set, and `lower j` cannot
share a value with a strict record.

The upper and lower endpoint values are also distinct in the rising case:

```text
Htilde'_j - Htilde_j = intervalExcess(ell,a,j) = j,
```

and the interior-coordinate hypothesis gives `1 <= j`.

## Non-rising case

If the rising guard fails, the raw branch set only inserts the upper endpoint
and the strict branches.  The strict-strict and upper-versus-strict arguments
above prove injectivity on that raw set.

## Boundary caveat

The interior-coordinate hypothesis is essential.  At `j=0`, the rising raw set
could insert both endpoint records while

```text
Htilde'_0 - Htilde_0 = intervalExcess(ell,a,0) = 0,
```

so the two endpoint values can coincide if the endpoint records are distinct.
The theorem therefore keeps `j in Finset.Icc 1 (ell - 1)`.  At `j=1`, the
rising strict alpha domain is empty but the endpoint gap is `1`, so the
endpoint-only raw set is still value-injective.

## Constructor wrapper

The previous endpoint supplied-family constructor kept raw value injectivity
and cross-coordinate raw disjointness as supplied fields.  Combining this raw
value-injectivity theorem with the coordinate-disjointness theorem gives a
wrapper that replaces those two fields by:

```text
strict alpha injectivity on strictBranches j,
strict/upper/lower component coordinate correctness.
```

The wrapper still assumes base-value membership, alpha-domain coverage, strict
and endpoint value equalities, and the supplied component coordinate facts.  It
does not construct the strict or endpoint records.

## Lean targets

```text
aoyagiLemma5Eq5EndpointRawBranches_value_injective_of_alpha_injective
AoyagiLemma5SuppliedNonbaseFamily.ofEq5AlphaIndexedEndpointCoverage_of_alphaInjective_branchCoord
```

## Nonclaims

- No construction of strict Eq5 or endpoint branch records.
- No source proof of strict alpha injectivity.
- No endpoint source production or source-label legality.
- No endpoint distinctness theorem as a standalone source fact.
- No base-filter survival theorem.
- No counted-datum classifier or no-extra terminal-minimum coverage theorem.
- No pole order, normal crossings, or RLCT extraction.
