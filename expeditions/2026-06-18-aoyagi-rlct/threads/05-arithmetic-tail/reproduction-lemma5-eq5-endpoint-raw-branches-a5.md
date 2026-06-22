# Reproduction - Lemma 5 Eq5 endpoint raw branches

Date: 2026-06-22.

Scope: one-coordinate finite supplied coverage assembly for equation `(5)`.
This packages strict Eq5 alpha branches together with supplied endpoint
branches into the raw branch set required by the supplied nonbase-family
constructor.  It does not construct the branch records, prove source-label
legality, prove branch injectivity, prove cross-coordinate disjointness, build
a classifier, prove no-extra terminal-minimum coverage, prove pole order, prove
normal crossings, or extract RLCT data.

## Source calculation

Aoyagi's equation `(5)` supplies strict offsets

```text
1 <= alpha < p
```

subject to the same-coordinate interval guard.  In the Lean notation this is

```text
alpha in aoyagiLemma5Eq5AlphaDomain ell a p
  = Icc 1 (min(excess_p, p-1)).
```

The strict own-coordinate values are

```text
Htilde'_p - alpha.
```

The already formalised value-image theorem says that if a finite supplied
strict branch set has alpha image equal to this alpha domain and each branch
has value `Htilde'_p-alpha`, then its value image is the Eq5 offset set

```text
E_p = { Htilde'_p - alpha | alpha in alpha-domain }.
```

The endpoint-deficit theorems split by the rising condition

```text
p <= a and p <= ell-a.
```

Off the rising region, `E_p` is the same-coordinate interval with the upper
endpoint erased:

```text
E_p = I_p.erase Htilde'_p.
```

In the rising region, `E_p` is the same-coordinate interval with both endpoints
erased:

```text
E_p = (I_p.erase Htilde'_p).erase Htilde_p.
```

Therefore a supplied upper endpoint branch fills the non-rising case, and
supplied upper and lower endpoint branches fill the rising case.

## Raw branch set

For a family of strict branch sets `strictBranches j` and supplied endpoint
records `upper j`, `lower j`, define

```text
rawBranches_j =
  if j <= a and j <= ell-a then
    insert (upper j) (insert (lower j) (strictBranches j))
  else
    insert (upper j) (strictBranches j).
```

For an interior coordinate `j=1,...,ell-1`, assume:

```text
(strictBranches j).image alphaOf = alpha-domain_j,
value b = Htilde'_j - alphaOf b        for b in strictBranches j,
value (upper j) = Htilde'_j,
value (lower j) = Htilde_j             in the rising case.
```

Then the value image of `rawBranches_j` is exactly `I_j`.

In the non-rising case:

```text
(insert upper strictBranches).image value
  = insert Htilde'_j E_j
  = insert Htilde'_j (I_j.erase Htilde'_j)
  = I_j.
```

In the rising case:

```text
(insert upper (insert lower strictBranches)).image value
  = insert Htilde'_j (insert Htilde_j E_j)
  = insert Htilde'_j (I_j.erase Htilde'_j)
  = I_j.
```

The final equality uses that `Htilde'_j` belongs to the interval for interior
`j`.

## Supplied-family assembly

The theorem above supplies only the `value_image` hypothesis of
`AoyagiLemma5SuppliedNonbaseFamily.ofCoordinateValueCoverage`.  The remaining
fields are still supplied:

```text
baseValue j in I_j,
Set.InjOn value rawBranches_j,
Disjoint rawBranches_i rawBranches_j   for i != j.
```

Filtering out the base value is then handled by the existing constructor.

## Lean targets

```text
aoyagiLemma5Eq5EndpointRawBranches
aoyagiLemma5Eq5EndpointRawBranches_value_image_eq_intervalValueSetNat
AoyagiLemma5SuppliedNonbaseFamily.ofEq5AlphaIndexedEndpointCoverage
```

## Nonclaims

- No construction of Eq5 strict or endpoint branch records.
- No proof that the supplied endpoint records are source-produced.
- No source-label legality.
- No proof of value injectivity or cross-coordinate disjointness.
- No base-value membership proof.
- No no-extra terminal-minimum classifier or order count.
- No pole order, normal crossings, or RLCT extraction.
