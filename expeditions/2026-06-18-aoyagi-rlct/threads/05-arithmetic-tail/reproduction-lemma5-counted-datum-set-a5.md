# Reproduction - Lemma 5 Counted Datum Set

Status: elementary finite-count layer; formalisation-ready.

Aoyagi's Lemma 5 upper-bound paragraph motivates an interval-count upper-bound
shape.  The Lean codomain model used here has one supplied base datum and, for
each interior coordinate `j=1,...,ell-1`, the nonbase values in the interval

```text
Htilde_j <= H <= Htilde'_j.
```

The existing Lean development already proves the interval value set

```text
aoyagiHtildeIntervalValueSetNat ell a M m j
```

and the aggregate identity

```text
1 + sum_{j=1}^{ell-1} (|I_j|-1) = a*(ell-a)+1.
```

This note turns that arithmetic into an explicit finite set of counted data.

## Counted Data

Fix a supplied base value

```text
baseValue : Nat -> Int
```

with

```text
baseValue j in I_j
```

for each interior coordinate `j=1,...,ell-1`.

The counted datum set is:

```text
{base} union
  { (j,H) : j in {1,...,ell-1},
            H in I_j,
            H != baseValue j }.
```

In Lean the base datum is represented by `none`; the nonbase datum `(j,H)` is
represented by `some (Sigma.mk j H)`.

## Count

For a fixed interior `j`, erasing `baseValue j` from `I_j` has cardinality
`|I_j|-1`, because `baseValue j in I_j`.

The pair tag `j` makes the nonbase sets for distinct coordinates disjoint.
The base tag `none` is disjoint from every nonbase datum.  Therefore

```text
|countedDatumSet|
  = 1 + sum_{j=1}^{ell-1} (|I_j|-1)
  = a*(ell-a)+1.
```

## Boundary

This is not yet Aoyagi's upper-bound classifier.  It only constructs the finite
codomain that such a classifier should land in.  A future source-backed
classifier still has to prove that every lambda-vector gives either the base
datum or one of these tagged interval values, and that the chosen base value is
the one removed in each interval.

## Nonclaims

- No vector `T_{s,k}` is classified.
- No Case 1(2) uniqueness or back-to-label theorem is proved.
- No supplied branch family is constructed.
- No terminal label, pole order, normal crossings, or RLCT extraction is
  proved.
