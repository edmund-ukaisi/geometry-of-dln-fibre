# Reproduction - Lemma 5 counted-datum maps-to adapters

Status: reproduced; Lean checked.

## Source

Aoyagi Lemma 5 counts interior same-coordinate values between the two
displayed Htilde chains, with one base value erased at each interior
coordinate.  The existing counted-datum set formalises this codomain as

```text
none
some (j,H) where j in {1,...,ell-1} and
  H in aoyagiHtildeIntervalValueSetNat ell a M m j
  with baseValue(j) erased.
```

This slice isolates the elementary maps-to step into reusable adapters.

## Calculation

Fix an interior coordinate `j` with

```text
j in Finset.Icc 1 (ell-1).
```

If

```text
H in aoyagiHtildeIntervalValueSetNat ell a M m j
H != baseValue j,
```

then `H` belongs to the erased interval

```text
(aoyagiHtildeIntervalValueSetNat ell a M m j).erase (baseValue j).
```

By the already proved membership characterisation
`some_mem_aoyagiLemma5CountDatumSet_iff`, this is exactly

```text
some (Sigma.mk j H) in aoyagiLemma5CountDatumSet ell a M m baseValue.
```

For the bounds variant, the same conclusion follows from

```text
aoyagiHtildeLowerNat ell a M m j <= H
H <= aoyagiHtildeUpperNat ell a M m j.
```

The interior-coordinate hypothesis gives `j < ell+1`, so the natural-indexed
value set unwraps to the finite-indexed value set at `Fin.mk j`.  The Htilde
interval membership theorem then identifies membership with the two displayed
bounds.

## Lean Targets

```text
aoyagiLemma5CountDatumSet_mem_of_intervalValueSetNat
aoyagiLemma5CountDatumSet_mem_of_HtildeBounds
```

## Kill Conditions

- Dropping the interior-coordinate hypothesis loses the source summation range
  and the counted datum coordinate is no longer in the codomain.
- Dropping `H != baseValue j` makes the erased-interval membership false in
  the base-value case.
- Dropping `a <= ell` from the bounds variant loses the theorem identifying
  Htilde interval membership with the two bounds.

## Nonclaims

- No source branch, Eq3/Eq4/Eq5 vector, or terminal chain is constructed.
- No classifier, injection, or back-to-label map is proved.
- No terminal-minimum exactness, order count, pole order, normal crossings, or
  RLCT extraction is proved.
