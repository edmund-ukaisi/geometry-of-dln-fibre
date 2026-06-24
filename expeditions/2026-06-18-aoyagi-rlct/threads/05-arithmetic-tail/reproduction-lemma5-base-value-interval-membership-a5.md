# Reproduction - A5 Lemma 5 base-value interval membership

Date: 2026-06-24.

Status: reproduced before Lean implementation.

## Source Anchor

Aoyagi Lemma 5 counts values between two displayed chains, written in the
paper as `\tilde H` and `\tilde H'`, after removing the base branch value in
each interior coordinate.  The existing Lean counted-datum set already assumes
that the supplied base value at every interior coordinate belongs to the
corresponding finite interval.

This note proves a small replacement for that naked assumption: if a supplied
base chain lies between the two displayed chains and its interior coordinates
are the supplied `baseValue`, then those `baseValue` entries lie in the
Nat-indexed interval value sets.

## Calculation

Let

```text
baseH : Fin (ell+1) -> Int
baseValue : Nat -> Int
```

and assume the componentwise chain bounds

```text
HtildeLowerChain <= baseH <= HtildeUpperChain.
```

The already formalized chain-bound lemma says that for every finite coordinate
`q : Fin (ell+1)`,

```text
baseH(q) in aoyagiHtildeIntervalValueSet ell a M m q.
```

For an interior natural coordinate

```text
j in {1,...,ell-1},
```

the Lean coordinate

```text
aoyagiLemma5InteriorCoord ell j hj : Fin (ell+1)
```

has value `j`.  If the supplied base-coordinate equality says

```text
baseH(aoyagiLemma5InteriorCoord ell j hj) = baseValue j,
```

then the previous finite-coordinate interval membership rewrites to

```text
baseValue j in aoyagiHtildeIntervalValueSetNat ell a M m j.
```

The Nat-indexed value set is just the finite-coordinate value set at
`<j, j < ell+1>` because the interior-coordinate hypothesis implies
`j < ell+1`.

## Lean Target

Add:

```text
aoyagiLemma5BaseValue_mem_intervalValueSetNat_of_baseChainBounds
```

in `Lemma5SuppliedFamily.lean`.

## Boundary

- The base chain `baseH` is supplied.
- The coordinate equality between `baseH` and `baseValue` is supplied.
- This does not construct Aoyagi's printed Eq3/Eq4/Eq5 branch family.
- This does not prove source-label legality, no-extra coverage, injectivity,
  back-to-label coverage, terminal exactness, pole order, normal crossings, or
  RLCT extraction.

## Kill Conditions

- Do not use this theorem to claim that the base branch exists from the printed
  equations.
- Do not drop the coordinate equality hypothesis between `baseH` and
  `baseValue`.
- Do not treat interval membership of the erased base values as a full Lemma 5
  classifier.
