# Reproduction - A6 Definition 3 general `L`, `ell=1` selected-pair formula package

Date: 2026-06-24.

Status: pen-and-paper reproduction before Lean implementation.

## Question

The existing selected-pair formula package was first proved for `L = 2`
because it was introduced while diagnosing the three-source-width branch
overlaps.  The actual `ell = 1` arithmetic does not depend on `L = 2`.

The safe general theorem should therefore keep the selected pair supplied:

```text
C : AoyagiSelectedCutpoints 1
```

and assume that its two selected values `u` and `v` are positive and cover the
source-range reduced-width values by value.  It should not choose a canonical
selected pair.

## Source Anchor

Aoyagi PDF pp. 8-9 define Definition 3 source data and Theorem 2 from an
already chosen `ell` and selected cutpoints.  For `ell = 1`, there are exactly
two selected widths:

```text
m_0 = u,
m_1 = v.
```

The local source-data constructor

```text
of_ell_eq_one_selectedValueSet_covers
```

already works for arbitrary `L`.  Its hypotheses are:

- every selected cutpoint lies in the source range `1 <= s <= L + 1`;
- the two selected reduced widths are positive;
- every source-range reduced width belongs to the selected value set.

The nonselected clauses in Definition 3 are then vacuous because the supplied
cover is by value, exactly matching the source definition's selected value set.

## Ceiling Datum

For `ell = 1`, the selected sum is

```text
sum_j m_j = u + v.
```

Since `u` and `v` are positive natural numbers, `0 < u + v`.  Use the
positive-remainder constructor with

```text
ceilPred = u + v - 1,
a = 1.
```

Then

```text
u + v = 1 * (u + v - 1) + 1,
ceilWidth = (u + v - 1) + 1 = u + v,
aParam = 1.
```

The Theorem 2 order formula is

```text
aParam * (ell - aParam) + 1 = 1 * (1 - 1) + 1 = 1.
```

## Rank-Width Provenance

The theorem should keep the source-range rank-width hypothesis

```text
forall s, 1 <= s -> s <= L + 1 -> r <= H s.
```

This converts selected integer reduced widths into natural subtractions:

```text
m_j = ((H (C.cut j) - r : Nat) : Int)
```

using the selected cutpoint positivity and source-range bound.  It also gives
nonnegativity of the selected width family and its natural-indexed accessor.

## Pair Sum and Lambda

For `ell = 1`, the pair sum has one contributing pair:

```text
aoyagiSelectedWidthPairSum 1 m = u * v.
```

The Theorem 2 lambda expression is

```text
aoyagiTheorem2Lambda_fromCeilData L 1 H r m data
  = aoyagiTheorem2RegularTerm L H r
      + a*(1-a)/(4*1)
      - (1*(1-1)/4) * (...)
      + pairSum/2.
```

With `a = 1`, both finite correction terms vanish:

```text
a*(1-a)/(4*1) = 0,
1*(1-1)/4 = 0.
```

Therefore

```text
aoyagiTheorem2Lambda_fromCeilData L 1 H r m data
  = aoyagiTheorem2RegularTerm L H r + u*v/2.
```

The only remaining `L`-dependence is the regular term and the source-range
guards.

## Guardrails

This slice must not:

- claim a canonical selected pair;
- claim branch-independent finite lambda or order data for arbitrary
  Definition 3 source-data choices;
- use the `L = 2` repeated-positive branch theorem as source evidence;
- add source-rank or final-socket wrappers;
- construct Eq5 payloads, charts, normal crossings, pole order, or RLCT.
