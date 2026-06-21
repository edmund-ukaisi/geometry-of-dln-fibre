# Reproduction - Lemma 5 Eq5 Strict-Offset Rising Count

Status: checked finite count wrapper.

This note records the rising-region specialization of the equation `(5)`
strict-offset cardinality.  It is a named count-side API extracted from the
already-formalised offset/excess decomposition.

## Source

Aoyagi Lemma 5, PDF pp. 26-27, uses equation `(5)` with

```text
alpha = Htilde'_p + 1 - k
```

and strict offset guard `1 <= alpha < p`.  The corresponding Lean finite set
is `aoyagiLemma5Eq5OffsetValueSet ell a p M m`.

## Reproduction

The existing Lean count theorem says:

```text
card(aoyagiLemma5Eq5OffsetValueSet ell a p M m)
  = min(e_p, p-1),
```

where

```text
e_p = aoyagiLemma5IntervalExcess ell a p.
```

In the rising region, assume:

```text
a <= ell,  1 <= p,  p <= a,  p <= ell-a.
```

The interval-excess arithmetic gives:

```text
e_p = p.
```

Therefore:

```text
card(aoyagiLemma5Eq5OffsetValueSet ell a p M m)
  = min(p,p-1)
  = p-1.
```

This matches the source guard `1 <= alpha < p`: the strict offsets contribute
exactly `p-1` counted values in the rising region.

## Lean Target

```text
aoyagiLemma5Eq5OffsetValueSet_card_eq_pred_of_le_min
```

## Kill Conditions

- Do not treat this as construction of equation `(5)` displayed vectors.
- Do not infer source-label legality or actual-width dominance.
- Do not infer endpoint realisation by equation `(3)` or `(4)`.
- Do not infer all-coordinate coverage, all-branch packaging, Lemma 5 order
  count, normal crossings, or RLCT extraction.
