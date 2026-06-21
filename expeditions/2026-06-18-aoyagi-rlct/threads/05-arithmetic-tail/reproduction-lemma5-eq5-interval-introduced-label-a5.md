# Pen-and-paper reproduction - Lemma 5 equation (5) interval and introduced-label wrappers

Status: checked finite-set and source-label wrapper.

This note records two narrow consequences of the already-formalised equation
`(5)` offset arithmetic.  It does not construct Aoyagi's displayed source
vectors.

## Source

Aoyagi Lemma 5 counts same-coordinate intervals

```text
I_p = { H : Htilde_p <= H <= Htilde'_p }.
```

Equation `(5)` uses

```text
alpha = Htilde'_p + 1 - k
```

with strict source guard `1 <= alpha < p`.  In Lean the strict Eq5 offset
values are

```text
Htilde'_p - alpha,
1 <= alpha <= min(excess_p,p-1).
```

where

```text
excess_p = Htilde'_p - Htilde_p
         = min(p, ell-p, a, ell-a).
```

## Lower Endpoint Plus Strict Offsets

In the rising region

```text
1 <= p,  p <= a,  p <= ell-a,
```

and with `a <= ell`, we have `excess_p=p`.  The strict Eq5 offsets therefore
have cardinality

```text
min(excess_p,p-1) = p-1.
```

The lower endpoint is not among these strict offsets: membership would give

```text
Htilde_p = Htilde'_p - alpha,
```

so `alpha=Htilde'_p-Htilde_p=p`, contradicting `alpha<=p-1`.

Thus inserting the lower endpoint into the strict offset set gives cardinality

```text
(p-1)+1 = p = excess_p.
```

Both the lower endpoint and every strict offset value lie in `I_p`, so the
inserted set is a subset of the same-coordinate interval value set.  Since the
full interval has cardinality `excess_p+1`, the inserted set accounts for all
but one same-coordinate interval value.

## Introduced Label Wrapper

For a supplied equation `(5)` piecewise source vector and a source point `S`
in the own block `C.block p S`, Lean already proves

```text
T S = k-1
actualWidthLabel L n S k
```

from:

- Definition 3 selected-width sum and strict selected-width inequalities;
- last selected cutpoint range `C.point ell <= L+1`;
- explicit actual-width lower bound `W_p <= n(S+1)`;
- equation `(5)` offset guards carried by the supplied piecewise certificate.

The same supplied own-branch data proves

```text
T S in I_p.
```

Finally, `actualWidthLabel L n S k` implies

```text
introducedLabel L n S k S k
```

by the post-advance current-layer rule: at state `(S,k)`, label `(S,k)` is
introduced.

## Lean Targets

```text
aoyagiLemma5Eq5_lowerEndpoint_mem_intervalValueSetNat_of_lt
aoyagiLemma5Eq5_insert_lowerEndpoint_offsetValueSet_card_of_le_min
aoyagiLemma5Eq5_insert_lowerEndpoint_offsetValueSet_subset_intervalValueSetNat_of_le_min
aoyagiLemma5Eq5_insertLower_offsetCard_add_one_eq_intervalCard_of_le_min
aoyagiLemma5Eq5_piecewise_ownBlock_intervalValue_introducedLabel_of_lastPoint_widthBound
```

## Nonclaims

- No construction of equation `(5)`'s displayed vector.
- No claim that equation `(3)` or `(4)` realises the remaining interval value.
- No derivation of `W_p<=n(S+1)` from Definition 3 alone.
- No terminal `tilde t=0`, vector admissibility, chart sequence, Lemma 5
  order count, pole order, normal crossings, or RLCT extraction.
