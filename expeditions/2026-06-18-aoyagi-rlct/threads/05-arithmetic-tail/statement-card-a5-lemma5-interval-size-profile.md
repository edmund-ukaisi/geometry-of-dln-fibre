# Statement Card - A5 Lemma 5 Interval-Size Profile

## Lean Names

- `DLNFibre.DLN.Aoyagi.aoyagiLemma5IntervalSize_eq_succ_of_le_min`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma5IntervalSize_eq_min_succ_of_min_le_of_le_max`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma5IntervalSize_eq_falling_of_max_le`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma5IntervalSize_sourcePiecewise`

## Claim

Aoyagi's interval size

```text
|{H : Htilde_j <= H <= Htilde'_j}|
```

has the three-region profile displayed in Lemma 5:

```text
j+1
min(a,ell-a)+1
min(a,ell-a)+1+max(a,ell-a)-j
```

with the regions determined by `min(a,ell-a)` and `max(a,ell-a)`.

## Inputs

- `a<=ell`.
- For the combined piecewise theorem, `j<=ell`.

## Proves

Only the finite arithmetic profile of `aoyagiLemma5IntervalSize`, which is
already the cardinality of the same-coordinate `Htilde` interval value set.

## Does Not Prove

- Displayed-vector construction or admissibility.
- Realisation of interval values by Eq3/Eq4/Eq5 source families.
- Lemma 5 order count, pole order, normal crossings, or RLCT extraction.

## Source

Aoyagi Lemma 5, PDF pp. 25-26, immediately after the upper-count setup.
