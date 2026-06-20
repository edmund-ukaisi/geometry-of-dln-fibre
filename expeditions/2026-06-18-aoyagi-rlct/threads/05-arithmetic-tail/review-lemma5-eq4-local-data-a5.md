# Review - Lemma 5 equation (4) local data

Status: passed.

## Source / Pen-And-Paper Check

Checker: xhigh `Feynman`.

Verdict: the package is correct with the repaired guard `p+1<=a`.

- `S_(p+ell-a+2)` lies in `S_1,...,S_(ell+1)` because
  `p+(ell-a)+2<=ell+1` is equivalent to `p+1<=a` under `a<=ell`.
- The own-coordinate value is correct: under `p<=a` and `p<=ell-a`, the
  `Htilde' - Htilde` gap is `p`, so `Htilde'_p-p=Htilde_p`.
- The label `k=Htilde_p+1` is legal by the Definition 3 selected-width label
  bounds, using `1<=p` and `p<=a`.

The checker also confirmed that there is no Lean zero-based mismatch:
`aoyagiSelectedWidthNat ell m p` is source `W_(p+1)`, and
`aoyagiPrefixSum ... p` is source `P_(p+1)`.

## Lean / API Check

Checker: xhigh `Mendel`.

Verdict: use a small conjunction theorem, not a record.  A record should be
reserved for a later displayed-vector/chart certificate carrying branch
formulas, source-vector coordinates, terminal `tilde t=0`, and admissibility
or coverage data.

The checker recommended exactly the theorem shape now implemented as

```text
aoyagiLemma5Eq4_localData_of_sourceSelectedInequality
```

## Nonclaims

- No full displayed equation `(4)` vector construction.
- No terminal `tilde t=0`.
- No vector admissibility or source vector-to-chain correspondence.
- No chart-family coverage or Lemma 5 order count.
- No pole-order, normal-crossing, or RLCT extraction claim.
