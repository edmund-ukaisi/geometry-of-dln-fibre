# Statement card - A5 Lemma 5 equation (5) own-coordinate offset

## Lean Names

- `DLNFibre.DLN.Aoyagi.AoyagiLemma5Eq5OwnCoordinateBranch`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma5Eq5OffsetValueSet`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma5Eq5_offsetValue_injective`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma5Eq5OffsetValueSet_card`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma5Eq5OffsetValueSet_subset_intervalValueSetNat`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma5Eq5_ownCoordinate_value`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma5Eq5_ownCoordinate_eq_label_pred`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma5Eq5_ownCoordinate_mem_intervalValueSetNat`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma5Eq5_ownCoordinate_mem_offsetValueSet`

## Claim

Lean now records a supplied own-coordinate branch for Aoyagi Lemma 5 equation
`(5)`.  With paper `j0` represented by Lean coordinate `p`, and with `s` in
the selected block `C.block p s`, the supplied branch gives

```text
T(s) = Htilde'_p - alpha.
```

If the source label relation is supplied as

```text
k = Htilde'_p + 1 - alpha,
```

then Lean rewrites the own-coordinate value as

```text
T(s) = k - 1.
```

If `alpha <= Htilde'_p-Htilde_p`, encoded by
`alpha <= aoyagiLemma5IntervalExcess ell a p`, then this value lies in the
same-coordinate interval between the displayed lower and upper `Htilde`
chains.  The finite offset values with
`1 <= alpha <= min(excess(ell,a,p),p-1)` have cardinality
`min(excess(ell,a,p),p-1)`.

## Inputs

- A supplied equation `(5)` own-coordinate branch certificate.
- `a<=ell`.
- Source guards `1<=alpha` and `alpha<p`.
- Same-coordinate interval guard
  `alpha <= aoyagiLemma5IntervalExcess ell a p`.
- For the `k-1` rewrite only, the supplied label relation
  `(k : Z) = Htilde'_p + 1 - alpha`.

## Proves

- Own-coordinate value `T(s)=Htilde'_p-alpha`.
- Own-coordinate value `T(s)=k-1` under the label relation.
- Membership in the Nat-indexed same-coordinate interval value set.
- Membership in the finite offset-value set.
- Injectivity and cardinality of the finite offset-value set.

## Does Not Prove

- Construction or existence of equation `(5)`'s displayed vector.
- Source-label legality for `k`.
- Full equation `(5)` selected-span classification.
- Terminal `tilde t=0`.
- Vector admissibility or source-vector-to-chain correspondence.
- Case 1(2) chart sequence.
- Lemma 5 order count, pole order, normal crossings, or RLCT extraction.

## Source

Aoyagi PDF p. 27, equation `(5)`, together with the displayed `Htilde` chains
from PDF pp. 25-26.

## Review

Initial pen-and-paper scout: `Newton`.
Independent correction/review: `Goodall`.
Final landed review: `review-lemma5-eq5-own-coordinate-offset-a5.md`.
