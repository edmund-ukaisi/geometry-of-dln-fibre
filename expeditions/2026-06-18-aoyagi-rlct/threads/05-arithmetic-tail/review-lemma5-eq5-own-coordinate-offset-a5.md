# Review - Lemma 5 equation (5) own-coordinate offset

Reviewer: `Zeno` (xhigh).  Verdict: no findings.

## Scope

Reviewed the supplied equation `(5)` own-coordinate offset slice:

```text
AoyagiLemma5Eq5OwnCoordinateBranch
aoyagiLemma5Eq5OffsetValueSet
aoyagiLemma5Eq5_offsetValue_injective
aoyagiLemma5Eq5OffsetValueSet_card
aoyagiLemma5Eq5OffsetValueSet_subset_intervalValueSetNat
aoyagiLemma5Eq5_ownCoordinate_value
aoyagiLemma5Eq5_ownCoordinate_eq_label_pred
aoyagiLemma5Eq5_ownCoordinate_mem_intervalValueSetNat
aoyagiLemma5Eq5_ownCoordinate_mem_offsetValueSet
```

and the reproduction/statement-card documents.

## Source Fidelity

The source translation is sound.  In Aoyagi PDF p. 27, equation `(5)`, paper
`j0` is Lean coordinate `p`, and `C.block p s` is the own block corresponding
to paper block `j=j0+1`.  Substituting this into the displayed fourth branch
gives `Htilde'_p-alpha`.

The Lean hypotheses keep the guards explicit:

```text
1 <= alpha,
alpha < p,
alpha <= Htilde'_p-Htilde_p.
```

They do not claim source-label legality for `k`.

## Lean Scope

The statements are narrow and match their names: supplied own-branch data,
value rewrite, same-coordinate interval membership, and finite offset count.
No construction or global classification is implied.

## Checks

The reviewer ran:

```text
cd lean && lake env lean DLNFibre/DLN/Aoyagi/Lemma5DisplayedVector.lean
rg 'sorry|axiom|native_decide|#exit' lean/DLNFibre/DLN/Aoyagi/Lemma5DisplayedVector.lean
```

The focused Lean check passed, and the forbidden-token scan found no matches.
The reviewer also checked the new Eq(5) docs for trailing whitespace; no
matches were found.

## Residual Risks

The following remain correctly outside the theorem:

- construction or existence of equation `(5)`'s displayed vector;
- source-label legality for `k`;
- full selected-span equation `(5)` classifier;
- terminal `tilde t=0`;
- Case 1(2) chart sequence;
- Lemma 5 order count;
- normal crossings or RLCT extraction.
