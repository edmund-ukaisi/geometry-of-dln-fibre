# Review - Lemma 5 Eq3/Eq4 local interval cardinality

Reviewer: xhigh Lean/API reviewer `Zeno`.

Verdict: pass.

## Scope

Reviewed:

- `lean/DLNFibre/DLN/Aoyagi/Lemma5DisplayedVector.lean`
- `reproduction-lemma5-eq3-eq4-local-interval-cardinality-a5.md`
- `statement-card-a5-lemma5-eq3-eq4-local-interval-cardinality.md`

## Findings

No findings.

## Lean/API Notes

The reviewer confirmed that the two added declarations are finite cardinality
wrappers only:

- `aoyagiLemma5_Eq3Upper_Eq4_local_insertComponents_card_eq_intervalSize`;
- `aoyagiLemma5_Eq3Upper_Eq4_local_insertComponents_card_eq_offsetCard_add_two`.

The hypotheses remain local Eq3/Eq4 piecewise certificates plus `1 <= p` and
`p <= ell-a`.  The second wrapper derives `p <= a` only from the Eq4
certificate's `indexGuard`.  The statements do not imply displayed-vector
construction, source-label legality, classifier coverage, Lemma 5 order count,
pole order, normal crossings, or RLCT extraction.

## Verification

Focused Lean check:

```text
lake env lean DLNFibre/DLN/Aoyagi/Lemma5DisplayedVector.lean
```

The reviewer also ran a focused diff whitespace check for the Lean file.
