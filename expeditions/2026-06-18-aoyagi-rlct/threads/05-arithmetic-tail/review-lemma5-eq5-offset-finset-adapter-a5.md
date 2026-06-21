# Review - Lemma 5 Eq5 offset finset adapter

Reviewers: controller review; exact-diff reviewer pending.
Verdict before exact-diff return: adapter is source-safe.

## Findings

No issue was found in the controller check.

The theorem combines:

```text
aoyagiLemma5Eq5_ownCoordinate_mem_offsetValueSet
aoyagiLemma5Eq5_ownBlock_intervalValue_mem_introducedLabelFinset_of_lastPoint_widthBound
```

The first theorem uses the supplied Eq5 guards on the fixed `alpha`; the second
theorem supplies interval membership, `T S=k-1`, and introduced-label finite
domain membership.  No new source hypothesis is weakened.

## Checks

Controller check:

```text
cd lean && lake env lean DLNFibre/DLN/Aoyagi/Lemma5SourceLabel.lean
```

passed before this note was written.

## Residual Risks

This is one fixed supplied branch, not an all-offset construction.  It does
not prove displayed-vector construction, terminal `tilde t=0`, vector
admissibility, chart sequence, normal crossings, RLCT extraction, or Lemma 5
order count.
