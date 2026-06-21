# Review - Lemma 5 Eq5 non-rising coverage

Reviewer: Curie, xhigh-effort subagent.
Date: 2026-06-21.

## Verdict

No mathematical or Lean correctness blockers.

The only review finding was a documentation hygiene issue: the ledgers already
referenced this review artifact before it existed.  This file resolves that
gap.

## Checks

- `aoyagiLemma5Eq5_offsets_eq_interval_erase_upper_of_excess_le_pred` has the
  right finite-set proof shape: show the Eq5 offset set is contained in the
  interval with the upper endpoint erased, then compare cardinalities.
- The cardinality argument is sound.  The interval has size `1 + excess`; the
  upper endpoint is present, so erasing it leaves `excess`.  The Eq5 offset set
  has size `min excess (p-1)`, which is `excess` under the non-rising
  hypothesis `excess <= p-1`.
- The hypotheses are appropriate.  `a <= ell` and `p < ell+1` are needed for
  the Nat-indexed interval wrapper; `excess <= p-1` is exactly the
  non-rising finite condition.
- The Eq3 plateau wrapper is conditional on supplied Eq3-shaped data and does
  not claim source-label legality, terminality, chart coverage, or order
  count.

## Follow-Up Delta

The reviewer noted that the plateau wrapper name could include `Component` to
parallel the existing rising-region name.  The final slice keeps the original
name and adds the alias:

```text
aoyagiLemma5_suppliedEq3UpperComponent_Eq5_offsets_eq_intervalValueSetNat_of_plateau
```

## Boundary

This slice does not construct equation `(3)` or `(5)` source vectors, prove
source-label legality, prove terminal `tilde t=0`, prove chart coverage,
construct an all-coordinate branch family, identify pole order, prove normal
crossings, or extract RLCT data.

## Verification

The reviewer ran:

```text
lake env lean DLNFibre/DLN/Aoyagi/Lemma5DisplayedVector.lean
git diff --check
```

and both passed.  The controller also ran the focused module build, full
`DLNFibre` build, placeholder scanner, and `git diff --check`.
