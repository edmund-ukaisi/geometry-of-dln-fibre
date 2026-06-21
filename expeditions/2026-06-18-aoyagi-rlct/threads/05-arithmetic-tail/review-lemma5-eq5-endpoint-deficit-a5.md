# Review - Lemma 5 Eq5 endpoint deficit

Reviewer: Mill, xhigh-effort subagent.
Date: 2026-06-21.

## Verdict

No blocking mathematical or source-boundary findings.

## Checks

- `aoyagiLemma5IntervalExcess_eq_self_iff_le_min` is correct: with `a<=ell`,
  the nested minimum defining the interval excess equals `p` exactly when
  `p<=a` and `p<=ell-a`.
- `aoyagiLemma5IntervalExcess_le_pred_of_not_le_min` follows from
  `excess<=p`, `excess!=p`, and `1<=p`.
- `aoyagiLemma5Eq5_intervalCard_eq_offsetCard_add_endpointDeficit` correctly
  combines `interval.card = 1 + excess` with the existing Eq5 offset-card
  formula and the rising-region indicator.
- `aoyagiLemma5Eq5_offsets_endpointDeficit_split` correctly packages the
  existing non-rising erase-upper equality and rising erase-both-endpoints
  equality.  Its docstring keeps this as an obligation split, not a source
  coverage theorem.

## Follow-Up Delta

The reviewer suggested using `endpointDeficit` rather than `endpointDefect` for
the cardinal theorem name, to match the slice language and the set-level split.
The final slice uses:

```text
aoyagiLemma5Eq5_intervalCard_eq_offsetCard_add_endpointDeficit
```

and keeps an alias with the older `endpointDefect` spelling for
discoverability.

The review also noted that the phrase "misses the lower endpoint exactly in
the rising region" can be degenerate when lower and upper endpoints coincide.
The final artifacts phrase this as "one additional lower-endpoint deficit" in
the rising region.

## Boundary

This slice does not construct Eq5 branches, realise endpoints by source
branches, prove source-label legality, prove terminal `tilde t=0`, prove chart
coverage, identify pole order, prove normal crossings, or extract RLCT data.

## Verification

The reviewer ran:

```text
lake env lean DLNFibre/DLN/Aoyagi/Lemma5DisplayedVector.lean
scripts/sorries
git diff --check
```

and all passed.  The controller also ran the focused module build, full
`DLNFibre` build, placeholder scanner, and `git diff --check`.
