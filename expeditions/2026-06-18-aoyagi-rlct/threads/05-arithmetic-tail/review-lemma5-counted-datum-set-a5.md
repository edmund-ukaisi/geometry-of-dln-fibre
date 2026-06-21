# Review - Lemma 5 Counted Datum Set

Reviewer: Kant, xhigh effort.

Status: passed after wording correction.

## Scope

Reviewed:

- `reproduction-lemma5-counted-datum-set-a5.md`
- `statement-card-a5-lemma5-counted-datum-set.md`
- the counted-datum additions in
  `lean/DLNFibre/DLN/Aoyagi/Lemma5SuppliedFamily.lean`

The review checked finite-count correctness, the erased-base-value boundary,
source-boundary wording, and overclaim risk.

## Findings

The finite count is mathematically sound.  The set has cardinality

```text
1 + sum_j (|I_j| - 1),
```

with disjointness enforced by the `Option` and coordinate tags, and the proof
correctly reuses `aoyagiHtildeIntervalValueSetNat_excess_sum_Icc`.

Two wording issues were found:

1. The reproduction note initially said Aoyagi's paragraph counts one base
   vector plus nonbase interval values.  The PDF motivates the interval
   upper-count shape, but the explicit one-base/erased-value codomain is the
   Lean supplied model.
2. The Lean comment for `none` initially called it the supplied base branch,
   although this slice only defines a counted datum standing for that branch.

Both were corrected.

## Verdict

No remaining mathematical or source-boundary issue found.  The slice counts
only the interval codomain and does not claim source classification, branch
construction, terminal-label exactness, pole order, normal crossings, or RLCT
extraction.
