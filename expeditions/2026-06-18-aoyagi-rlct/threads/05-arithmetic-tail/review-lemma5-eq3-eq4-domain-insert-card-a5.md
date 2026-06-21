# Review - Lemma 5 Eq3/Eq4 One-Step Domain Insert and Cardinality

Reviewers: controller review; James the 2nd exact-diff xhigh review.
Verdict: xhigh PASS.  The finite-domain wrappers are source-safe.

## Findings

No issue was found in the controller check or exact-diff xhigh review.

The wrappers use only:

```text
aoyagiLemma5Eq4_piecewise_ownCoordinate_actualWidthLabel_of_lastPoint
aoyagiLemma5Eq3_piecewise_ownCoordinate_actualWidthLabel_of_lastPoint
introducedLabelFinset_succ_eq_insert
introducedLabelFinset_card_succ_eq_succ
```

The Eq4 wrapper preserves the repaired Eq4 guards and actual-width
compatibility.  The Eq3 wrapper preserves the explicit one-unit slack and
actual-width compatibility.

## Checks

Controller checks:

```text
cd lean && lake env lean DLNFibre/DLN/Aoyagi/Lemma5SourceLabel.lean
cd lean && lake build DLNFibre.DLN.Aoyagi.Lemma5SourceLabel
cd lean && scripts/sorries
git diff --check
cd lean && lake build DLNFibre
```

All passed.  The full build emitted only pre-existing Core warnings outside the
Aoyagi files touched by this slice.

Exact-diff xhigh review additionally ran:

```text
cd lean && lake env lean DLNFibre/DLN/Aoyagi/Lemma5SourceLabel.lean
git diff --check
rg -n "sorry|axiom|native_decide|#exit" lean/DLNFibre/DLN/Aoyagi/Lemma5SourceLabel.lean lean/DLNFibre/DLN/Aoyagi
```

and reported no findings.

## Residual Risks

These are not displayed-vector construction, exponent-certificate, terminal,
or Lemma 5 order-count theorems.  They do not provide least-value data, chart
coverage, normal crossings, or RLCT extraction.
