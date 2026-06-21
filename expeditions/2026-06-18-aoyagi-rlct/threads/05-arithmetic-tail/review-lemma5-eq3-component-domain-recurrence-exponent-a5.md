# Review - Lemma 5 Eq3 Component Domain/Recurrence/Exponent

Reviewers: controller review; Pauli the 2nd exact-diff xhigh review.
Verdict: PASS.

## Findings

The wrappers use only:

```text
aoyagiLemma5Eq3_component_actualWidthLabel_of_lastPoint_labelBounds
introducedLabelFinset_succ_eq_insert
introducedLabelFinset_card_succ_eq_succ
IntroducedLabelRecurrenceState.Case2SuppliedPostData.weight_succ_current_eq_new_mul_of_ge
introducedLabel_of_eq_stage_le
IntroducedLabelExponentCertificates.extendDomain_succ_current
```

The p-general actual-width compatibility and label bounds remain explicit
hypotheses.  The wrappers do not derive them from Definition 3.

## Checks

Controller checks:

```text
cd lean && lake env lean DLNFibre/DLN/Aoyagi/Lemma5SourceLabel.lean
cd lean && lake build DLNFibre.DLN.Aoyagi.Lemma5SourceLabel
cd lean && scripts/sorries
git diff --check
cd lean && lake build DLNFibre
```

The full build produced only pre-existing Core warnings in `RankPattern`,
`DeformationExt`, `CThetaQIP`, `CThetaQIPConverse`, and `CThetaValue`.

Pauli the 2nd exact-diff xhigh review passed with no blocking findings.  The
review confirmed that `hwidth` and `hlabelBounds` remain explicit in every new
wrapper, that the exponent wrapper copies supplied `hterminal` and `hleast`
directly into the new label certificate, and that the docs/ledgers do not
derive p-general Eq3 label bounds from Definition 3 or claim chart production,
all-interval/all-branch coverage, order count, normal crossings, or RLCT
extraction.

## Residual Risks

This is domain, recurrence, and exponent-certificate bookkeeping under supplied
bounds.  It does not compute terminal exponents or least values, construct
displayed vectors, prove p-general Eq3 label legality from Definition 3, cover
all intervals or all branches, prove Lemma 5 order count, normal crossings, or
RLCT extraction.
