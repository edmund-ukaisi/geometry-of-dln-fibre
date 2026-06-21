# Review - Lemma 5 Eq5 One-Step Introduced Domain Cardinality

Reviewers: controller review; Ohm the 2nd exact-diff xhigh review.
Verdict: xhigh PASS.  The finite-domain cardinality wrapper is source-safe.

## Findings

No issue was found in the controller check or exact-diff xhigh review.

The wrapper uses only:

```text
introducedLabelFinset_succ_eq_insert
not_mem_introducedLabelFinset_case2_new_before
Finset.card_insert_of_notMem
aoyagiLemma5Eq5_piecewise_ownBlock_actualWidthLabel_of_lastPoint_widthBound
```

The first three prove the generic one-step cardinality increment.  The last
supplies `actualWidthLabel L n S (J+1)` for the supplied Eq5 branch label
under the explicit width bound.

## Checks

Controller checks:

```text
cd lean && lake build DLNFibre.DLN.Aoyagi.BlowupArithmetic
cd lean && lake build DLNFibre.DLN.Aoyagi.Lemma5SourceLabel
cd lean && scripts/sorries
git diff --check
cd lean && lake build DLNFibre
```

All passed.  The full build emitted only pre-existing Core warnings outside the
Aoyagi files touched by this slice.

Exact-diff xhigh review additionally ran:

```text
cd lean && lake build DLNFibre.DLN.Aoyagi.BlowupArithmetic DLNFibre.DLN.Aoyagi.Lemma5SourceLabel
cd lean && ./scripts/sorries
git diff --check
diff-scoped phrase/source-boundary scans
```

and reported no findings.

## Residual Risks

This is not an exponent certificate, terminal theorem, or Lemma 5 order-count
theorem.  It does not provide least-value data, construct Eq5 vectors, quantify
over all `alpha`, prove chart coverage, normal crossings, or RLCT extraction.
