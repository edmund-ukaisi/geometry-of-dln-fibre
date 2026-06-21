# Review - Lemma 5 Printed Equations And Lemma 4 Obstructions

Reviewers: controller review; equation-specific xhigh passes by Pascal the
2nd, Hegel the 2nd, and Leibniz the 2nd; Franklin the 2nd final
source-fidelity xhigh review.

Verdict: PASS.

## Findings

The checkpoint records obstructions, not a replacement proof of Lemma 5.  It
keeps the conclusion narrow: equations `(3)`, `(4)`, and `(5)` cannot be used
as complete Lemma 4 witnesses in their printed form.

The Lean addition is conditional and finite:

```text
aoyagiLemma5Eq5_piecewise_belowLowerCounterexample_allWidthsFour
aoyagiLemma5Eq5_piecewise_not_lowerBounded_allWidthsFour
```

It assumes a supplied Eq5 piecewise certificate and proves that a concrete
branch value lies below the lower chain.  It does not construct a displayed
source vector or prove source-label existence.

## Checks

Controller checks completed so far:

```text
pdftotext -layout -f 8 -l 9 paper-sources/aoyagi-2023-consideration-of-learning-efficiency-of-dln/aoyagi-2023-neural-networks-preprint.pdf -
pdftotext -layout -f 15 -l 19 paper-sources/aoyagi-2023-consideration-of-learning-efficiency-of-dln/aoyagi-2023-neural-networks-preprint.pdf -
pdftotext -layout -f 25 -l 27 paper-sources/aoyagi-2023-consideration-of-learning-efficiency-of-dln/aoyagi-2023-neural-networks-preprint.pdf -
lake build DLNFibre.DLN.Aoyagi.Lemma5DisplayedVector
```

The Lake command above is run from `lean/`.  Franklin the 2nd independently
checked the diff against Aoyagi PDF pp. 8-9, 15-19, and 22-27; reran the
focused module build, `scripts/sorries`, full `lake build DLNFibre`, and
`git diff --check`; and found no blocking source-fidelity or theorem-boundary
issues.  Full build warnings were pre-existing linter warnings.

## Residual Risks

The note does not construct a corrected branch family.  It also does not prove
that no corrected reading of Aoyagi's proof exists.  The next mathematical
work must either search for a corrected chart-family formula or keep Lemma 5's
displayed-family realisation behind supplied data.
