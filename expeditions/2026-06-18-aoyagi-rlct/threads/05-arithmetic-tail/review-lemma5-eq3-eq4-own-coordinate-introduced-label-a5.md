# Review - Lemma 5 equations (3)/(4) own-coordinate introduced labels

Reviewers: controller review and exact-diff reviewer `Avicenna the 2nd`.
Verdict: valid as a conservative API adapter.

## Findings

No issue was found in the controller check.
No issue was found in the exact-diff review.

The new theorems are direct wrappers over the existing actual-label adapters:

```text
T S = k-1
actualWidthLabel L n S k
```

The introduced-label conclusion follows by the generic current-layer
post-advance rule:

```text
introducedLabel_of_eq_stage_le
```

with source equality `S=S` and `k<=k`.

## Source Fidelity

The statements preserve the existing hypotheses.  Equation `(3)` still carries
the explicit one-unit slack, and both equations keep actual-width
compatibility explicit.  The theorem names say `introducedLabel`, not Lemma 5
or order count.

## Checks

Controller check:

```text
lake env lean DLNFibre/DLN/Aoyagi/Lemma5SourceLabel.lean
lake build DLNFibre.DLN.Aoyagi.Lemma5SourceLabel
lake build DLNFibre
scripts/sorries
git diff --check
```

passed before this note was finalised.  The full build emitted only the known
pre-existing Core warnings.

## Residual Risks

These wrappers do not construct the displayed vectors, derive actual-width
compatibility from Definition 3, remove Eq3 slack, prove terminal `tilde t=0`,
prove vector admissibility, chart sequence, normal crossings, or RLCT
extraction.
