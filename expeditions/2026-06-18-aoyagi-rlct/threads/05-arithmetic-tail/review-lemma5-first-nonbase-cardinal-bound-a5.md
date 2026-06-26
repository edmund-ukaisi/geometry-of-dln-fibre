# Review - Lemma 5 first-nonbase cardinal bound

Reviewer: `Kierkegaard the 2nd` (xhigh).
Status: passed; no findings.

## Scope

Reviewed the uncommitted Lean theorem

```text
aoyagiLemma5FirstInteriorNonbaseCountDatumOrBase_candidates_card_le
```

in `lean/DLNFibre/DLN/Aoyagi/Lemma5SuppliedFamily.lean`, together with the
relevant A5 thread context.

## Findings

No issues found.

The theorem is a conditional finite-cardinality wrapper, not a source-backed
Lemma 5 theorem.  Its statement keeps the moving assumptions explicit:
terminal chain endpoints and binary prefix deltas, base-value interval
membership, and injectivity of the deterministic first-nonbase-or-base
classifier.

The proof only builds an `AoyagiLemma5CountDatumClassifier` and delegates to
the existing cardinal squeeze.  The name and docstring are acceptable because
the displayed upper count is immediately qualified by explicit injectivity and
finite-bookkeeping caveats.

## Residual Boundaries

- Construction of the candidate terminal chains `H`.
- Proof of the binary-prefix-delta hypotheses from Aoyagi's vectors.
- Base-branch and base-value realisation.
- Injectivity of this classifier.
- No-extra terminal-minimum coverage.
- Counted-datum back-to-label data.
