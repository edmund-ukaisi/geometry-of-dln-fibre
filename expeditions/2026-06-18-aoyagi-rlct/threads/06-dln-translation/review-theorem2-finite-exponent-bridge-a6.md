# Review - A6/A0 Theorem 2 finite exponent bridge

Reviewer: xhigh `Singer`, read-only.  No files edited by the reviewer.

## Verdict

Pass after scope hardening.  The Lean result is acceptable only as a
conditional bridge from explicit finite exponent formula equalities and the A0
extraction hypothesis.  It is not a final Theorem 2 theorem.

## Required changes applied

- Renamed the module to
  `lean/DLNFibre/DLN/Aoyagi/Theorem2FiniteExponentBridge.lean`.
- Renamed the boundary structure to
  `AoyagiTheorem2FiniteExponentFormulaHypothesis`.
- Renamed theorem statements to end in `_of_extractionHypothesis`.
- Used `poleOrder` for the extracted order variable in the new bridge.
- Imported `FinalFormula` instead of `Definition3Bridge`, because the bridge
  uses formula rewrites only.
- Strengthened docstrings and statement-card exclusions to name the missing
  source parameter provenance, Definition 3 source-selection data, rank-width
  hypotheses, chart coverage, unit factors, Jacobian/prior exponent
  correctness, terminal-minimum exactness, and Lemma 5 order count.

## Remaining boundary

The bridge proves only transitivity:

```text
lambda = D.exponentMinimum = displayed lambda,
poleOrder = D.exponentOrder = displayed order.
```

The finite equalities

```text
D.exponentMinimum = displayed lambda,
D.exponentOrder = displayed order
```

remain supplied.  No normal-crossing chart data, no finite exponent/order
equalities, and no analytic RLCT extraction theorem are constructed here.
