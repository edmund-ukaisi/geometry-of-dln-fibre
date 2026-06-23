# Review - Lemma 5 Terminal Order Classifier Notation

Date: 2026-06-23.

Reviewer: Beauvoir, xhigh effort.

Verdict: pass.

No required fixes were found.  The four new Lean wrappers in
`Lemma5TerminalOrderBridge.lean` are only
`simpa [AoyagiDefinition3CeilData.theorem2OrderFormula]` rewrites of existing
supplied A5 facts.  The theorem names in the statement card match the Lean
declarations.

The classifier, counted-datum classifier, back-to-label bridge, and
branch-label injectivity all remain explicit supplied inputs.  The
exact-count variants still require `hinj`.

Source fidelity passes: the reproduction and statement card treat Aoyagi
Lemma 5's `a(ell-a)+1` count as source motivation while preserving the
expedition boundary that the PDF does not by itself supply Lean-level
classifier, injectivity, back-to-label, or no-extra coverage.

