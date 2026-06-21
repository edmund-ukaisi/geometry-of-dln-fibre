# Review - Lemma 5 Eq5 alpha-indexed branch source labels

Reviewer: xhigh `Peirce`. Scout: xhigh `Herschel`.

## Verdict

Pass after documentation repair.

## Initial findings

Peirce found no Lean or mathematical proof issue, but flagged two scope
fidelity problems in the first draft:

- the source-label wrapper docstring said the branch alpha image was the whole
  strict Eq5 alpha domain, while the theorem only assumed branchwise alpha
  membership;
- the injectivity wrapper docstring described fixed-source labels, while the
  theorem proved injectivity for a general supplied Sigma-valued branch-label
  map.

Both docstrings were repaired.  The final Lean statements use branchwise
alpha-domain membership and a general `branchLabel : beta -> Sigma ...`.

## Checks

- `lake build DLNFibre.DLN.Aoyagi.Lemma5SourceLabel` passed after the repair.
- `git diff --check` passed during controller verification.
- No new `sorry`, `axiom`, `native_decide`, or `#exit` appears in the touched
  Lean block.

## Residual nonclaims

This slice proves source-label legality and supplied branch-label injectivity
only under explicit branchwise hypotheses.  It does not construct Eq5 branch
records, prove alpha-domain coverage, prove selected-span coverage, construct
displayed vectors, prove terminal exactness, classifier/back-to-label
coverage, pole order, normal crossings, or RLCT extraction.
