# Review - A4 Case 2 Source Suffix Chain

Status: passed xhigh source/math and Lean/API review.

## Source/Math Review

No high or medium fidelity issues were found.

- The product orientation matches Aoyagi's paper-order product:
  `paperMatrixChainStep` extends by right multiplication `rec * C p`.
- The source endpoint convention is correct: source layer `s` maps to
  zero-based vertex `s-1`, and `sourceSuffixProduct` starts at source layer
  `S+2` and ends at layer `L+1`.
- The empty suffix case is represented by the raw chain identity when
  `S+1=L`, although no source-level simp lemma is currently exported for this
  propositional endpoint equality.
- No actual-width/prefix-minimum confusion was found. The suffix chain is
  width-agnostic through `κ`; the stopped Case 2 hypothesis remains the
  existing prefix-minimum continuation boundary.
- The terminal theorem only instantiates the already supplied suffix parameter
  with `sourceSuffixProduct`.

## Lean/API Review

No blocking Lean/API issues were found.

- The theorem names match the content.
- `paperMatrixChain_succ_right` exposes the intended right-multiplication
  recursion.
- The endpoint-order proof irrelevance theorem is explicit and usable.
- Imports do not create a cycle: the new matrix-chain module imports Mathlib
  only, and `BlowupArithmetic.lean` imports the new module.

## Residual Risk

`sourceSuffixProduct` is intentionally thin. Downstream work may need
source-level peel or empty-suffix simp lemmas to avoid unfolding the generic
chain and normalizing one-based endpoint arithmetic. Those lemmas are not
needed for the current supplied-suffix terminal specialization.
