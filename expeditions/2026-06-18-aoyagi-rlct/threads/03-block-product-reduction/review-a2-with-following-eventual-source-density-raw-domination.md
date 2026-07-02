# Review - A2 with-following eventual source-density raw domination

Date: 2026-07-02.

Reviewer: xhigh read-only reviewer `Kuhn the 2nd`.

## Verdict

No findings.

## Checks

The Lean theorem is scoped correctly.  It assumes only the eventual lower bound
near the base point and converts it internally to the a.e. lower bound consumed
by the existing lower-density raw-domination theorem.  It does not prove
continuity, positivity, or identify `sourceImageDensity`; `eps != 0` and
`eps != infinity` remain caller hypotheses.

The shrink is correct.  The proof extracts an open lower-bound neighborhood
`H` from `eventually_nhds_iff`, applies the previous lower-density theorem on
`G inter H`, returns the resulting `V` with `V subset G`, and uses
`V subset H` plus `ae_restrict_mem` to prove the a.e. lower bound.

The determinant-side reverse domination is preserved as a hypothesis on the
returned `V`, and is passed unchanged into the previous lower-density theorem.

The reproduction note and statement card match the theorem and its nonclaims.

## Residual risk

The only residual risk is normal brittleness from the large `let`-bound
`simpa` block used to call the previous theorem.  Current definitions and the
subset projections elaborate cleanly.
