# Review - A2 product-reduction triangular coordinate chart

Reviewer: Turing the 4th, xhigh-effort subagent.

## Verdict

Pass after minor repairs.

## Findings And Repairs

The initial Lean inverse theorem was algebraically true with only the `A1`
unit hypothesis, because Lean's matrix inverse is total.  For source-facing
determinant-chart use, the reviewer requested that it require the raw
determinant-chart predicate, recording both `C1` and `A1` as determinant-unit
variables.  The theorem now takes `x.detChart`.

The reproduction originally phrased the source chart as if Aoyagi directly
assumed `C1'` and `A1'` regular.  The note now distinguishes Aoyagi's literal
wording, where `C1'` is already regular and the chart assumes `C1' A1'`
regular, from the Lean presentation using the equivalent determinant-domain
data `C1'` and `A1'`.

The reproduction plan originally listed the block-difference wrapper among the
current Lean targets.  It is now marked as a deferred structure-level wrapper
to be built from the existing block identities.

## Source-Fidelity Check

The Lean formulas match the p. 13 triangular variable transformation:

```text
Ctop = C1*A1,
F2   = -A1^(-1)*A2,
F3   = F3old - D*A3*(C1*A1)^(-1),
C    = A4 - A3*A1^(-1)*A2.
```

The passive variables `D`, `A1`, and `A3` are retained.  No inverse of `D` is
used.  The determinant-preservation lemmas are correct and the docs do not
claim analytic chart coverage, regular-suspension construction, normal
crossings, pole order, or RLCT extraction.

## Verification

The reviewer reported that `scripts/lb DLNFibre.DLN.Aoyagi.ProductReduction`
and `git diff --check` passed.  The controller reran the focused build after
the requested repairs.
