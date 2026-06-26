# Review - A2 product-step raw-order inverse-density pushforward

Date: 2026-06-26.

Reviewer: xhigh read-only reviewer `Laplace the 2nd`.

## Verdict

Pass.  No blockers found.

The new theorem has the intended orientation: from the already-landed weighted
change-of-variables identity and pointwise cancellation, it proves

```text
Phi_* (m|s) = (m|s) with density K,
```

where `Phi` is the raw-order product-step coordinate map, `s` is the raw
determinant chart, and `K` is the chart-side reciprocal Jacobian density.

## Checks

- The local helper `map_withDensity_comp_of_aemeasurable` only assumes
  a.e.-measurability of `f` and of `g` with respect to the pushforward.  It
  does not require injectivity, a measurable embedding, or an inverse map.
- The determinant-chart cancellation lemmas use the existing raw/chart inverse
  formulas and determinant-chart hypotheses for `C1`, `A1`, and `Ctop`.
- No hidden invertibility of the passive `D` block is introduced.
- The theorem does not assert original DLN source/prior transport, p. 13
  source coverage, signed-box density identification, regular suspension,
  normal crossings, pole order, or RLCT.

## Polish Applied

- Updated the reproduction status from in-progress to proved and reviewed.
- Reworded the pen-and-paper pushforward step from "measurable embedding" to
  "a.e.-measurable map", matching the Lean helper.
- Made the statement-card input list explicit about the decidable equality
  instances used by the Lean statement.

## Verification

The reviewer ran read-only checks:

```text
lake env lean DLNFibre/DLN/Aoyagi/ProductReductionStepMeasure.lean
git diff --check
```

Both passed.  The reviewer also found no `sorry`, `axiom`, `native_decide`, or
`#exit` markers in the touched Lean/docs files.
