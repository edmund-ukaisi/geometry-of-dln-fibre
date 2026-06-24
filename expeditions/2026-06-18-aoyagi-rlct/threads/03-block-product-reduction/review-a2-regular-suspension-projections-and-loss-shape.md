# Review - A2 regular-suspension projections and source loss shape

Date: 2026-06-24.

Reviewer: xhigh `Tesla the 4th`.

Verdict: accepted.

## Checked Artifacts

- `lean/DLNFibre/DLN/Aoyagi/RegularSuspensionInterface.lean`
- `lean/DLNFibre/DLN/Aoyagi/RegularSuspensionCoordinates.lean`
- `reproduction-a2-supplied-regular-suspension-extraction-projection.md`
- `statement-card-a2-supplied-regular-suspension-extraction-projection.md`
- `reproduction-a2-source-stratum-literal-regular-residual-square-sum.md`
- `statement-card-a2-source-stratum-literal-regular-residual-square-sum.md`
- `reproduction-a2-regular-square-suspension-integrability-target.md`
- expedition ledger edits for the same slice

## Verdict

No required edits.

The projection theorems in `RegularSuspensionInterface.lean` are projections
from `Cfull.ExtractionHypothesis lambda poleOrder` through the supplied finite
equality

```text
Cfull.exponentData =
  Cred.exponentData.jacobianPriorLossShift regularCount.
```

They do not construct `Cfull`, extract from `Cred`, or invoke a Fubini/polar
or Aoyagi regular-coordinate additivity result.

The coordinate theorem in `RegularSuspensionCoordinates.lean` composes the
existing source-stratum literal/cleaned factor-`2` comparison with the existing
cleaned square-sum split into regular plus residual pieces.  It stays finite
and source-side.

The docs and ledger edits are policy-faithful: extraction remains on `Cfull`,
the regular-suspension construction remains supplied/open, and no Aoyagi
Lemma 1, Theorem 4, Fubini/polar shift, normal-crossing production, pole
order, or RLCT equality is claimed.  The integrability-target note is framed
as a future target, not a completed theorem.

## Reviewer Checks

```text
lake env lean DLNFibre/DLN/Aoyagi/RegularSuspensionInterface.lean
lake env lean DLNFibre/DLN/Aoyagi/RegularSuspensionCoordinates.lean
git diff --check
```

All passed in the review workspace.
