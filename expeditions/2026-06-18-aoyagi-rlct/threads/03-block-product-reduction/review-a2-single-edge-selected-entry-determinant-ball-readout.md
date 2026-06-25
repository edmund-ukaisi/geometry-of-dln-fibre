# Review - A2 single-edge selected-entry determinant-ball readout

Date: 2026-06-25.

Reviewer mode: controller review plus xhigh scout `Gibbs`.

## Verdict

Pass at the one-edge determinant-neighborhood boundary.

## Scope Check

The theorem packages three existing facts:

```text
Ctop(0)=I,
det(Ctop(0))=1,
det(Ctop(u)) remains a unit for u in a sufficiently small ball.
```

Inside that ball, the previous pointwise one-edge selected-entry readout
theorems apply.  The result returns regular-coordinate readout, residual
coordinate readout through the supplied `residualCoordEquiv`, and the scalar
selected-entry square-sum identity.

No new source fact is introduced.  The parameter `y` is the selected-entry
coordinate parameter for the one-edge product-coordinate family, and the
radius depends only on the regular-coordinate determinant chart.

Gibbs compared this front with the broader multi-edge selected-entry
residual-factor front.  The determinant-ball theorem is the honest next Lean
slice because it is a direct composition of established local facts.  The
multi-edge front remains important but needs an explicit factor statement of
the form

```text
residualFactorProduct C last 0 = selectedEntryMatrix
```

from displayed Aoyagi residual-factor data; the existing rank obstruction
rules out arbitrary terminal-matrix insertion without compatible intermediate
factors.

## Risks To Keep Explicit

- One-edge only.
- Local near `u=0` only.
- The residual-coordinate equivalence is not constructed.
- No source coverage, source-stratum equality, source-measure transport,
  local lower bound, normal crossings, pole order, or RLCT is proved.

Focused `SelectedEntryOriginalLossLocalMeasure` build passed.  Full
`DLNFibre` build, forbidden-marker scan, and diff check also passed.
