# Review - A2 passive theta source-image bounded-density pullback

Status: controller review before final build verification.

## Soundness Check

The theorem does not assert domination for an arbitrary external measure.
Instead it assumes either:

```text
sourceImageMeasure =
  (sourceBase.withDensity density).restrict (sourceChart '' V)
```

or the corresponding equality for `externalMeasure.restrict (sourceChart '' V)`,
plus the a.e. bound `density <= c`.  This is the correct boundary: arbitrary
singular external measures can pull back to atoms and need not be dominated by
the theta reference.

## Source Fidelity

Aoyagi's p.13 algebra supports the local chart and readback infrastructure.
The paper's smooth positive prior assumption supports local boundedness once a
coordinate-density identity is available.  It does not by itself identify the
project's external/original source prior with the chart-produced source-image
reference.  The theorem therefore leaves that identity explicit.

## Remaining Boundary

The next non-wrapper target is the actual source-prior density identity or a
local Haar/source-measure transport theorem strong enough to supply it.  The
normal-crossing-to-RLCT extraction remains cited.
