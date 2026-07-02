# Review - A2 with-following original-volume readback from reverse raw-source domination

Date: 2026-07-02.

Reviewer: `Lorentz the 2nd` (xhigh, read-only).

## Finding

No issues found.

## Checks

- The formal-product theorem uses the p.13 two-stage measure equality
  `rawChart o rawMap = sourceChart` and the supplied reverse domination
  hypothesis.  It does not assume exact raw-Haar pushforward from the
  with-following theta chart.
- The original-volume bridge applies the inverse Haar scalar through the
  existing positive-scalar p.13 helper.  The scalar direction is correct:
  `formalProduct <= D • sourceRef` gives
  `originalVolume <= (cHaar^-1 * D) • sourceRef`.
- The readback theorem keeps the shrink chain `V subset V0 subset G` and
  requires `chartPiece subset sourceChart '' V`; p.13 support is derived from
  this image containment.
- The reproduction, statement card, synthesis, and priorities entries frame the
  result as a conditional consumer bridge.  They do not claim
  determinant-Haar transport, source-density positivity, or RLCT extraction.

## Residual risk

This was a line-level mathematical/formalisation review of the requested files.
The controller separately ran the Lean build, no-sorry audit, marker scan,
whitespace check, and direct axiom probe.
