# Thread 02 - analytic interface

Type: explore/formalisation. Status: closed.

## Task

Specify the cited normal-crossing-to-RLCT extraction interface and decide what
parts of Aoyagi's use of RLCT background are genuinely analytic.

## Output contract

- A precise interface with inputs, outputs, and naming that cannot be confused
  with a proved analytic theorem.
- A verdict on Aoyagi Theorem 4: prove by elementary reduction if possible;
  cite only after a real probe.
- Candidate Lean statement shape, including all assumptions.

## Controller notes

The operator has allowed the normal-crossing extraction theorem to remain Cited.
Do not expand the cited boundary without evidence.

## 2026-06-18 controller draft

Scout `Boole` returned and the controller extracted a draft cited-interface
shape at `interface-draft.md`. This remains a draft until A4 supplies the exact
normal-crossing certificate data. It explicitly excludes Aoyagi Lemma 1 and
Theorem 4 from the allowed citation boundary.

## 2026-06-18 A2 interface repair

Reopened the analytic boundary after the A2 chart-local induction step landed.
Xhigh scouts `Hypatia` and `Kepler` independently checked the post-Theorem-3
passage on PDF p. 13. Controller decision: keep A0 as a concrete
normal-crossing extraction boundary, not as a broad analytic-ideal invariance
package.

Repair note: `interface-repair-a2.md`.

Consequences:

- Aoyagi Lemma 1 remains outside A0 as a general RLCT generator-comparison
  theorem.
- Regular-coordinate additivity after Theorem 3 is not cited separately.
- The preferred route is to prove elementary matrix-entry ideal algebra and to
  build the regular variables into a full normal-crossing certificate, so the
  `c/2` shift is finite certificate arithmetic before the single extraction
  citation.

## 2026-06-22 finite exponent interface

Lean now contains the exponent-only interface
`lean/DLNFibre/DLN/Aoyagi/NormalCrossingInterface.lean`, imported by
`lean/DLNFibre.lean`.

This module records only the finite formula after a normal-crossing chart
certificate has been supplied:

- active coordinates have `k > 0`;
- `exponentMinimum` is the minimum of `(h+1)/(2*k)` over active chart
  coordinates;
- `exponentOrder` is the maximum, over charts, of the number of active
  coordinates attaining the global minimum;
- `AoyagiNormalCrossingExtractionHypothesis` is the explicit cited-boundary
  hypothesis equating external `lambda, theta` with those finite values.

Artifacts:

- `reproduction-normal-crossing-exponent-interface-a0.md`;
- `statement-card-a0-normal-crossing-exponent-interface.md`;
- `review-normal-crossing-exponent-interface-a0.md`.

Nonclaims remain unchanged: no analytic theorem, chart production,
nonvanishing units, Aoyagi Lemma 1, regular-coordinate additivity, Theorem 4,
pole-order theorem, or RLCT theorem is proved by this module.
