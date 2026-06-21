# Review - A5 Lemma 5 Eq4 rising non-strict endpoint split

Review mode: xhigh Lean API scout, xhigh hardener, and controller integration.

## Verdict

Accepted as a dispatcher over existing Eq4/Eq5 endpoint facts.

The mathematical content is the finite split of `not (p+1<a)` under `p<=a`.
The rest is packaging: terminal-collision consequences remain conditional on
a supplied Eq4 certificate, and the `p=a` branch records repaired-guard
failure plus the existing Eq5 endpoint deficit.

## Checks

- The pure split includes the necessary hypothesis `p<=a`.
- The richer payload includes the hypotheses needed by the Eq5 rising
  erased-endpoints theorem: `a<=ell`, `1<=p`, `p<=a`, and `p<=ell-a`.
- The terminal-collision branch does not assert existence of an Eq4
  certificate.
- The `p=a` branch proves nonexistence only for the repaired
  `AoyagiLemma5Eq4PiecewiseSourceVector` shape with the fixed parameters.
- The theorem names avoid coverage, construction, exactness, pole order, and
  RLCT language.

## Residual Risk

Future uses must not merge `p+1=a` with `p=a`.  The first is guard-success
terminal collision; the second is repaired-guard failure.  Neither branch
proves a source-backed Lemma 5 chart-family construction.
