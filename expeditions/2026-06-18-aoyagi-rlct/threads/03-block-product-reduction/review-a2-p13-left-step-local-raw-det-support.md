# Review - A2 p.13 left-step local raw-det support

Date: 2026-06-26.

Reviewed artifacts:

- `lean/DLNFibre/DLN/Aoyagi/ProductReductionStepRegularDensity.lean`
- `reproduction-a2-p13-left-step-local-raw-det-support.md`
- `statement-card-a2-p13-left-step-local-raw-det-support.md`

## Verdict

No blocking findings.

## Checks

- Lean/API scout `Linnaeus the 2nd` recommended this exact local support
  target after auditing the p.13 raw tuple surface.  The proof uses only the
  existing raw-preimage membership theorem, the actual-left-step equality, and
  the small `Ctop` determinant ball.
- Boundary reviewer `Mill the 2nd` confirmed that current regular-suspension
  and raw-measure interfaces do not overclaim; this slice stays below the same
  line by proving only raw determinant-chart membership.
- Source scout `Hilbert` reconfirmed that Aoyagi does not provide p.13
  raw-Haar/source coverage.  The new theorem does not assert either.

## Boundary Audit

The theorem is local chart-domain support:

```text
u in ball(0,R) -> leftStepRaw(x,u) in rawDetChart
```

The proof depends on the p.13 section facts:

```text
C1 = I,   A1 = Ctop(u),   A3 = 0.
```

It does not identify the section image with the full raw determinant chart and
does not prove a pushforward identity.  The a.e. corollaries only convert
regular-coordinate ball support into the a.e. raw-chart support hypothesis used
by the section-image theorem.

## Verification

Focused build passed:

```text
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre.DLN.Aoyagi.ProductReductionStepRegularDensity
```

The build reports only the existing flexible-tactic warning around the older
raw-preimage algebra proof.  No new style warning remains after shortening the
small-ball a.e. theorem name.
