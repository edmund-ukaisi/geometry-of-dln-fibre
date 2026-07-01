# Review - A2 Case 2 reverse raw-source density lower adapter

Date: 2026-07-01.

Status: post-Lean controller review PASS for statement direction and boundary.

## Checks

- The new generic lemma uses the lower-density direction:
  `epsilon • base.restrict V <= (base.withDensity density).restrict V`.
- The lower bound is a.e. with respect to `base.restrict V`, not the weighted
  measure.
- The scalar cost is the inverse lower bound, so the composed domination pays
  `D * epsilon^{-1}`.
- The concrete theorem keeps the determinant-side reverse domination
  `rawHaar.restrict rawDetChart <= Cdet • Measure.map Y (...)` explicit.
- The concrete theorem separately assumes `Cdet < infinity`,
  `epsilon != 0`, and `epsilon != infinity`, and proves
  `(Cdet * epsilon^{-1}) < infinity`.
- No wording claims that Aoyagi pp. 10-13 prove raw-Haar/source-prior
  transport or source-image coverage.

## Independent Audit

Xhigh read-only reviewer `Darwin` found no blocking formalisation or
mathematical issues.  The only low API note was that the concrete theorem
proves `AEMeasurable rawMap (coordinateSourceMeasure.restrict V)` internally
but does not return it.  This is not needed by the current domination
conclusion; a later consumer can request a package theorem if it needs that
witness exposed.

## Verification

Focused warning-clean elaboration passed for
`RetainedPassiveCase2PassiveThetaRawImageHandoff.lean`.  Focused local Lake
builds passed for `LocalMeasureHandoff` and
`RetainedPassiveCase2PassiveThetaRawImageHandoff`, with only pre-existing
imported warning noise in the latter build.

Full local `lake build DLNFibre`, `scripts/sorries`, `git diff --check`, and
direct theorem axiom audit passed.  The new generic and concrete declarations
report only `[propext, Classical.choice, Quot.sound]`.
