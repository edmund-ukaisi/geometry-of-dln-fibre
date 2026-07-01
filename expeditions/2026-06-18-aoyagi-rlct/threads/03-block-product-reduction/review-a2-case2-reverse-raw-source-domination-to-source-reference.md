# Review - A2 Case 2 reverse raw-source domination to source reference

Date: 2026-07-01.

Status: post-Lean controller review PASS for statement direction, boundary,
and verification.

## Checks

- The hypothesis has the useful reverse direction:
  `rawHaar.restrict rawSourceSet <= D • rawMap_*(thetaReference|V)`.
- Mapping through `rawChart` is legitimate because the raw image is supported
  in `rawSourceSet` and the p.13 raw-order source chart is a.e. measurable on
  raw-source restrictions.
- The formal-product conclusion is exactly the input expected by the previous
  original-volume/source-image bridge.
- The original-volume theorem adds only the p.13 inverse Haar scalar and
  requires `MeasurableSet chartPiece`.
- The statement does not claim Aoyagi pp. 10-13 prove the reverse raw-source
  domination.

## Independent Audit

Xhigh read-only scout `Mendel` judged the theorem shape honest and useful.  The
scout confirmed that the direction feeds the existing original-volume
domination consumers, that the reverse raw-source comparison must remain an
explicit hypothesis, and that the only hidden Lean API point is the raw-chart
a.e. measurability for the raw image measure, handled by raw-image support in
`rawSourceSet`.

## Verification

Focused warning-clean elaboration passed for
`RetainedPassiveCase2PassiveThetaFormalProductSourceReference.lean` and
`RetainedPassiveCase2PassiveThetaOriginalVolumeBridge.lean`.  Focused local
Lake builds for both modules passed, with only pre-existing imported warning
noise.  Full local `lake build DLNFibre`, `scripts/sorries`, `git diff
--check`, and direct theorem axiom audit passed.  Both new theorems report
only `[propext, Classical.choice, Quot.sound]`.
