# Review - A2 Case 2 baseJ raw-image density handoff

Date: 2026-07-01.

Status: PASS.

## Reviewed Claim

The theorem

```text
exists_open_subset_measure_map_case2PassiveTheta_rawMap_baseJ_restrict_eq_withDensity_rawImage_of_jacobianDensity_ae_eq
```

returns a local Case 2 passive-theta open set `V subset G` and proves that, if
the theta-side Jacobian density factors a.e. through `rawMap` as an
a.e.-measurable raw density, then

```text
Measure.map rawMap (baseJ.restrict V)
=
(Measure.map rawMap (passiveSource.restrict V)).withDensity rawDensity.
```

The helper

```text
measure_map_restrict_withDensity_eq_withDensity_map_of_ae_eq
```

is the generic measure-theoretic density-pushforward lemma.

## Verdict

PASS as a raw-image handoff, provided the theorem is not described as raw Haar
transport.

## Checks

- Source-boundary check: the theorem uses only the local Case 2 chart sector
  and generic `withDensity` bookkeeping.  It does not assert the missing
  determinant-chart/passive-product Haar transport.
- Lean-shape check: the theorem exposes the raw-image measure
  `Measure.map rawMap (passiveSource.restrict V)` in the conclusion, so no
  hidden Haar normalization or image-coverage claim is present.
- Factorization check: the a.e. identity
  `jacobianDensity z = rawDensity (rawMap z)` is explicit.  A future theorem can
  instantiate `rawDensity` using the raw-order inverse density, but this file
  does not claim that instantiation.
- Verification: focused elaboration, focused module build, full local
  `lake build DLNFibre`, `scripts/sorries`, `git diff --check`, and direct
  axiom probe all passed.  The direct axiom probe for both public theorem names
  reports only `[propext, Classical.choice, Quot.sound]`.
- Independent review: xhigh Lean/API reviewer `Anscombe the 3rd` returned
  PASS with no findings; xhigh math/source-boundary reviewer
  `Schrodinger the 3rd` returned PASS.  The only requested wording hardening,
  clarifying that p.13 supplies block/product raw-order algebra rather than a
  measure theorem, was applied in `theorem-ledger.md`.

## Nonclaims

No raw-Haar pushforward, determinant-chart Haar transport from
`passiveSource`, original source-prior transport, source-image coverage,
source-rank coverage, scalar normalization, normal crossings, pole order, or
RLCT extraction is proved.
