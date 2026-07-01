# Review - A2 Case 2 baseJ raw-image inverse-readback density

Date: 2026-07-01.

Status: PASS.

## Reviewed Claim

The theorem

```text
exists_open_subset_measure_map_case2PassiveTheta_rawMap_baseJ_restrict_eq_withDensity_rawImage_rawOrderInverse_jacobianDensity
```

returns a local Case 2 passive-theta open set `V subset G` and proves

```text
Measure.map rawMap (baseJ.restrict V)
=
(Measure.map rawMap (passiveSource.restrict V)).withDensity rawDensity,
```

where

```text
rawDensity y =
  ofReal
    (retainedPassiveFormalRawOrderJacobianProductAbsDetAt
      (topologyTupleEdgeRawOrderInverse y)).
```

## Verdict

PASS as a concrete raw-image handoff, provided the raw density is described as
source-side Jacobian readback and not as the inverse Jacobian density.

## Checks

- Factorization check: on the returned sector, `Y z` lies in the determinant
  chart, so `topologyTupleEdgeRawOrderInverse (rawMap z) = Y z`.  Therefore the
  new `rawDensity` pulls back to `jacobianDensity`.
- Measurability check: `rawMap` is continuous on `V`; the raw image is
  a.e. supported on the raw-order source-recursive determinant chart; on that
  chart, raw-order inverse is continuous and the retained-passive formal
  Jacobian product is continuous at the inverse point.
- Boundary check: the theorem keeps
  `Measure.map rawMap (passiveSource.restrict V)` visible.  It does not
  identify that measure with raw Haar or with a prescribed raw-source set.
- Verification: focused elaboration, focused module build, full local
  `lake build DLNFibre`, `scripts/sorries`, `git diff --check`, and direct
  axiom probe all passed.  The direct axiom probe reports only
  `[propext, Classical.choice, Quot.sound]`.
- Independent review: xhigh Lean/math scout `Pasteur the 3rd` returned PASS,
  confirmed the factorization and a.e.-measurability route, and emphasized the
  naming boundary: this is a forward Jacobian product read through raw-order
  inverse, not the target-side inverse-Jacobian density.

## Nonclaims

No raw-Haar pushforward, determinant-chart Haar transport from
`passiveSource`, raw Haar normalization, original source-prior transport,
source-image coverage, source-rank coverage, normal crossings, pole order, or
RLCT extraction is proved.
