# A2 Case 2 With-Following Endpoint Reference Image Writeback Factorization

## Purpose

The with-following endpoint map had a pointwise factorization through the
active selected-entry chart and active writeback.  Downstream measure
arguments need the same statement at the level of the named endpoint reference
image measure.

## Calculation

Let

```text
referenceSource =
  case2PassiveThetaWithFollowingFactorReferenceSourceMeasure n hS hnext Rres

Y z =
  case2PassiveThetaWithFollowingFactorEndpointTopologyTuple
    n hS hcont hnext z eNext e

activeChart z =
  ((z.1.1, chartMap pivotNext z.1.yNext), z.2)

activeWriteback =
  Case2PassiveThetaWithFollowingFactor.endpointTopologyTupleActiveWriteback n e
```

The endpoint reference image is defined by

```text
endpointReferenceImage = Measure.map Y (referenceSource.restrict Omega).
```

The pointwise writeback theorem gives

```text
Y z = activeWriteback (activeChart z).
```

The new continuity theorem

```text
continuous_endpointTopologyTupleActiveWriteback
```

turns `activeWriteback` into a measurable map.  The active selected-entry
chart is measurable because it is a product map whose nontrivial center
coordinate component is `SelectedEntrySignedBox.CenterCoord.chartMap`, already
known measurable.  Therefore `Measure.map_map` gives:

```text
endpointReferenceImage =
  Measure.map activeWriteback
    (Measure.map activeChart (referenceSource.restrict Omega)).
```

No measurability or support assumption on `Omega` is needed for this
pushforward identity.

## Boundary

This is an endpoint-image pushforward factorization only.  It does not
identify the endpoint image with determinant-chart Haar measure, does not
prove a raw-order change of variables for the endpoint image, does not
normalize raw Haar, does not transport the original prior, and does not prove
coverage, normal crossings, pole order, or RLCT.

## Verification

Checked on 2026-07-02 in the `expedition/aoyagi-rlct` worktree with local
Lake commands:

```text
cd lean
env LEAN_NUM_THREADS=3 lake build DLNFibre.DLN.Aoyagi.RetainedPassiveCase2PassiveThetaCFieldReadout
env LEAN_NUM_THREADS=3 lake build DLNFibre.DLN.Aoyagi.RetainedPassiveCase2PassiveThetaWithFollowingFactorEndpointReference
env LEAN_NUM_THREADS=3 lake build DLNFibre
scripts/sorries
git diff --check
rg -n "\bsorry\b|\badmit\b|TODO|FIXME|native_decide|#exit|\baxiom\b" \
  lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaCFieldReadout.lean \
  lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaWithFollowingFactorEndpointReference.lean
env LEAN_NUM_THREADS=3 lake env lean /tmp/aoyagi_endpoint_writeback_axioms.lean
```

The focused modules and full library build passed.  `scripts/sorries`
reported `0 sorry, 0 #exit, 0 native_decide, 0 axiom`.  The touched-file
marker scan found no matches, and the direct axiom probe for both new
declarations reported exactly `[propext, Classical.choice, Quot.sound]`.
