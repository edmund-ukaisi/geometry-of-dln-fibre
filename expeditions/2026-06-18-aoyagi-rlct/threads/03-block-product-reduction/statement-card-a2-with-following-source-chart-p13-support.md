# Statement card - A2 with-following source-chart p.13 support

## Lean Target

File:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaSourceImage.lean
```

Name:

```text
exists_open_subset_measurableSet_case2PassiveThetaWithFollowingFactorEndpointSourceChart_image_subset_p13SourceEdgeFamilySet
```

The exported constant is under:

```text
DLNFibre.DLN.Aoyagi.PaperEndpointFixedBaseRegularCoordinateSourceData
```

## Claim

After shrinking inside a prescribed open neighborhood `G` of a Case 2
with-following passive-theta point, the actual endpoint source-chart image is
locally supported on Aoyagi's p.13 retained-passive source edge-family set:

```text
forall E in sourceChart '' V, E in p13SourceSet.
```

The same local shrink also carries the existing determinant-sector,
readback-left-inverse, injectivity, continuity, and measurable-image fields for
the source chart.

## Proved

Lean proves pointwise support by unfolding the with-following endpoint source
chart into the fixed-base retained-passive p.13 source chart and applying the
existing retained-passive source membership theorem.  Image support is then the
one-line image elimination: if `E = sourceChart z` with `z in V`, the pointwise
support theorem gives `E in p13SourceSet`.

## Assumed

The theorem assumes the usual local Case 2 base data:

- the base point lies in the with-following determinant sector;
- the selected pivot at the base point is nonzero;
- `G` is open and contains the base point;
- the standard finite-dimensional/measurable-space instances for the
  with-following theta and edge-family targets.

## Cited

None.

## Deferred

No p.13 source-set coverage, no p.13 image equality, no source-prior or
original-prior transport, no raw Haar transport, no determinant-chart Haar
transport, no normal crossings, no pole order, and no RLCT extraction.

## Status

Focused module elaboration, full local `lake build DLNFibre`, no-sorry audit,
whitespace check, touched-file marker scan, and direct axiom probe passed.  The
theorem reports `[propext, Classical.choice, Quot.sound]`.  Xhigh reviewer
`Avicenna the 2nd` passed with no findings.
