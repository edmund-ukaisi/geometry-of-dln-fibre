# Statement Card - A2 Case 2 with-following endpoint source-chart image support

## Statement

Near any enlarged Case 2 determinant-sector point with nonzero selected pivot,
inside any prescribed open theta-neighborhood `G`, there is a smaller open set
`V` such that the with-following endpoint source chart is injective and
continuous on `V`, has measurable image, and for every theta-domain measure
`thetaMeasure`,

```text
let mu = Measure.map sourceChart (thetaMeasure.restrict V)

mu.restrict (sourceChart '' V) = mu.
```

## Kill Condition

The claim would fail if the image `sourceChart '' V` were not measurable or if
`sourceChart` were not a.e.-measurable on `thetaMeasure.restrict V`.  In Lean
these are supplied by the local source-chart continuity and measurable-image
package.

## Source And Dependencies

- Aoyagi Case 2 selected-pivot coordinate calculation, PDF pp. 19-21.
- Existing with-following local source-chart image theorem:
  `exists_open_subset_continuousOn_measurableSet_case2PassiveThetaWithFollowingFactorEndpointSourceChart_image_readback_leftInverse`.
- Generic image-support lemma:
  `measure_map_restrict_image_eq_self_of_aemeasurable`.

## Lean Target

```text
exists_open_subset_measure_map_case2PassiveThetaWithFollowingFactorEndpointSourceChart_restrict_image_eq_self_readback_leftInverse
```

## Nonclaims

No local `Y` change of variables, no determinant-chart Haar equality, no
endpoint Haar transport, no external/original source-prior identification, no
source-image coverage beyond the actual local image, no density comparison, no
raw-map pushforward, no normal crossings, no pole order, and no RLCT
extraction.
