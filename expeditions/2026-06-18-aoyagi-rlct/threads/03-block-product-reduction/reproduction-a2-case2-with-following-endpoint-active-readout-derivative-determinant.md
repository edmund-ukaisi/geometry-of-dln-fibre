# Reproduction - A2 Case 2 with-following endpoint active-readout derivative determinant

Date: 2026-07-02.

Status: controller pen-and-paper reproduction before review.

## Question

For the enlarged Case 2 endpoint map

```text
Y z =
  case2PassiveThetaWithFollowingFactorEndpointTopologyTuple
    n hS hcont hnext z eNext e,
```

can we prove the selected-entry Jacobian determinant after reading back the
active endpoint coordinates?

Answer: yes, for the source-type composite

```text
endpointTopologyTupleActiveReadout n e (Y z).
```

This avoids the source/target coordinate mismatch in the bare endpoint map
`Y`, while proving the determinant factor that Aoyagi's Case 2 calculation
uses.

## Source Calculation

Aoyagi's Case 2 selected-entry chart on PDF pp. 19-21 chooses the displayed
successor pivot coordinate.  In Lean this pivot is

```text
pivotNext = case2PassiveThetaPivotNext n hS hnext.
```

Write the active center coordinates as

```text
y pivotNext = u,
y i = v_i      for i != pivotNext.
```

The selected-entry chart sends

```text
u       |-> u,
v_i     |-> u * v_i.
```

With the pivot coordinate first, the derivative matrix has block form

```text
[ 1    0  ]
[ *   u I ].
```

Therefore its determinant is `u^k`, where `k` is the number of non-pivot
center coordinates.  In Lean this is

```text
(center.erase pivotNext).card,
```

and the absolute determinant is exactly

```text
SelectedEntrySignedBox.CenterCoord.sourceDensity pivotNext y.
```

Under the rectangular residual-block reading of the paper, this is Aoyagi's
`|u|^(mn - 1)` selected-entry factor.

For the enlarged source point

```text
z = ((passiveFields, yNext), followingFactor),
```

the active source-side map is

```text
((passiveFields, yNext), followingFactor)
  |->
((passiveFields, chartMap pivotNext yNext), followingFactor).
```

The passive fields and the free following factor are identities in this
source-type coordinate map, so their determinant contributions are `1`.
Thus the full source-type determinant is only the selected-entry determinant.
Here the following factor is Lean's normalized retained/raw `C(0)` coordinate,
not Aoyagi's original untransformed following matrix.

The endpoint-facing equality already proved in Lean is

```text
endpointTopologyTupleActiveReadout n e (Y z)
  =
((z.1.1, chartMap pivotNext z.1.yNext), z.2).
```

Consequently the derivative determinant of the composite active readout
equals the selected-entry source density.

## Lean Target

File:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaEndpointDerivative.lean
```

New declarations:

```text
Case2PassiveThetaWithFollowingFactor.activeSelectedEntryChartMapFDeriv
Case2PassiveThetaWithFollowingFactor.hasFDerivAt_activeSelectedEntryChartMap
Case2PassiveThetaWithFollowingFactor.activeSelectedEntryChartMapFDeriv_absDet_eq_sourceDensity
Case2PassiveThetaWithFollowingFactor.fderiv_activeSelectedEntryChartMap
Case2PassiveThetaWithFollowingFactor.fderiv_endpointTopologyTupleActiveReadout_comp_case2PassiveThetaWithFollowingFactorEndpointTopologyTuple_absDet_eq_sourceDensity
```

## Reproduction Verdict

This is a valid elementary Case 2 derivative theorem.  It is the determinant
calculation behind the selected-entry density factor for the endpoint active
readout.  No pivot-nonzero hypothesis is needed for the determinant equality
itself; at `u = 0` both sides vanish.  Pivot nonzero is needed later for
inverse-chart and local COV statements.

## Kill Conditions

- The theorem must be stated for `activeReadout o Y`, not for the bare endpoint
  topology-tuple map `Y`.
- The determinant must be an endomorphism determinant on the enlarged source
  coordinate type.
- Passive and following-factor coordinates must contribute determinant `1`;
  the selected-entry chart is the only nontrivial factor.
- The source-density convention must be forward/source-side:
  `sourceDensity pivotNext yNext`, not its reciprocal.

## Nonclaims

No local change-of-variables theorem, no endpoint Haar/reference-image
identification, no determinant-chart Haar equality, no raw-Haar transport, no
raw-order composition, no source-image coverage beyond actual images, no
formal-product domination, no normal crossings, no pole order, and no RLCT
extraction is proved here.
