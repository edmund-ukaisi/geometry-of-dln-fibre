# A2 Localized Composed Retained-Passive Raw-Order COV

## Purpose

The localized retained-passive raw-order change of variables identified the
raw-order image of a determinant-chart patch.  Downstream arguments often need
to compose that raw-order image with a source chart, readback, or another
measurable target map.  This checkpoint records the composed form directly.

## Calculation

Let

```text
Phi = topologyTupleEdgeRawOrder
Omega subset topologyTupleDetChartSet
Jprod z = ofReal (retainedPassiveFormalRawOrderJacobianProductAbsDetAt z).
```

The localized COV gives:

```text
Measure.map Phi ((m.restrict Omega).withDensity Jprod)
  = m.restrict (Phi '' Omega).
```

If a post-map `psi` is a.e. measurable on the localized image measure
`m.restrict (Phi '' Omega)`, then it is a.e. measurable on the pushforward
`Measure.map Phi ((m.restrict Omega).withDensity Jprod)` by the equality
above.  Since `Phi` is continuous on the determinant chart, it is a.e.
measurable for `(m.restrict Omega).withDensity Jprod`.  Therefore
`AEMeasurable.map_map` gives:

```text
Measure.map (fun z => psi (Phi z))
  ((m.restrict Omega).withDensity Jprod)
=
Measure.map psi
  (m.restrict (Phi '' Omega)).
```

## Boundary

This is determinant-chart measure infrastructure only.  It does not prove
endpoint-Haar transport, source-to-endpoint Haar comparison, concrete Aoyagi
raw-pushforward, source-prior/original-prior transport, coverage, normal
crossings, pole order, or RLCT.

## Verification

Focused module build passed on 2026-07-02 in the `expedition/aoyagi-rlct`
worktree:

```text
cd lean
env LEAN_NUM_THREADS=3 lake build DLNFibre.DLN.Aoyagi.RetainedPassiveCoordinatesJacobianMeasure
```

Full verification and axiom-probe results are recorded in `synthesis.md` for
the corresponding checkpoint.
