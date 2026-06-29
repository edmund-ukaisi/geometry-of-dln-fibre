# Reproduction - A2 Case 2 Passive Chart-Produced Support

Date: 2026-06-29.

## Source Slice

Aoyagi pp. 10-13 give the Case 2 retained-passive block substitutions and the
p.13 residual product display.  The Lean source point now has the form

```text
z = (theta, y) : eta x (center -> R)
```

where `theta` carries passive fields and `y` carries the selected-entry
residual center coordinates.  The previous banked theorem proved pointwise
that, under determinant-unit hypotheses on `Ctop` and `A1passive`, and under
the supplied rank equation at `y`, the constructed source point lies in the
named source-rank stratum and retained-passive p.13 local source.

## Claim to Formalise

Let `sourceMeasure` be any measure on the passive chart domain
`eta x (center -> R)`.  Let

```text
sourceChart z =
  paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilyOfData
    W2 B2 U0 hU0 (retainedData z)
```

where `retainedData z` is the endpoint-transported passive selected-entry
datum.  If `sourceChart` is a.e. measurable for `sourceMeasure`, then:

- the pushforward measure `mu = Measure.map sourceChart sourceMeasure`
  restricts to the retained-passive p.13 local source as itself;
- if the successor rank equation holds `sourceMeasure`-a.e., then `mu`
  restricts to the source-rank stratum as itself.

This is support bookkeeping for a chart-produced measure.  It is not a
determinant-chart pushforward formula, product-measure construction, raw-Haar
transport, external source-prior transport, Jacobian formula, normal-crossing
statement, pole-order statement, or RLCT extraction.

## Calculation

The local-source support is direct.  The previous source-readback theorem gives

```text
forall z, sourceChart z in retainedPassiveP13LocalSource.
```

Therefore it holds `sourceMeasure`-a.e.  The generic retained-passive measure
lemma

```text
measure_map_restrict_retainedPassiveP13LocalSource_eq_self_of_ae_mem
```

turns this a.e. membership into

```text
(Measure.map sourceChart sourceMeasure).restrict localSource =
  Measure.map sourceChart sourceMeasure.
```

The source-rank support is the same argument with one extra a.e. hypothesis.
Assume

```text
forall^ae z, r + rank(case2SuccessorSelectedEntryMatrix z.2) = rEdge 1.
```

For an a.e. such `z`, the previous pointwise source-rank theorem gives

```text
sourceChart z in paperEndpointFixedBaseSourceRankStratum W2 B2 id r rEdge.
```

The generic source-rank measure lemma

```text
measure_map_restrict_sourceRankStratum_eq_self_of_ae_mem
```

then gives

```text
(Measure.map sourceChart sourceMeasure).restrict sourceStratum =
  Measure.map sourceChart sourceMeasure.
```

## Dependency Boundary

The theorem should carry:

- explicit determinant-unit hypotheses on `Ctop` and `A1passive`;
- explicit `AEMeasurable sourceChart sourceMeasure`;
- for source-rank support, explicit `hprod`, `hr0`, and a.e. `hr1`;
- no continuity assumptions on the passive fields unless a later theorem
  constructs a concrete product measure and proves `sourceChart` measurable;
- no source-prior or Jacobian claim.

## Expected Lean Targets

```text
measure_map_case2EndpointTransport_sourceEdgeFamilyOfData_withPassive_restrict_retainedPassiveP13LocalSource_eq_self
measure_map_case2EndpointTransport_sourceEdgeFamilyOfData_withPassive_restrict_sourceRankStratum_eq_self
```
