# Review - A2 p.13 left-step Ctop from raw-chart support

Date: 2026-06-26.

Reviewer: xhigh read-only scout `Harvey the 2nd`.

Verdict: sound, conditional on the existing raw-map a.e. measurability input.

## Scope Checked

The scout checked whether the p.13 `Ctop` determinant-unit a.e. hypothesis can
be derived from the supplied raw pushforward

```text
Measure.map p13ProductCoordinateLeftStepRawTopologyTuple eta =
  m.restrict rawDetChart.
```

## Finding

Yes, provided the raw tuple map is already a.e.-measurable.  This is exactly
the remaining measurability hypothesis in the conditional consumer.

The generic support argument is:

```text
map pre eta = m|S
S null-measurable
pre a.e.-measurable
--------------------------------
pre x in S for eta-a.e. x
```

For the p.13 raw preimage tuple, membership in `S = rawDetChart` gives two
unit conditions.  The second raw chart condition is the `A1` determinant unit,
and the p.13 raw preimage tuple has `A1 = Ctop`.  Therefore `IsUnit det(Ctop)`
holds a.e.

## Lean Names

```text
ae_mem_productReductionStepRawDetChartSet_of_map_eq_restrict
ae_isUnit_ctopMatrix_det_of_p13RawPreimage_map_eq_restrict_rawDetChart
ae_isUnit_ctopMatrix_det_of_p13LeftStepRaw_map_eq_restrict_rawDetChart
```

The conditional consumer theorems now derive the needed `Ctop` a.e. unit fact
internally and no longer take it as an input:

```text
map_p13RawOrderTuple_eq_withDensity_inverseJacobian_of_rawPreimage_map
map_p13RawOrderTuple_eq_withDensity_inverseJacobian_of_leftStepRaw_map
```

## Nonclaims Reconfirmed

This does not prove the supplied raw pushforward.  It only extracts support
information from that hypothesis.  The earlier section guardrail remains: the
p.13 section fixes raw `C1 = I` and `A3 = 0`, so p.13 raw algebra alone should
not be read as a full raw-Haar chart construction.
