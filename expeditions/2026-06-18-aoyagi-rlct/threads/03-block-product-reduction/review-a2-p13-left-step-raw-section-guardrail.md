# Review - A2 p.13 left-step raw section guardrail

Date: 2026-06-26.

Reviewers: xhigh read-only scouts `Dalton the 2nd` and `Bernoulli the 2nd`.

Verdict: guardrail required and now recorded.

## Scope Checked

The scouts checked the conditional raw pushforward consumer around:

```text
paperEndpointFixedBaseP13RawPreimageTuple
p13ProductCoordinateLeftStepRawTopologyTuple
map_p13RawOrderTuple_eq_withDensity_inverseJacobian_of_leftStepRaw_map
```

## Finding

Aoyagi p.13 supports the finite product-coordinate algebra, but not a theorem
that the p.13 raw section pushes a source measure to full additive Haar
measure restricted to the raw determinant chart.

The support issue is structural.  The raw preimage tuple has the shape

```text
(I,Dtail,F3,Ctop,-Ctop*F2,0,C0).
```

Thus its raw `C1` coordinate is fixed to `I` and its raw `A3` coordinate is
fixed to `0`.  In nontrivial raw `C1` or `A3` directions this is a
lower-dimensional section of the full raw determinant chart, not a
full-dimensional raw-Haar parametrisation.

## Lean Guardrails

The follow-up Lean patch records the section facts:

```text
paperEndpointFixedBaseP13RawPreimageTuple_C1_eq_one
paperEndpointFixedBaseP13RawPreimageTuple_A3_eq_zero
p13ProductCoordinateLeftStepRawTopologyTuple_C1_eq_one
p13ProductCoordinateLeftStepRawTopologyTuple_A3_eq_zero
```

These are guardrails, not a formal global non-equality theorem.  They explain
why the raw pushforward should remain an explicit source/product-chart
hypothesis unless a later chart construction supplies the correct measure data.

## Nonclaims Reconfirmed

The slice does not prove the supplied raw pushforward, source coverage,
original DLN source/prior transport, p.13 source-chart construction from
original coordinates, signed-box density identification, product-measure
pushforward, regular-suspension certification, normal crossings, pole order,
or RLCT.
