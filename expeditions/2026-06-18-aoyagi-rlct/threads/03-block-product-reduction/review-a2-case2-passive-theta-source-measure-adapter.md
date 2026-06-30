# Review - A2 Case 2 passive theta source-measure adapter

Date: 2026-06-30.

## Verdict

PASS.

Two xhigh read-only reviews checked the adapter before banking:

- Source/scope reviewer `Banach` returned PASS.
- Lean/API reviewer `Popper` returned PASS.

## Source And Scope Review

`Banach` checked that the theorem is scoped to an arbitrary source-domain
measure on the concrete theta coordinate domain, restricted to an existential
open punctured determinant sector.  The conclusion is support on the
retained-passive p.13 local source and exact selected residual inverse readout
as the `Case2PassiveTheta.yNext` marginal.

The passive-fields `MeasurableSpace` and `OpensMeasurableSpace` hypotheses are
explicit.  The adapter consumes those instances; it does not build or identify
determinant-chart measure structure.

No determinant-chart Haar transport, source-prior transport, exact
passive-sector pushforward, dominated passive-sector comparison,
finite-integral transfer, source-image equality, source-rank coverage, normal
crossings, pole order, or RLCT claim was found.

The source note is Aoyagi-only: pp. 10-13 support the retained-passive p.13
coordinate chart and pp. 19-22 support the Case 2 selected-entry residual
readout.  No quiver-paper evidence is used.

## Lean/API Review

`Popper` checked the public adapter definitions:

```text
case2PassiveThetaEndpointSourceChart
case2PassiveThetaEndpointResidualCoordEquiv
case2PassiveThetaEndpointInverseReadout
```

and the theorem:

```text
exists_open_measure_map_case2PassiveThetaEndpointSourceChart_puncturedSector_inverseReadout_eq_yNext
```

The proof is a specialization of:

```text
exists_open_measure_map_case2EndpointTransport_withPassive_puncturedSector_inverseReadout_eq_snd
```

with `eta = Case2PassiveTheta.PassiveFields`.  The aggregator import order in
`lean/DLNFibre.lean` was also checked.

## Verification

Reviewer direct checks:

```text
lake env lean -E warning DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaSourceMeasure.lean
lake env lean -E warning DLNFibre.lean
```

Both passed with no output.

Controller final gates before banking:

```text
lake env lean -E warning DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaSourceMeasure.lean
env LEAN_NUM_THREADS=3 lake build DLNFibre.DLN.Aoyagi.RetainedPassiveCase2PassiveThetaSourceMeasure
env LEAN_NUM_THREADS=3 lake build DLNFibre
./scripts/sorries
git diff --check
lake env lean -E warning DLNFibre.lean
```

All passed.  The focused and full builds replay only pre-existing warning noise
from unrelated modules.  `./scripts/sorries` reported:

```text
Summary: 0 sorry, 0 #exit, 0 native_decide, 0 axiom
```

Direct axiom probe for the public theorem reports:

```text
[propext, Classical.choice, Quot.sound]
```
