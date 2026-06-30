# Review - A2 Case 2 passive theta product-measure residual-source adapter

Date: 2026-06-30.

## Verdict

PASS.

Two xhigh read-only reviews checked the slice before banking:

- Source/scope reviewer `Parfit` returned PASS.
- Lean/API reviewer `Averroes` returned PASS.

## Source And Scope Review

`Parfit` checked that the Lean wrappers conclude only:

- support of the chart-produced measure on the retained-passive p.13 local
  source;
- a.e. residual square-sum positivity on that local source;
- `residualNegPowerIntegrableOn` for the chart-produced measure.

The concrete product-measure wrapper uses the generic handoff whose proof
transfers residual hypotheses by domination of the restricted `yNext` marginal,
not by exact restricted marginal equality.  The arbitrary-source wrapper keeps
both local assumptions explicit after the sector is chosen:

```text
c < infinity,
sourceMeasure.restrict V <= c • passiveSource.
```

No determinant-chart Haar transport, raw-order Haar transport, source-prior
transport, source-image equality, source-rank coverage, normal crossings, pole
order, RLCT extraction, or quiver-paper dependence was found.

## Lean/API Review

`Averroes` checked that both public theorems are definitional specializations
of existing generic handoffs:

```text
exists_open_residualSourceHypotheses_of_case2PassiveThetaEndpointSourceChart_puncturedSector_yNext_passiveProductMeasure_finiteMass
exists_open_residualSourceHypotheses_of_case2PassiveThetaEndpointSourceChart_puncturedSector_yNext_of_restrict_le_smul_passiveProductMeasure_finiteMass
```

The namespace, imports, finite-mass/domination statements, topology and
measurability hypotheses, and `Case2PassiveTheta.yNext` specialization line up
with the generic APIs.  The aggregator import is appended at the end of
`lean/DLNFibre.lean`.

## Verification

Reviewer direct checks:

```text
lake env lean DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaProductMeasure.lean
lake env lean DLNFibre.lean
```

Controller final checks:

```text
lake env lean -E warning DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaProductMeasure.lean
env LEAN_NUM_THREADS=3 lake build DLNFibre.DLN.Aoyagi.RetainedPassiveCase2PassiveThetaProductMeasure
lake env lean -E warning DLNFibre.lean
env LEAN_NUM_THREADS=3 lake build DLNFibre
./scripts/sorries
git diff --check
```

All controller checks passed.  The focused and full builds replayed only
pre-existing warning noise from unrelated modules.  `./scripts/sorries`
reported:

```text
Summary: 0 sorry, 0 #exit, 0 native_decide, 0 axiom
```

Direct axiom probes for both public theorems report:

```text
[propext, Classical.choice, Quot.sound]
```
