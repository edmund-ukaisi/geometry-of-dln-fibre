# Review - A2 Case 2 passive theta bounded-density residual-source adapter

Date: 2026-06-30.

## Verdict

PASS.

Two xhigh read-only reviews checked the slice before banking:

- Source/scope reviewer `Fermat` returned PASS.
- Lean/API reviewer `Pauli` returned PASS.

## Source And Scope Review

`Fermat` checked that the Lean theorem, reproduction note, and statement card
stay scoped to the concrete passive-product comparison measure

```text
passiveSource = passiveMeasure.prod weightedBox
sourceMeasure = passiveSource.withDensity sourceDensity
```

and that the local a.e. density bound is quantified only after the open sector
`V` is returned:

```text
forall^ae z in passiveSource.restrict V,
  sourceDensity z <= c.
```

No overclaim was found for original source-prior density construction, proof
that an original prior satisfies the bound, exact restricted `yNext` marginal
equality, determinant-chart Haar transport, source-prior transport,
source-image/source-rank coverage, normal crossings, pole order, RLCT, or
quiver-paper evidence.

## Lean/API Review

`Pauli` checked that the public theorem is a definitional specialization of
the generic bounded-density passive-product handoff:

```text
exists_open_residualSourceHypotheses_of_case2PassiveThetaEndpointSourceChart_puncturedSector_yNext_of_withDensity_ae_le_const_passiveProductMeasure_finiteMass
```

The namespace and imports match the surrounding Aoyagi API.  The local bound is
stated as an a.e. bound with respect to `passiveSource.restrict V`; the
selected-entry signed-box density remains fully qualified, while
`sourceDensity` is only the theta-domain density.  `Case2PassiveTheta.yNext`
is unfolded only where needed for the pivot proof, and the final proof is a
definitional specialization of the generic handoff.

## Verification

Reviewer direct check:

```text
lake env lean DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaProductMeasure.lean
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

Direct axiom probe for the public theorem reports:

```text
[propext, Classical.choice, Quot.sound]
```
