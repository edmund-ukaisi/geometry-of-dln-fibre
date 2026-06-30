# Review - A2 Case 2 passive theta Jacobian-weighted residual source

Date: 2026-06-30.

## Verdict

PASS.

Two xhigh read-only reviews checked the slice before banking:

- Source/scope reviewer `Meitner` returned PASS.
- Lean/API reviewer `Hubble` returned PASS.

## Source And Scope Review

`Meitner` checked that the Lean theorem only combines the concrete
`Case2PassiveTheta` Jacobian sandwich with the existing local-domination
residual-source socket.  The proof first obtains the open Jacobian-unit
neighborhood `U` and upper scalar domination from
`exists_pos_open_withDensity_sandwich_retainedPassiveFormalRawOrderJacobianProductAbsDetAt_case2PassiveThetaEndpointTopologyTuple_passiveProductMeasure`,
then invokes
`exists_open_residualSourceHypotheses_of_case2PassiveThetaEndpointSourceChart_puncturedSector_yNext_of_restrict_le_smul_passiveProductMeasure_finiteMass`
for the second open neighborhood `V`.

No overclaim was found.  The reproduction and statement card keep the result
scoped to local domination bookkeeping for

```text
sourceMeasure =
  ((passiveMeasure.prod weightedBox).restrict U).withDensity
    (fun z => ofReal (retainedPassiveFormalRawOrderJacobianProductAbsDetAt (Y z)))
```

and exclude determinant-chart Haar transport, raw-order Haar transport,
source-prior transport, exact passive-sector pushforward, source-image
equality, source-rank coverage, normal crossings, pole order, and RLCT.

## Lean/API Review

`Hubble` checked the theorem shape against the intended APIs:

- `U` is obtained from the theta Jacobian sandwich.
- `sourceMeasure` is the `U`-restricted passive-product measure with the
  Jacobian `withDensity`.
- The upper sandwich is converted to global domination using
  `measure_le_smul_of_le_smul_restrict`.
- The residual-source theorem returns `V`, and the final mapped measure uses
  `sourceMeasure.restrict V`.

No import, typeclass, namespace, or definitional-shape issue was found.

## Verification

Reviewer direct check:

```text
lake env lean DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaJacobianMeasure.lean
```

Controller checks:

```text
lake env lean -E warning DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaJacobianMeasure.lean
env LEAN_NUM_THREADS=3 lake build DLNFibre.DLN.Aoyagi.RetainedPassiveCase2PassiveThetaJacobianMeasure
lake env lean -E warning DLNFibre.lean
env LEAN_NUM_THREADS=3 lake build DLNFibre
./scripts/sorries
git diff --check
```

All listed controller checks passed.  The focused and full builds replayed only
pre-existing warning noise from unrelated modules.  `./scripts/sorries`
reported:

```text
Summary: 0 sorry, 0 #exit, 0 native_decide, 0 axiom
```

Direct axiom probe for the public theorem reports:

```text
[propext, Classical.choice, Quot.sound]
```
