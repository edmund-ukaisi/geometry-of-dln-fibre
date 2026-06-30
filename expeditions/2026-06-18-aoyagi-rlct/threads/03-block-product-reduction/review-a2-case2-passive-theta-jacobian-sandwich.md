# Review - A2 Case 2 passive theta Jacobian sandwich

Date: 2026-06-30.

## Verdict

PASS after one minor API repair.

Two xhigh read-only reviews checked the slice before banking:

- Source/scope reviewer `Aristotle` returned PASS.
- Lean/API reviewer `Copernicus` returned one minor finding, repaired.

## Source And Scope Review

`Aristotle` checked that the Lean theorem is a thin specialization of the
existing passive-parameter sandwich: it sets
`eta = Case2PassiveTheta.PassiveFields`, defines
`sourceMeasure = passiveMeasure.prod weightedBox`, defines `Y` using
`case2PassiveThetaEndpointTopologyTuple`, unpacks the passive determinant
sector to `Ctop`/`A1passive` unit hypotheses, and applies the generic theorem.

No overclaim was found.  The Lean docstrings and markdown notes keep the
result scoped to local chart-domain Jacobian bookkeeping and exclude
determinant-chart Haar transport, raw-order Haar transport,
source-prior transport, exact passive-sector pushforward, source-image
equality, source-rank coverage, normal crossings, pole order, RLCT, and
quiver-paper evidence.

## Lean/API Review

`Copernicus` checked the definitional specialization against

```text
exists_pos_open_withDensity_sandwich_retainedPassiveFormalRawOrderJacobianProductAbsDetAt_case2EndpointTransport_withPassive_passiveProductMeasure
```

and found that the first version unnecessarily required
`[Fintype tau] [DecidableEq tau]`, even though the generic theorem only needs
`tau : Type`.  The theorem was repaired by removing those stronger hypotheses
and the now-unneeded linter suppressions.

No issue was found with determinant-sector unpacking, the definitional match
of `Y` with the generic retained-data topology tuple, namespaces/imports, or
the aggregator import.

## Verification

Reviewer direct checks:

```text
lake env lean DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaJacobianMeasure.lean
lake env lean DLNFibre.lean
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

All listed controller checks passed.  The focused and full builds replayed
only pre-existing warning noise from unrelated modules.  `./scripts/sorries`
reported:

```text
Summary: 0 sorry, 0 #exit, 0 native_decide, 0 axiom
```

Direct axiom probe for the public theorem reports:

```text
[propext, Classical.choice, Quot.sound]
```
