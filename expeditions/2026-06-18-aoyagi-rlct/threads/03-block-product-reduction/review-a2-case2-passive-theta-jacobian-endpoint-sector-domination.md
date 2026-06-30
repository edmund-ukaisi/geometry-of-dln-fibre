# Review - A2 Case 2 passive theta Jacobian endpoint-sector domination

Date: 2026-06-30.

## Verdict

PASS.

Two xhigh read-only reviews checked the slice before banking:

- Source/scope reviewer `Hegel` returned PASS.
- Lean/API reviewer `Epicurus` returned PASS.

## Source And Scope Review

`Hegel` checked that the theorem is a faithful next Aoyagi-only step after
sector support and conditional endpoint-sector domination.  It uses only the
upper side of the local `Case2PassiveTheta` Jacobian sandwich, rewrites the
restricted `withDensity`, and applies the existing endpoint-sector domination
transfer.

No overclaim was found.  The statement keeps the endpoint sector image
measurability and endpoint map measurability explicit, and it does not claim
exact passive-sector Haar pushforward, determinant-chart Haar transport,
raw-order Haar transport, source-prior comparison, source-image equality,
source-rank coverage, normal crossings, pole order, or RLCT extraction.

The reviewer requested wording repairs, now applied in the Lean docstring:
the density is described as the concrete retained-passive formal raw-order
Jacobian density, and the nonclaim list includes source-image equality and
source-rank coverage.

## Lean/API Review

`Epicurus` verified read-only that the target and source files elaborate with
`lake env lean`.  The proof correctly consumes the upper Jacobian sandwich and
then calls

```text
measure_map_case2PassiveThetaEndpointTopologyTuple_restrict_endpointSectorSet_le_smul
```

from `RetainedPassiveCase2PassiveThetaSourceMeasure.lean`.

API recommendations addressed:

- add a direct import of
  `RetainedPassiveCase2PassiveThetaSourceMeasure.lean` instead of relying on a
  transitive import;
- present the sector measurability condition as an implication after `U` is
  chosen, rather than as a named dependent `forall` binder.

The explicit measurability hypothesis on `Y` is kept.  Deriving it from
continuity would require additional Borel/open-measurable assumptions on the
target measurable space.

## Verification

Controller checks before banking:

```text
lake env lean -E warning DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaJacobianMeasure.lean
env LEAN_NUM_THREADS=3 lake build DLNFibre.DLN.Aoyagi.RetainedPassiveCase2PassiveThetaJacobianMeasure
lake env lean -E warning DLNFibre.lean
env LEAN_NUM_THREADS=3 lake build DLNFibre
./scripts/sorries
git diff --check
```

All listed checks passed when run from the local `lean/` directory, except
`git diff --check`, which was run from the repository root.  The focused and
full builds replayed only pre-existing warning noise from unrelated modules.
`./scripts/sorries` reported:

```text
Summary: 0 sorry, 0 #exit, 0 native_decide, 0 axiom
```

Direct axiom probe for the public theorem reports:

```text
[propext, Classical.choice, Quot.sound]
```

## Nonclaims

This slice does not prove exact passive-sector Haar transport,
determinant-chart Haar transport, raw-order Haar transport, source-prior
comparison, source-image equality, source-rank coverage, normal crossings,
pole order, or RLCT extraction.
