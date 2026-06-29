# Statement Card - A2 Case 2 Passive Selected-Entry Local Source-Readback Domain

Status: sorry-free focused build and full aggregator build passed; direct axiom
probe passed; xhigh reviews PASS.

Reproduction:

```text
reproduction-a2-case2-passive-selected-entry-local-source-readback-domain.md
```

Lean files:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveSelectedEntrySource.lean
lean/DLNFibre.lean
```

## Claim

For passive selected-entry Case 2 coordinates, continuity of the passive fields
and determinant-unit hypotheses at one base point produce an open neighborhood
on which the endpoint-transported fixed-base p.13 source chart lies in the
retained-passive local source, and source readback recovers the full
endpoint-transported retained-passive datum.

## Lean

```text
exists_open_case2EndpointTransport_withPassive_detChart_sourceReadback_eq
```

## Proved

- The open set is the preimage of `topologyTupleDetChartSet` under
  `z |-> topologyTuple (retainedData z)`.
- The base point belongs to that open set using only the determinant-unit
  hypotheses for `Ctop z0.1` and `A1passive z0.1`.
- For each `z` in the open set, determinant-chart membership gives
  local-source membership for the fixed-base p.13 source edge family.
- For each `z` in the open set, source readback of the extracted fixed-base
  edge matrices equals the full transported retained-passive datum
  `retainedData z`.

## Assumed

- Case 2 dimension hypotheses `hS`, `hcont`, and `hnext`.
- Endpoint equivalences `e` and `eNext`.
- Continuity of the passive field families `A1passive`, `F2`, `A3passive`,
  `Ctop`, and `F3`.
- Basepoint determinant units for `Ctop z0.1` and `A1passive z0.1`.
- Fixed-base complement data `U0, hU0`.

## Cited

Aoyagi pp. 10-13 motivate the retained-passive p.13 block coordinates and
source chart.  The Lean proof is elementary finite-coordinate topology and
source-readback algebra already present in the retained-passive coordinate
library.

## Deferred

- Selected-entry source-image equality or local coverage for arbitrary nearby
  source points.
- Source-rank coverage.
- Determinant-chart Haar pushforward, raw-Haar transport, or source-prior
  transport.
- Jacobian change-of-variables or exact localized residual marginal.
- Normal crossings, pole order, and RLCT extraction.

## Build

Focused build passed from `lean/`:

```text
scripts/lb DLNFibre.DLN.Aoyagi.RetainedPassiveCase2PassiveSelectedEntrySource
```

Full aggregator build passed:

```text
scripts/lb DLNFibre
```

`git diff --check` passed.  `scripts/sorries` reports
`0 sorry, 0 #exit, 0 native_decide, 0 axiom`.

Direct axiom probe for the new theorem reports
`[propext, Classical.choice, Quot.sound]`.

Independent xhigh reviews by `McClintock the 3rd` and `Galileo the 3rd`
passed; see
`review-a2-case2-passive-selected-entry-local-source-readback-domain.md`.

## Nonclaims

This card does not prove source-image equality, source-rank coverage,
determinant-chart Haar pushforward, raw-Haar transport, source-prior
transport, Jacobian transport, exact localized residual marginal, normal
crossings, pole order, or RLCT.
