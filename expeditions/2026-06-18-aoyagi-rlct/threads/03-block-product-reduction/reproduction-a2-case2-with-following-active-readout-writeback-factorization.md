# A2 Case 2 With-Following Active Readout Writeback Factorization

## Purpose

This note records the finite-coordinate inverse for the active endpoint
readout in the enlarged Case 2 with-following coordinates.  The target
coordinates are charted active coordinates: the center component represents
the already-selected-entry-charted `C 1` block, while the following factor is
the active `C 0` block.

This is not the nonlinear inverse of the selected-entry chart on uncharted
source centers.  It is only the endpoint tuple repacking inverse to the active
readout.

## Calculation

For an endpoint topology tuple `T`, first undo endpoint reindexing:

```text
raw = ofTopologyTuple(T).endpointTransport(e.symm).
```

The active readout extracts:

```text
passive fields = raw passive fields,
y_chart(i) = value(raw.C 1)(residualCoordEquiv.symm i),
F_follow = raw.C 0.
```

The writeback takes charted active coordinates

```text
z = ((passive fields, y_chart), F_follow)
```

and rebuilds raw retained-passive data by setting:

```text
C 0 = F_follow,
C 1 = AoyagiResidualBlockCoordinateIndex.matrix
        (fun c => y_chart (residualCoordEquiv c)),
```

leaving the passive fields unchanged, then endpoint-transports by `e`.

The inverse identities are elementary:

```text
readout(writeback(z)) = z
```

uses `value(matrix f) = f`, while

```text
writeback(readout(T)) = T
```

uses the same `value/matrix` cancellation for `C 1`, direct equality for
`C 0`, and the existing endpoint-transport cancellation theorem.

For the actual endpoint map `Y`, the existing readout calculation gives

```text
readout(Y z) =
  ((z.passive, chartMap pivotNext z.yNext), z.following).
```

Composing with writeback yields the pointwise factorization:

```text
Y z =
  writeback ((z.passive, chartMap pivotNext z.yNext), z.following).
```

## Lean Landing

The formal checkpoint is in:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaCFieldReadout.lean
```

It adds:

```text
endpointTopologyTupleActiveWritebackRawData
endpointTopologyTupleActiveWriteback
endpointTopologyTupleActiveReadout_writeback
endpointTopologyTupleActiveWriteback_readout
case2PassiveThetaWithFollowingFactorEndpointTopologyTuple_eq_activeWriteback_activeSelectedEntryChart
```

The result deliberately stops short of packaging a `LinearEquiv`: the maps are
mathematically finite-coordinate linear repackings, but Lean needs additional
API showing that `ofTopologyTuple` commutes with addition and scalar
multiplication cleanly.  The inverse pair and endpoint factorization are the
part needed for the next determinant-image analysis.

## Boundary

This proves no endpoint-Haar transport, determinant-Haar comparison, raw-map
pushforward, source-prior/original-prior transport, source-image coverage,
normal crossings, pole order, or RLCT.  It only identifies the finite
coordinate factorization of the bare endpoint map through active charted
coordinates.

## Verification

Checked on 2026-07-02 in the `expedition/aoyagi-rlct` worktree with local
Lake commands:

```text
cd lean
env LEAN_NUM_THREADS=3 lake build DLNFibre.DLN.Aoyagi.RetainedPassiveCase2PassiveThetaCFieldReadout
env LEAN_NUM_THREADS=3 lake env lean /tmp/aoyagi_readout_axioms.lean
env LEAN_NUM_THREADS=3 lake build DLNFibre
scripts/sorries
git diff --check
rg -n "sorry|admit|TODO|FIXME|native_decide|#exit|axiom" \
  lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2PassiveThetaCFieldReadout.lean
```

The focused module and full library builds passed.  `scripts/sorries` reported
`0 sorry, 0 #exit, 0 native_decide, 0 axiom`.  The direct axiom probe for all
five new declarations reported exactly `[propext, Classical.choice,
Quot.sound]`.
