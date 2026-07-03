# A2 with-following p.13 pointwise right inverse

Source: Aoyagi pp. 10-13 retained-passive source chart and pp. 19-22
selected-entry Case 2 coordinates.  This note is independent of the
quiver-based paper.  It is elementary coordinate reconstruction; it does not
use the cited normal-crossing-to-RLCT theorem.

Let `X` be a retained-passive p.13 source edge family, and let

```text
E    := paperEndpointFixedBaseEdgeMatrixOfReverseEdges(X),
data := sourceReadback(E),
z    := withFollowingReadback(X).
```

The p.13 partial homeomorphism gives

```text
p13Chart(data) = X
```

whenever `X` lies in the named p.13 source edge-family set.  Thus the only
extra calculation needed for the enlarged selected-entry source chart is

```text
withFollowingRetainedData(z) = data.
```

The with-following readback is constructed by transporting `data` back to the
raw two-edge coordinate order, reading the passive fields directly, reading
the active `C 0` block as the free following factor, and applying the inverse
selected-entry center-coordinate map to the active `C 1` block.

The active endpoint readout/writeback API packages this bookkeeping.  If
`T = topologyTuple(data)`, then `endpointTopologyTupleActiveReadout(T)` is the
same passive data, the charted active `C 1` center-coordinate function, and
the active `C 0` following factor.  The readback `z` differs from this readout
only by replacing the charted `C 1` center-coordinate function by its
selected-pivot preimage.

If the selected pivot of `z.1.yNext` is nonzero, then this preimage is in the
domain where the selected-entry chart is a two-sided inverse:

```text
chartMap(pivot, z.1.yNext) = active C1 readout of data.
```

Therefore the active selected-entry chart of `z` is exactly
`endpointTopologyTupleActiveReadout(T)`.  Applying endpoint active writeback
to both sides gives

```text
topologyTuple(withFollowingRetainedData(z))
  = endpointActiveWriteback(activeChart(z))
  = endpointActiveWriteback(endpointActiveReadout(T))
  = T
  = topologyTuple(data).
```

Since `topologyTuple` is injective, `withFollowingRetainedData(z) = data`.
Composing with the p.13 partial homeomorphism right inverse yields

```text
withFollowingSourceChart(withFollowingReadback(X)) = X.
```

Boundary: the statement is pointwise and conditional on `X` being in the
named p.13 source edge-family set and on the selected-entry pivot of the
readback being nonzero.  It does not assert that the pivot condition holds
globally, does not prove local or finite source-rank coverage, and does not
transport source priors, Haar/Jacobian densities, normal crossings, pole
order, or RLCT.
