# A2 Active Endpoint Coordinate Linear Equivalence

Date: 2026-07-03.

## Local calculation

The with-following Case 2 endpoint tuple stores the passive fields and two
active `C` blocks.  The active readout map

```text
R : TopologyTuple -> Case2PassiveThetaWithFollowingFactor
```

does the following finite coordinate operations:

- reads the passive fields `A1passive`, `F2`, `A3passive`, `Ctop`, `F3`;
- reads active `C 1` as the charted successor selected-entry center
  coordinates;
- reads active `C 0` as the independent following-factor matrix.

The active writeback map

```text
W : Case2PassiveThetaWithFollowingFactor -> TopologyTuple
```

writes the same fields back into the endpoint tuple slots, putting the
following factor into `C 0` and the center-coordinate matrix into `C 1`.

Every operation is a coordinate projection, product rebracketing,
finite-index reindexing, or matrix entrywise reconstruction.  Hence

```text
R(T + U) = R(T) + R(U),      R(a • T) = a • R(T).
```

The already-proved pointwise identities

```text
R(W z) = z,
W(R T) = T
```

therefore upgrade `R` and `W` from continuous inverse maps to a global
continuous linear equivalence between the ambient endpoint topology-tuple
space and the active with-following coordinate source.

The same linear-equivalence package also gives the generic additive-Haar
restriction comparison.  If `sourceHaar` is an additive Haar measure on the
active coordinate source and `rawHaar` is an additive Haar measure on the
endpoint topology-tuple space, then for any active-coordinate set `Omega`,

```text
map W (sourceHaar.restrict Omega)
  = scalar • rawHaar.restrict (W '' Omega),
```

where

```text
scalar = (map W sourceHaar).addHaarScalarFactor rawHaar.
```

This is only uniqueness of additive Haar measure under the continuous linear
equivalence, followed by restriction compatibility for the measurable
equivalence `W`.

## Boundary

This is a generic Haar-scalar transport theorem, not the endpoint image
identity needed later.  It does not say that `W` preserves a chosen Haar
normalization, does not identify the scalar with `1`, does not identify a
restricted endpoint image measure with determinant-side Haar or weighted Haar,
does not match the image set with the p.13 determinant patch, and does not
prove a Jacobian formula.  Its use is to isolate the next endpoint-image
problem: identify the active-coordinate product reference measure as a
restricted full additive Haar measure and then compose it with selected-entry
change-of-variables plus this explicit-scalar active writeback transport.
