# Reproduction - A2 retained-passive source-edge-family pre-measure inputs

Date: 2026-06-28.

Status: reproduced; Lean target selected and proved.

## Target

Specialize the fixed-base retained-passive pre-measure input theorem to the
canonical source edge-family map attached to retained-passive coordinate data:

```text
sourceChart y =
  paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilyOfData
    W B U₀ hU₀ (retainedData y).
```

The expected conclusion is the same pair of source-side inputs as before:

```text
sourceChart y ∈ paperEndpointFixedBaseRetainedPassiveP13LocalSource ...

residualFactorProduct (sourceReadback E(y)).C
  = selected-entry center-coordinate matrix.
```

This specialization should not require a separate edge-realization hypothesis,
because the source family is defined from the retained-passive datum itself.

## Calculation

Let

```text
EdgeFamily =
  ∀ p : Fin (M + 1), reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ

Cedge : EdgeFamily → EdgeFamily
Cedge E = E
```

and define

```text
sourceChart y =
  paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilyOfData
    W B U₀ hU₀ (retainedData y).
```

The previously proved fixed-base pre-measure input theorem applies once we
supply, for every `y`, the realization identity

```text
paperEndpointFixedBaseEdgeMatrixOfReverseEdges W B U₀ hU₀
  (fun p => sourceChart y p)
  = (retainedData y).edgeMatrix.
```

This is exactly

```text
paperEndpointFixedBaseEdgeMatrixOfReverseEdges_retainedPassiveP13SourceEdgeFamilyOfData_eq
```

after unfolding the definition of `sourceChart`.

Therefore the earlier theorem gives:

1. local-source membership, by rewriting the fixed-base edge matrix to
   `(retainedData y).edgeMatrix` and applying the supplied determinant-chart
   proof `hdet y`;
2. the source-readback residual-factor product identity, by the
   source-readback inverse bridge and the supplied stored-data factor identity
   `hdataFactor y`.

No additional determinant, inverse, measure, density, or analytic calculation is
introduced in this specialization.

Lean endpoint:

```text
PaperEndpointFixedBaseRegularCoordinateSourceData.retainedPassiveP13LocalSource_mem_and_sourceReadback_residualFactorProduct_eq_matrix_of_sourceEdgeFamilyOfData
```

## Boundary Checks

- If `center` is empty, the hypothesis `pivot : center` is impossible, so there
  is no extra empty-center case to discharge.
- If `center` has one point, the argument is unchanged; the selected-entry
  matrix readout is carried by the supplied `hdataFactor`.
- No nonzero pivot, local inverse, measure support, Jacobian, normal-crossing,
  pole-order, or RLCT hypothesis is used.
- The result depends on `hdet` and `hdataFactor`; it removes only the separate
  `hedge` hypothesis for this specific source family.

## Proved / Assumed / Cited / Deferred

**Proved by this reproduction.** The canonical fixed-base source edge-family
map attached to retained-passive coordinate data supplies local-source
membership and the source-readback selected-entry residual-factor matrix input.

**Assumed.** Determinant-chart proofs `hdet`; stored-data residual-factor
readout `hdataFactor`; finite-dimensional fixed-base endpoint hypotheses; and
the selected-entry residual-coordinate equivalence.

**Cited.** None.

**Deferred.** Endpoint transport of `edgeMatrix` and `sourceReadback`; fixed-base
realization for endpoint-transported explicit Case 2 data; original source-prior
pushforward; Jacobian density comparison; normal crossings; pole order; and
RLCT.
