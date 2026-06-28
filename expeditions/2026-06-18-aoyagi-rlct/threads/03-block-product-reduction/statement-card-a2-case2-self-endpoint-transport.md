# Statement card - A2 Case 2 self-endpoint transport

## Claim

In the self-endpoint specialization

```text
tau = Case2ResidualColIndex n S (J + 1),
```

the Case 2 endpoint-transported fixed-base source-family theorem no longer
needs an explicit

```text
eNext : tau ~= Case2ResidualColIndex n S (J + 1).
```

The theorem uses `Equiv.refl _` for that endpoint.

## Lean Target

File:

```text
lean/DLNFibre/DLN/Aoyagi/RetainedPassiveCase2LocalJacobianMeasure.lean
```

Target name:

```lean
PaperEndpointFixedBaseRegularCoordinateSourceData.retainedPassiveP13LocalSource_mem_and_sourceReadback_residualFactorProduct_eq_matrix_of_case2EndpointTransport_selfEndpoint_sourceEdgeFamilyOfData
```

## Proof Basis

Instantiate the existing supplied-equivalence theorem

```lean
retainedPassiveP13LocalSource_mem_and_sourceReadback_residualFactorProduct_eq_matrix_of_case2EndpointTransport_sourceEdgeFamilyOfData
```

at `tau := Case2ResidualColIndex n S (J + 1)` and `eNext := Equiv.refl _`.

## Nonclaims

This is finite endpoint plumbing only.  It does not prove `hTau`, construct
fixed-base endpoint equivalences, prove endpoint provenance or label
preservation, compare source priors or Jacobians, prove normal crossings,
compute pole order, or extract RLCT.

## Status

Sorry-free, focused build passed, and reviewed PASS by xhigh `Maxwell` in
`review-a2-case2-self-endpoint-transport.md`.
