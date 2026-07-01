# Statement Card - A2 Original Edge-Family Raw-Order Bridge

## Claim

Retained-passive raw-order tuple coordinates are globally linearly equivalent
to original matrix tuple coordinates after edgewise finite row/column
reindexing.  The map is:

```text
y ↦ fun p =>
  Matrix.reindex (e p.succ) (e p.castSucc)
    (edgeFamilyOfRawOrderTuple y p).
```

For the p.13 endpoint bases, the canonical specialization uses

```text
e j := Fintype.equivFin
  (Fin (finrank U0) ⊕ throughSubspaceEndpointComplementIndex ... j).
```

On `topologyTupleRawOrderSourceRecursiveDetChartSet`, the original
edge-family coordinate readout of the public p.13 raw-order source chart
equals this raw-order matrix tuple readout.

## Public Lean Names

```text
edgeFamilyTupleReindexLinearEquiv
edgeFamilyTupleReindexLinearEquiv_apply
edgeFamilyTupleReindexLinearEquiv_symm_apply
rawOrderMatrixTuple
rawOrderMatrixTuple_apply
rawOrderMatrixTupleLinearEquiv
rawOrderMatrixTupleLinearEquiv_apply
continuous_edgeFamilyTupleReindex
continuous_edgeFamilyTupleReindex_symm
edgeFamilyTupleReindexContinuousLinearEquiv
rawOrderMatrixTupleContinuousLinearEquiv
paperEndpointFixedBaseRawOrderMatrixTupleLinearEquiv
paperEndpointFixedBaseRawOrderMatrixTupleLinearEquiv_apply
paperEndpointFixedBaseRawOrderMatrixTupleContinuousLinearEquiv
edgeFamilyMatrixTuple_p13Basis_reindex_rawOrderSourceChart_eq_rawOrderMatrixTuple
edgeFamilyMatrixTuple_p13FinBasis_rawOrderSourceChart_eq_rawOrderMatrixTuple
```

## Inputs Used

- retained-passive raw-order tuple and edge-family block APIs;
- finite equivalences `e j : ρ ⊕ κ' j ≃ Fin (d j)`;
- `Matrix.reindex` as a linear equivalence;
- continuity of the raw block reassembly/readout maps;
- for the p.13 source-chart specialization, membership in
  `topologyTupleRawOrderSourceRecursiveDetChartSet`;
- Aoyagi's p.13 fixed endpoint bases and their canonical `Fin (card I_j)`
  reindexing.

## Output

The full-space raw coordinate readout is a linear and continuous-linear
equivalence:

```text
TopologyTuple ρ κ' ℝ ≃L[ℝ] Tuple (k := ℝ) d.
```

The p.13 source-chart theorem is pointwise:

```text
edgeFamilyMatrixTuple (paperEndpointFixedBaseFinBasis W B U0 hU0)
  (paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart W B U0 hU0 y)
=
rawOrderMatrixTuple (fun j => Fintype.equivFin ...) y
```

under the raw-order source-recursive determinant-chart hypothesis on `y`.

## Proof Shape

First use the existing block equivalence

```text
edgeFamilyRawOrderTuple : EdgeFamilyTuple ρ κ' ℝ ≃ₗ[ℝ] TopologyTuple ρ κ' ℝ
```

and compose its inverse with edgewise `Matrix.reindex`.  Continuity follows
from the existing continuous raw reassembly/readout theorems and entrywise
continuity of matrix `submatrix`.  The p.13 source-chart theorem is a rewrite
of the previously proved fixed-basis p.13 coordinate readout theorem.

## Nonclaims

This is an ambient coordinate equivalence and a chart-domain pointwise readout
theorem. It does not prove that restricted determinant-chart or source-chart
measures are Haar. It does not prove equality, domination, or scalar
comparison between chart-produced source-image measures and
`originalEdgeFamilyVolume`. It does not prove a Jacobian formula, normal
crossings, pole order, or RLCT extraction.
