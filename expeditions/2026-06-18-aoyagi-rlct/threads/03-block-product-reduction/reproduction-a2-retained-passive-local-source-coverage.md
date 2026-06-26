# Reproduction - A2 Retained-Passive Local-Source Coverage

Date: 2026-06-26.

Status: reproduced before Lean, then formalised in
`lean/DLNFibre/DLN/Aoyagi/RetainedPassiveLocalSource.lean`.

## Source and Scope

This is the first Lean bridge after
`statement-card-a2-retained-passive-p13-source-chart-coverage-boundary.md`.
It uses only the elementary Aoyagi pp. 10-13 block-reduction chart logic that
has already been formalised in the fixed-base and retained-passive files.

The theorem does not prove exact-rank openness, global source-image equality,
measure pushforward, Jacobian density transport, normal crossings, pole order,
or RLCT extraction.

## Index Convention

Use `M` for the retained-passive Lean parameter.  Then:

```text
vertices: Fin (M + 2)
edges:    Fin (M + 1)
```

If the paper-side notation has `N` edges, then the Lean retained-passive
parameter is `M = N - 1`.

With this convention:

- paper edge `p = 0, ..., N - 1` corresponds to Lean `p : Fin (M + 1)`;
- the last paper edge corresponds to `Fin.last M : Fin (M + 1)`;
- the terminal paper vertex corresponds to `Fin.last (M + 1) : Fin (M + 2)`;
- the terminal convention `F2_N = 0` is Lean
  `F2full (Fin.last (M + 1)) = 0`.

The retained-passive nonredundant data stores:

```text
A1passive : Fin M          -- paper A1_p for p > 0
F2        : Fin (M + 1)    -- paper F2_p for all edges
A3passive : Fin M          -- paper A3_p for p < last
C         : Fin (M + 1)    -- all residual C_p
Ctop, F3  : active endpoint data
```

## Local Source

For a fixed base chain `B`, fixed endpoint complement `U0`, and a continuous
reversed edge family

```text
Cedge : alpha -> forall p : Fin (M + 1),
  reverseVertex W p.castSucc ->L[K] reverseVertex W p.succ,
```

define the fixed-base matrix edge family

```text
Efixed x =
  paperEndpointFixedBaseEdgeMatrixOfReverseEdges W B U0 hU0
    (fun p => (Cedge x p : reverseVertex W p.castSucc ->L[K] reverseVertex W p.succ)).
```

The retained-passive p.13 local source is

```text
{x | Efixed x in sourceRecursiveDetChartSet}
```

where

```text
rho    = Fin (Module.finrank K U0)
kappa' = throughSubspaceEndpointComplementIndex
           (reverseVertex W) (reverseEdge W B) U0.
```

This definition prevents the bad proof pattern
`localSource := sourceStratum`.  The local source is a determinant-chart
preimage with retained-passive coordinates available through the already
proved source readback.

## Predicate Bridge

The fixed-base file already has the predicate

```text
paperEndpointFixedBaseContinuousEdgesRecursiveDetCharts W B U0 hU0 Cedge x.
```

Unfolding shows that this predicate is exactly membership in the retained-
passive local source.  Both sides assert that each transformed edge computed
from the same fixed-base matrix family lies in `identityCornerDetChart`.

The proof is definitional after rewriting:

```text
paperEndpointFixedBaseEdgeMatrixOfReverseEdges ...
  (fun p => Cedge x p)
=
fun q =>
  LinearMap.toMatrix
    (paperEndpointFixedBaseBasis W B U0 hU0 q.castSucc)
    (paperEndpointFixedBaseBasis W B U0 hU0 q.succ)
    (Cedge x q).
```

## Neighborhood Step

At a self-base point,

```text
Cedge x0 = fun p => LinearMap.toContinuousLinearMap (reverseEdge W B p),
```

the fixed-base theorem

```text
paperEndpointFixedBaseContinuousEdges_recursiveBprev_mem_nhds_transformed_identityCornerDetChart
```

gives a neighborhood of `x0` on which the recursive determinant charts hold.
Using the predicate bridge, the retained-passive local source is therefore a
neighborhood of `x0`.

By `mem_nhds_iff`, choose an open set `Ulocal` with

```text
x0 in Ulocal
Ulocal subset retainedPassiveP13LocalSource.
```

The nontrivial content is the ambient neighborhood statement for the
determinant-chart preimage.  Then, for any source-rank stratum,

```text
Ulocal inter sourceStratum subset
  Ulocal inter retainedPassiveP13LocalSource
```

follows immediately from the subset field.  This is the coverage shape needed
by the existing local-measure consumer, with a nontrivial chart-tied
`localSource`; it is not a source-rank openness theorem.

## Lean Names

```text
paperEndpointFixedBaseRetainedPassiveP13LocalSource
mem_paperEndpointFixedBaseRetainedPassiveP13LocalSource_iff_recursiveDetCharts
paperEndpointFixedBaseRetainedPassiveP13LocalSource_mem_nhds_of_selfBase
exists_open_paperEndpointFixedBaseRetainedPassiveP13LocalSource_coverage_of_selfBase
```

## Nonclaims

The theorem does not show that the source-rank stratum is open.  It does not
show that the retained-passive chart covers a whole rank stratum globally.  It
does not provide measurability of the local source, residual integrability,
loss comparison, density bounds, a measure pushforward, a Jacobian theorem,
normal crossings, pole order, or RLCT extraction.
