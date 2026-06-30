# Reproduction - A2 Original Edge-Family Prior In Fixed Bases

Date: 2026-06-30.

Status: pen-and-paper check before Lean. This is a fixed-basis transport of
the original tuple measure to continuous edge families, not a source-chart
transport theorem.

## Question

Aoyagi's p.13 source variables are edge maps written in fixed bases.  After
the expedition has named the original tuple-coordinate volume on
`Tuple (k := ℝ) d`, can we put the same original volume on the continuous
edge-family type

```text
EdgeFamily := ∀ p : Fin N, V p.castSucc ->L[ℝ] V p.succ
```

without defining it as an Aoyagi source-chart pushforward?

## Calculation

Fix bases

```text
b j : Basis (Fin (d j)) ℝ (V j).
```

Define the matrix-coordinate map

```text
M_b(E) p = LinearMap.toMatrix (b p.castSucc) (b p.succ) (E p)
```

from continuous edge families to `Tuple (k := ℝ) d`.  Define the reconstruction
map

```text
T_b(A) p =
  LinearMap.toContinuousLinearMap
    (Matrix.toLin (b p.castSucc) (b p.succ) (A p)).
```

For each edge `p`, the fixed-basis matrix/linear-map equivalence gives

```text
M_b(T_b(A)) p = A p,
T_b(M_b(E)) p = E p.
```

Thus `M_b ∘ T_b = id` on tuple coordinates and `T_b ∘ M_b = id` on edge
families.  Both maps are continuous because fixed-basis matrix coordinates of
continuous linear maps are continuous, and finite-dimensional matrix-to-linear
reconstruction is continuous.

Define the edge-family original volume by transport from tuple volume:

```text
originalEdgeFamilyVolume b := Measure.map T_b (originalTupleVolume d).
```

Then

```text
Measure.map M_b (originalEdgeFamilyVolume b)
  = Measure.map (M_b ∘ T_b) (originalTupleVolume d)
  = Measure.map id (originalTupleVolume d)
  = originalTupleVolume d.
```

For a real density `rho : EdgeFamily -> ℝ`, define

```text
originalEdgeFamilyPrior b rho
  := (originalEdgeFamilyVolume b).withDensity
       (fun E => ENNReal.ofReal (rho E)).
```

If `rho <= K` almost everywhere with respect to
`(originalEdgeFamilyVolume b).restrict s`, then

```text
(originalEdgeFamilyPrior b rho).restrict s
  <= ENNReal.ofReal K • (originalEdgeFamilyVolume b).restrict s.
```

This is the same restricted with-density calculation used for tuple priors.

## Source Fidelity

Aoyagi p.13 works with fixed bases and edge maps/matrices in the local
product-reduction chart.  The calculation above is only the finite
linear-algebra identification between edge maps and their fixed-basis
matrices.  It does not assert that Aoyagi's retained-passive chart image has
this measure, or that the chart-produced Jacobian measure equals this
original measure.

## Lean Target

Add:

```text
lean/DLNFibre/DLN/Aoyagi/OriginalEdgeFamilyPrior.lean

edgeFamilyMatrixTuple
tupleToEdgeFamily
edgeFamilyMatrixTuple_tupleToEdgeFamily
tupleToEdgeFamily_edgeFamilyMatrixTuple
continuous_edgeFamilyMatrixTuple
continuous_tupleToEdgeFamily
measurable_edgeFamilyMatrixTuple
measurable_tupleToEdgeFamily
originalEdgeFamilyVolume
originalEdgeFamilyVolume_map_edgeFamilyMatrixTuple
originalEdgeFamilyPrior
originalEdgeFamilyPrior_restrict_le_smul_of_ae_le
```

## Nonclaims

No theorem identifies `originalEdgeFamilyVolume` with a retained-passive or
selected-entry chart-produced source-image measure.  No theorem proves
chart-piece equality, readback domination, source-rank coverage, Haar/Jacobian
transport, normal crossings, pole order, or RLCT extraction.
