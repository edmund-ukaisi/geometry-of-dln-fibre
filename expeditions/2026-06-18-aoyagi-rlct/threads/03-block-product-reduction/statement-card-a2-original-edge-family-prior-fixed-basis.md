# Statement Card - A2 Original Edge-Family Prior In Fixed Bases

## Claim

Fixed bases identify continuous edge families with original matrix tuples.
Transporting `originalTupleVolume d` through the tuple-to-edge reconstruction
defines an original edge-family volume whose fixed-basis matrix-coordinate
pushforward is exactly `originalTupleVolume d`.  Locally bounded real prior
densities give the corresponding restricted scalar domination.

Public Lean names:

```text
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

## Inputs Used

- finite-dimensional real vector spaces `V j`;
- fixed bases `b j : Basis (Fin (d j)) ℝ (V j)`;
- the existing tuple-side original measure `originalTupleVolume d`;
- measurable-space, open-measurable, and Borel hypotheses on the continuous
  edge-family type for the measure-map statements;
- a measurable local edge-family piece `s`;
- a local a.e. upper bound on the real prior density.

## Output

The original edge-family volume is:

```text
originalEdgeFamilyVolume b
  : Measure (∀ p : Fin N, V p.castSucc ->L[ℝ] V p.succ)
```

and Lean proves:

```text
Measure.map (edgeFamilyMatrixTuple b) (originalEdgeFamilyVolume b)
  = originalTupleVolume d.
```

The prior and bounded-density domination are:

```text
originalEdgeFamilyPrior b density

(originalEdgeFamilyPrior b density).restrict s
  <= ENNReal.ofReal K • (originalEdgeFamilyVolume b).restrict s.
```

## Proof Shape

The proof is finite basis-coordinate algebra plus measure-map functoriality:

```text
edgeFamilyMatrixTuple b (tupleToEdgeFamily b A) = A
tupleToEdgeFamily b (edgeFamilyMatrixTuple b E) = E

map edgeFamilyMatrixTuple (map tupleToEdgeFamily originalTupleVolume)
  = map (edgeFamilyMatrixTuple ∘ tupleToEdgeFamily) originalTupleVolume
  = map id originalTupleVolume
  = originalTupleVolume.
```

The prior domination is the restricted `withDensity` inequality after applying
`ENNReal.ofReal_le_ofReal` to the supplied real density bound.

## Nonclaims

This is not the missing Aoyagi source-chart transport theorem.  It does not
identify the original edge-family measure with a chart-produced
retained-passive source-image measure, prove chart-image equality, prove
readback domination, prove source-rank coverage, transport Haar/Jacobian
densities, construct normal crossings, compute pole order, or extract an RLCT.
