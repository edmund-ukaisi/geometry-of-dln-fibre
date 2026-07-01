# Statement Card - A2 p.13 Chart-piece Inverse-scalar Measure Bridge

## Claim

The p.13 chart-piece source-measure equality can be inverted by the positive
tuple-side Haar scalar.  For any measurable
`chartPiece ⊆ sourceSet`,

```text
muP13.restrict chartPiece
= c • (originalEdgeFamilyVolume b).restrict chartPiece
```

implies

```text
(originalEdgeFamilyVolume b).restrict chartPiece
= c⁻¹ • muP13.restrict chartPiece.
```

The scalar is the same full-space tuple Haar scalar used in the p.13 source-set
bridge.  Positivity comes from Haar uniqueness for `Measure.map L m` and
`originalTupleVolume d`.

## Public Lean Names

```text
measure_eq_inv_smul_of_eq_nnreal_smul
originalEdgeFamilyVolume_restrict_chartPiece_eq_inv_smul_map_paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart_restrict_chartPiece
originalEdgeFamilyVolume_restrict_chartPiece_eq_inv_smul_map_paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart_withDensity_formalProductAbsDet_restrict_chartPiece
originalEdgeFamilyPrior_restrict_chartPiece_le_smul_map_paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart_withDensity_formalProductAbsDet_restrict_chartPiece
```

The bounded-prior theorem states the local density bound explicitly:

```text
∀ᵐ E ∂(originalEdgeFamilyVolume b).restrict chartPiece, density E ≤ K.
```

## Inputs Used

- the two p.13 chart-piece scalar equalities;
- `Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure`;
- `paperEndpointFixedBaseRawOrderMatrixTupleContinuousLinearEquiv`;
- `isAddHaarMeasure_originalTupleVolume`;
- elementary NNReal scalar cancellation for measures.

## Proof Shape

1. Package the general lemma:
   `mu = c • nu` and `c ≠ 0` imply `nu = c⁻¹ • mu`.
2. Instantiate `c` as the tuple-side Haar scalar.
3. Prove `c ≠ 0` from Haar-scalar positivity.
4. Apply the general lemma to the chart-piece equality.
5. For the bounded-prior theorem, combine the existing
   `originalEdgeFamilyPrior_restrict_le_smul_of_ae_le` with the formal-product
   inverse-scalar equality and scalar associativity.

## Nonclaims

This is not source-rank coverage, full source coverage, passive-theta
source-image containment, original-prior transport from a global original
parameter space through the p.13 chart, restricted Haar structure, scalar
normalization to `1`, normal crossings, pole order, or RLCT extraction.

