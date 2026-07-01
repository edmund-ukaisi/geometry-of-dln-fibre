# Reproduction - A2 p.13 Chart-piece Inverse-scalar Measure Bridge

Date: 2026-07-01.

Status: pen-and-paper check before Lean.  This is scalar bookkeeping after
the p.13 source-set and chart-piece measure bridges.

## Question

For a measurable `chartPiece` contained in the named p.13 source edge-family
set, the existing chart-piece bridge proves

```text
muP13.restrict chartPiece
  = c • (originalEdgeFamilyVolume b).restrict chartPiece,
```

where `c` is the tuple-side full-space Haar scalar

```text
c :=
  (Measure.map (paperEndpointFixedBaseRawOrderMatrixTupleContinuousLinearEquiv W B U0) m)
    .addHaarScalarFactor (originalTupleVolume d).
```

Can we turn this around into a domination/equality with the original volume on
the left?

## Calculation

The scalar `c` is an `ℝ≥0`, not an `ℝ≥0∞`.  Let

```text
L := paperEndpointFixedBaseRawOrderMatrixTupleContinuousLinearEquiv W B U0.
```

Since `m` is an additive Haar measure on raw coordinates and `L` is a
continuous linear equivalence, `Measure.map L m` is an additive Haar measure.
The tuple volume `originalTupleVolume d` is also an additive Haar measure.
Therefore Mathlib's Haar uniqueness scalar is positive:

```text
0 < c.
```

In particular `c ≠ 0`.  For any measures `mu` and `nu`, the elementary scalar
cancellation is:

```text
mu = c • nu  and  c ≠ 0
--------------------------------
nu = c⁻¹ • mu.
```

Indeed,

```text
c⁻¹ • mu
  = c⁻¹ • (c • nu)
  = (c⁻¹ * c) • nu
  = nu.
```

Applying this with

```text
mu := muP13.restrict chartPiece
nu := (originalEdgeFamilyVolume b).restrict chartPiece
```

gives

```text
(originalEdgeFamilyVolume b).restrict chartPiece
  = c⁻¹ • muP13.restrict chartPiece.
```

This should be proved for both p.13 source measures already present in Lean:

```text
Measure.map sourceChart (m.restrict rawSourceSet)
```

and

```text
Measure.map (fun z => sourceChart (topologyTupleEdgeRawOrder z))
  ((m.restrict detChart).withDensity formalProductAbsDet).
```

## Bounded-prior Consequence

If an original edge-family prior density is locally bounded on `chartPiece`,

```text
∀ᵐ E ∂(originalEdgeFamilyVolume b).restrict chartPiece, density E ≤ K,
```

then the existing original-prior bounded-density lemma gives

```text
(originalEdgeFamilyPrior b density).restrict chartPiece
  ≤ ENNReal.ofReal K • (originalEdgeFamilyVolume b).restrict chartPiece.
```

Composing with the inverse-scalar equality gives the consumer-facing
domination

```text
(originalEdgeFamilyPrior b density).restrict chartPiece
  ≤ (ENNReal.ofReal K * ((c⁻¹ : ℝ≥0) : ℝ≥0∞)) • muP13.restrict chartPiece.
```

The density bound is a hypothesis.  This theorem still does not prove that an
original prior is transported from a global original parameter space through
the p.13 chart; it only says that once the prior is written against
`originalEdgeFamilyVolume b` and locally bounded, the scalar chart-piece
measure comparison gives domination by the p.13 chart measure.

## Lean Target

Add a reusable scalar helper to:

```text
lean/DLNFibre/DLN/Aoyagi/LocalMeasureHandoff.lean
```

with content:

```text
measure_eq_inv_smul_of_eq_nnreal_smul
```

Add p.13 corollaries to:

```text
lean/DLNFibre/DLN/Aoyagi/OriginalEdgeFamilyP13SourceMeasureBridge.lean
```

with inverse-scalar equalities for the unweighted and formal-product p.13
measures, plus the formal-product bounded-prior domination variant:

```text
originalEdgeFamilyPrior_restrict_chartPiece_le_smul_map_paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart_withDensity_formalProductAbsDet_restrict_chartPiece
```

## Kill Conditions

- If the scalar is normalized to `1`, the theorem overclaims.
- If the inverse-scalar equality is used outside a supplied measurable
  `chartPiece ⊆ sourceSet`, it overclaims.
- If the prior variant is used without a local density bound against
  `originalEdgeFamilyVolume b`, it overclaims.
- If the theorem is cited as passive-theta source-image containment,
  source-rank coverage, restricted Haar structure, normal crossings, pole
  order, or RLCT extraction, it overclaims.

