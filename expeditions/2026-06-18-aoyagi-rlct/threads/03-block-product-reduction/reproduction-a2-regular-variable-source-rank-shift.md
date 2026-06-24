# Reproduction - A2 Regular-Variable Source-Rank Shift

Date: 2026-06-24.

Status: controller reproduction before Lean implementation.

## Source Anchor

Aoyagi PDF p. 13, after Theorem 3, separates the product-reduction output into
regular block coordinates

```text
C1 - Er,   F2,   F3
```

and the residual singular product.  The regular coordinates contribute

```text
(-r^2 + r(H^(1)+H^(L+1))) / 2
```

to the displayed Theorem 2 lambda formula.  The already formalised finite
shift slice records the corresponding regular-coordinate count as

```text
aoyagiTheorem2RegularVariableCount L H r
```

and proves that shifting Jacobian/prior exponents by that count shifts the
finite exponent minimum by `aoyagiTheorem2RegularTerm L H r`, assuming the
endpoint width bounds

```text
r <= H 1,     r <= H (L+1).
```

## Question

The A2 source-rank boundary now has a source-shaped rank stratum

```text
paperEndpointFixedBaseSourceRankStratum W B Cedge r rEdge
```

and a theorem

```text
paperEndpointFixedBaseSourceRankStratum_sourceRangeRankWidth
```

saying that, if `H(k+1)` is identified with `finrank(W k)`, membership in the
source-rank stratum implies

```text
forall s, 1 <= s -> s <= N+1 -> r <= H s.
```

Therefore it should discharge the two endpoint assumptions needed by the
regular-variable finite shift when `L = N`.

## Derivation

Assume:

```text
hx : x in paperEndpointFixedBaseSourceRankStratum W B Cedge r rEdge
hH : forall k : Fin (N+1), H(k.val+1) = finrank(W k).
```

By the source-range theorem, for every source-layer label `s` with
`1 <= s <= N+1`,

```text
r <= H s.
```

Taking `s = 1` gives

```text
r <= H 1,
```

since `1 <= 1` and `1 <= N+1`.

Taking `s = N+1` gives

```text
r <= H (N+1),
```

since `1 <= N+1` and `N+1 <= N+1`.

These are exactly the endpoint hypotheses in the existing finite shift theorem

```text
D.exponentMinimum_jacobianPriorLossShift_regularVariableCount N H
```

and its chart-certificate version.  Therefore the source-rank stratum implies:

```text
(D.jacobianPriorLossShift regularCount).exponentMinimum
  = D.exponentMinimum + regularTerm,

(D.jacobianPriorLossShift regularCount).exponentOrder
  = D.exponentOrder.
```

Consequently, if the reduced finite exponent data satisfies the reduced
formula obligations

```text
D.exponentMinimum + regularTerm = displayed lambda,
D.exponentOrder = displayed order,
```

then the shifted data satisfies the existing Theorem 2 finite exponent formula
boundary, with the endpoint rank-width assumptions supplied by `hx` and `hH`.

## Nonclaims

- No proof of Aoyagi Theorem 3 as an analytic/RLCT theorem.
- No exact-rank openness.
- No construction of regular-suspension chart coordinates.
- No analytic ideal transport or Aoyagi Lemma 1.
- No normal-crossing chart production.
- No pole-order or RLCT extraction beyond the existing A0 citation boundary.

## Lean Target

Extend `lean/DLNFibre/DLN/Aoyagi/RegularVariableShift.lean` with:

```text
paperEndpointFixedBaseSourceRankStratum_regularVariableEndpointBounds
AoyagiNormalCrossingExponentData.exponentMinimum_jacobianPriorLossShift_regularVariableCount_of_sourceRankStratum
AoyagiNormalCrossingChartCertificate.exponentData_exponentMinimum_jacobianPriorLossShift_regularVariableCount_of_sourceRankStratum
AoyagiTheorem2FiniteExponentFormulaHypothesis.of_regularVariableCountShift_sourceRankStratum
AoyagiTheorem2FiniteExponentFormulaHypothesis.of_chart_regularVariableCountShift_sourceRankStratum
```

These are finite/certificate arithmetic and source-rank provenance only.
