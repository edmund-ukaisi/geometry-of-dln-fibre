# Reproduction - Theorem 2 supplied regular-suspension final bridge

Date: 2026-06-24.

Status: reproduced before Lean implementation.

## Source Anchor

Aoyagi PDF pp. 8-9 state Definition 3 and Theorem 2.  Aoyagi PDF p. 13
separates the regular block-entry contribution after the product-reduction
step.  This slice is only a handoff between already formalised boundary
interfaces:

- Definition 3 source-data provenance supplies the selected-width family
  `m` and ceiling datum `data`;
- the supplied regular-suspension boundary supplies an actual full chart
  certificate `Cfull`;
- normal-crossing extraction is applied to `Cfull`, not to a reduced chart
  followed by adding the regular term.

## Setup

Fix Definition 3 source data and source-range rank-width:

```text
Ssrc : AoyagiDefinition3SourceData L ell H r C,
hr   : forall s, 1 <= s -> s <= L+1 -> r <= H s.
```

Fix a supplied regular-suspension certificate:

```text
Sreg : AoyagiSuppliedRegularSuspensionCertificate
  Cred Cfull regularCount
  RegularChartSource RegularIdealTransport RegularCoverage
  RegularJacobianCompatible lambda poleOrder.
```

This includes:

```text
Cfull.ExtractionHypothesis lambda poleOrder
```

and the finite exponent equality:

```text
Cfull.exponentData =
  Cred.exponentData.jacobianPriorLossShift regularCount.
```

Assume the supplied regular count is Aoyagi's p. 13 regular-variable count:

```text
regularCount = aoyagiTheorem2RegularVariableCount L H r.
```

For each selected-width family `m` and ceiling datum `data` produced from
`Ssrc`, keep the reduced finite formula obligations explicit:

```text
Cred.exponentData.exponentMinimum + aoyagiTheorem2RegularTerm L H r
  = aoyagiTheorem2Lambda_fromCeilData L ell H r m data,

Cred.exponentData.exponentOrder = data.theorem2OrderFormula.
```

## Derivation

1. From `Ssrc` and `hr`, the existing Definition 3 source-data handoff
   produces `m,data` and selected-width side facts:

   ```text
   m = aoyagiSelectedReducedWidths H r C,
   m_j = H(C_j)-r,
   0 <= m_j,
   ell*m_i < sum_j m_j,
   m_i <= data.ceilWidth - 1.
   ```

2. The endpoint bounds `r <= H 1` and `r <= H (L+1)` follow from `hr`.

3. The supplied regular-suspension certificate converts the reduced finite
   min/order equalities into a finite formula hypothesis for `Cfull`:

   ```text
   AoyagiTheorem2FiniteExponentFormulaHypothesis
     Cfull.exponentData L ell H r m data.
   ```

4. Combining that finite formula with `Cfull.ExtractionHypothesis` yields

   ```text
   AoyagiTheorem2SuppliedChartFinalBoundary
     Cfull L ell H r C m data lambda poleOrder.
   ```

This final boundary is for `Cfull` exactly.  It is not a boundary for
`Cred.jacobianPriorLossShift regularCount`.

## Source-rank Variant

The source-rank-stratum variant replaces `hr` by:

```text
x in paperEndpointFixedBaseSourceRankStratum W B Cedge r rEdge,
H(k+1) = finrank(W k).
```

The already formalised source-rank bridge derives the source-range rank-width
hypothesis `hr`, and the proof delegates to the rank-width handoff.

## Nonclaims

- No selected cutpoints or Definition 3 source data are constructed.
- No construction of the full regular-suspension chart `Cfull`.
- No proof of the abstract source, ideal-transport, coverage, or Jacobian
  predicates in the supplied regular-suspension boundary.
- No analytic ideal transport, Aoyagi Lemma 1, or regular-coordinate
  additivity theorem.
- No reduced normal-crossing certificate production, active-ratio lower bound,
  or chart-count theorem.
- No pole-order/RLCT theorem beyond the supplied extraction hypothesis for
  `Cfull`.
