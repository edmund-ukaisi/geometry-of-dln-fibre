# Reproduction - Theorem 2 rank-width regular-shift bridge

Status: formalised and xhigh checked.

## Source Anchor

Aoyagi PDF pp. 8-9 state Definition 3 and Theorem 2.  Aoyagi PDF p. 13
separates the regular block-entry contribution after the product-reduction
step.  This slice composes already formalised finite pieces; it does not add a
new analytic theorem.

## Setup

Fix Definition 3 source data and source-range rank-width:

```text
Ssrc : AoyagiDefinition3SourceData L ell H r C,
hr   : forall s, 1 <= s -> s <= L+1 -> r <= H s.
```

For each selected-width family `m` and ceiling datum `data` produced from
`Ssrc`, keep the reduced finite formula obligations explicit:

```text
hminimum :
  D.exponentMinimum + aoyagiTheorem2RegularTerm L H r
    = aoyagiTheorem2Lambda_fromCeilData L ell H r m data,

horder :
  D.exponentOrder = data.theorem2OrderFormula.
```

Let the shifted exponent datum be

```text
Dshift = D.jacobianPriorLossShift
  (aoyagiTheorem2RegularVariableCount L H r).
```

The A0 extraction hypothesis remains explicitly supplied for `Dshift`:

```text
hNC : AoyagiNormalCrossingExtractionHypothesis Dshift lambda poleOrder.
```

The chart-certificate version replaces `D` by `Cnc.exponentData` and uses the
shifted chart certificate

```text
Cnc.jacobianPriorLossShift
  (aoyagiTheorem2RegularVariableCount L H r).
```

## Derivation

1. From `Ssrc` and `hr`, the existing Definition 3 source-data final handoff
   produces `m,data` and selected-width side facts.

2. For the produced `m,data`, the rank-width regular-shift finite constructor
   gives

   ```text
   AoyagiTheorem2FiniteExponentFormulaHypothesis
     Dshift L ell H r m data.
   ```

   The constructor uses `hr` only through the endpoint projections
   `r <= H 1` and `r <= H (L+1)`.

3. Combining that finite formula hypothesis with the supplied extraction
   hypothesis for `Dshift` yields

   ```text
   AoyagiTheorem2SuppliedFinalBoundary
     Dshift L ell H r C m data lambda poleOrder.
   ```

4. The chart version uses the same proof with
   `AoyagiTheorem2SuppliedChartFinalBoundary` and the shifted chart
   extraction hypothesis.

## Nonclaims

- No selected cutpoints or Definition 3 source data are constructed.
- No regular-suspension chart is constructed.
- No analytic ideal transport, Aoyagi Lemma 1, or regular-coordinate
  additivity theorem is proved.
- No reduced normal-crossing certificate, active-ratio lower bound, or
  chart-count theorem is proved.
- No pole-order/RLCT theorem is proved independently of the supplied shifted
  A0 extraction hypothesis.
