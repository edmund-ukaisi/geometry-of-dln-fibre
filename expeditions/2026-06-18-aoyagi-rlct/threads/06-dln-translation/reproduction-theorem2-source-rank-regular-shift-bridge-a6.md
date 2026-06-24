# Reproduction - Theorem 2 Source-Rank Regular-Shift Bridge

Date: 2026-06-24.

Status: controller reproduction before Lean implementation.

## Source Anchor

Aoyagi PDF pp. 11-13 proves the product-reduction step and then isolates the
regular block families `C1 - Er`, `F2`, and `F3`; PDF p. 13 records their
contribution to the final lambda formula.  Aoyagi PDF pp. 8-9 state
Definition 3 and the final Theorem 2 formula.

This slice does not reproduce a new analytic theorem.  It composes already
formalised finite/certificate pieces:

- Definition 3 source data plus the A2 source-rank stratum produces selected
  widths and ceiling data.
- The source-rank stratum supplies endpoint rank-width bounds for the
  regular-variable finite shift.
- A supplied reduced finite formula obligation, after adding the regular term,
  produces the shifted finite formula obligation.

## Setup

Fix:

```text
Ssrc : AoyagiDefinition3SourceData N ell H r C
hx   : x in paperEndpointFixedBaseSourceRankStratum W B Cedge r rEdge
hH   : forall k : Fin(N+1), H(k+1)=finrank(W k)
Cnc  : AoyagiNormalCrossingChartCertificate Param R
```

The chart certificate intended for the final socket is the finite
regular-variable shift

```text
Cshift = Cnc.jacobianPriorLossShift
  (aoyagiTheorem2RegularVariableCount N H r).
```

The A0 extraction hypothesis remains explicitly supplied for `Cshift`:

```text
hNC : Cshift.ExtractionHypothesis lambda poleOrder.
```

For each selected-width family `m` and ceiling datum `data` produced from
Definition 3 source data, keep the reduced finite obligations explicit:

```text
hReduced :
  Cnc.exponentData.exponentMinimum + aoyagiTheorem2RegularTerm N H r
    = aoyagiTheorem2Lambda_fromCeilData N ell H r m data

hOrder :
  Cnc.exponentData.exponentOrder = data.theorem2OrderFormula.
```

These are still supplied because the reduced normal-crossing chart production,
active-ratio lower bound, and chart-count theorem are not proved here.

## Derivation

1. From `Ssrc`, `hx`, and `hH`, use the existing source-rank final handoff to
   produce `m` and `data`, together with selected-width provenance

   ```text
   m = aoyagiSelectedReducedWidths H r C.
   ```

2. For the produced `m` and `data`, apply the source-rank regular-shift finite
   constructor

   ```text
   AoyagiTheorem2FiniteExponentFormulaHypothesis
     .of_chart_regularVariableCountShift_sourceRankStratum
   ```

   to `hReduced data selected` and `hOrder data selected`.  The endpoint
   rank-width assumptions inside the finite shift are discharged from `hx` and
   `hH`.

3. The result is a finite exponent formula hypothesis for

   ```text
   Cshift.exponentData.
   ```

4. Combine that with `hNC` and the selected-width provenance using the existing
   chart final boundary structure.  The output is

   ```text
   AoyagiTheorem2SuppliedChartFinalBoundary
     Cshift N ell H r C m data lambda poleOrder.
   ```

The returned side facts are the same selected-width Nat rewrites,
nonnegativity, strict selected inequalities, selected-width upper bounds, and
Nat selected-width nonnegativity already provided by the source-rank final
handoff.

## Nonclaims

- No construction of `Cnc` or `Cshift`.
- No proof that the regular variables form an analytic regular suspension.
- No Aoyagi Lemma 1 or analytic ideal transport.
- No exact-rank openness.
- No active-ratio lower bound or chart-count theorem.
- No normal-crossing chart production.
- No pole-order/RLCT theorem beyond the explicit chart-level extraction
  hypothesis for the shifted certificate.

## Lean Target

Add a narrow bridge, likely in a new file
`lean/DLNFibre/DLN/Aoyagi/Theorem2SourceRankRegularShiftBridge.lean`, with a
chart-final theorem:

```text
AoyagiDefinition3SourceData
  .exists_theorem2SuppliedChartFinalBoundary_of_sourceRankStratum_regularVariableCountShift
```

If useful, also add the non-chart finite-exponent-data analogue with
`AoyagiNormalCrossingExtractionHypothesis` for the shifted exponent data.
