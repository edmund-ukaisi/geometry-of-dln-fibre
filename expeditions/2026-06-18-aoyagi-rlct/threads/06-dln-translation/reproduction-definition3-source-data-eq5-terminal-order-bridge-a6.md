# Reproduction - Definition 3 source-data Eq5 terminal-order bridge

Date: 2026-06-23.

Status: reproduced before Lean implementation.

## Source Anchor

Aoyagi Definition 3, PDF pp. 8-9, supplies selected cutpoints and selected
reduced widths.  Theorem 2, PDF pp. 8-9, uses the resulting ceiling datum in
the displayed lambda and order formula.  Aoyagi Lemma 5, PDF pp. 24-27,
supplies the terminal finite count that should become the displayed order
formula.

The existing Lean slices already separate these pieces:

```text
AoyagiDefinition3SourceData
  -> exists m,data with m = aoyagiSelectedReducedWidths H r C

AoyagiLemma5SuppliedEq5EndpointBlockWidthOrderPayload data TC
  -> TC.terminalMinimumLabels.card = data.theorem2OrderFormula
```

This slice composes them without proving new source content.

## Calculation

Start with source data for fixed selected cutpoints:

```text
Ssrc : AoyagiDefinition3SourceData L (n+1) H r C.
```

Under the source-range rank-width hypothesis,

```text
forall s, 1 <= s -> s <= L+1 -> r <= H s,
```

the Definition 3 source-data theorem produces

```text
exists m data,
  hm : m = aoyagiSelectedReducedWidths H r C
```

plus the selected-width provenance facts:

```text
m_j = (H(C.cut j)-r : Nat)
0 <= m_j
(n+1)*m_i < sum_j m_j
m_i <= data.ceilWidth - 1
0 <= aoyagiSelectedWidthNat (n+1) m i.
```

For the produced `m,data`, assume an Eq5 terminal-order package:

```text
TC : AoyagiLemma5SuppliedTerminalCandidateFamily ...
P  : AoyagiLemma5SuppliedEq5EndpointBlockWidthOrderPayload data TC
```

with the explicit cutpoint compatibility

```text
P.cut = C.
```

The existing Eq5 bridge wants selected-width provenance over `P.cut`:

```text
m = aoyagiSelectedReducedWidths H r P.cut.
```

This follows by rewriting `hm` along `P.cut = C`.  The already-landed Eq5
bridge then consumes the active-ratio and displayed-ratio chart-count
certificates:

```text
ratioAt p = aoyagiTheorem2Lambda_fromCeilData L (n+1) H r m data

forall active p',
  aoyagiTheorem2Lambda_fromCeilData L (n+1) H r m data <= ratioAt p'

countInChartAtRatio displayedLambda c = TC.terminalMinimumLabels.card

forall c',
  countInChartAtRatio displayedLambda c' <= TC.terminalMinimumLabels.card.
```

The output is an existential final boundary using the original Definition 3
cutpoints `C`, since the constructed boundary over `P.cut` is rewritten back
along `P.cut = C`.

## Lean Shape

Add source-data wrappers in
`lean/DLNFibre/DLN/Aoyagi/Theorem2Eq5TerminalOrderBridge.lean`:

```text
AoyagiDefinition3SourceData
  .exists_theorem2SuppliedFinalBoundary_of_rankWidth_activePair_ratioCount_suppliedEq5EndpointBlockWidthPayload

AoyagiDefinition3SourceData
  .exists_theorem2SuppliedChartFinalBoundary_of_rankWidth_activePair_ratioCount_suppliedEq5EndpointBlockWidthPayload
```

The callback for Eq5 data is indexed by the produced `m,data`; this avoids
assuming uniqueness of the Definition 3 ceiling datum.

## Nonclaims

- No construction of selected cutpoints.
- No proof of the source-range rank-width hypothesis from matrix data.
- No construction of Eq5 endpoint families.
- No source proof of Lemma 5 exactness.
- No active-ratio lower-bound theorem.
- No displayed-ratio chart-count theorem.
- No normal-crossing chart production, coverage, or transition regularity.
- No pole-order or RLCT theorem beyond the existing explicit
  normal-crossing extraction hypothesis.
