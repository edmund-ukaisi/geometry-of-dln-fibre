# Reproduction - Definition 3 source-rank final handoff

Date: 2026-06-24.

Status: pen-and-paper reproduction before Lean.

## Question

The current Definition 3 final-boundary and Eq5 terminal-order handoffs require
an explicit source-range rank-width hypothesis

```text
forall s, 1 <= s -> s <= L+1 -> r <= H s.
```

The preceding source-range bridge proved this hypothesis from the A2
source-rank stratum when `L = N` and the displayed width function is explicitly
identified with layer dimensions:

```text
H(k+1) = finrank K (W k),  k : Fin(N+1).
```

This slice asks whether the final-boundary and Eq5 handoffs should consume the
source-rank stratum directly, rather than asking the caller to re-supply the
same rank-width conclusion.

## Source Anchors

Aoyagi PDF pp. 8-9 defines the layer widths `H^(s)`, the reduced widths

```text
M^(s) = H^(s) - r,  s = 1,...,L+1,
```

and the selected reduced widths used in Theorem 2.  PDF pp. 11-13 give the
rank-stratum/product-rank setup used by the product-reduction theorem.  The
only source-moving ingredient in this handoff is the elementary fact already
formalized in the preceding bridge: the product rank is bounded by every layer
dimension because the product factors through every layer.

This handoff does not use the normal-crossing extraction theorem; it merely
routes the elementary rank-width consequence into existing final sockets.  The
normal-crossing-to-RLCT extraction boundary remains an explicit supplied A0
hypothesis in those sockets.

## Existing Lean Inputs

The source-rank bridge now provides

```text
paperEndpointFixedBaseSourceRankStratum_sourceRangeRankWidth
```

which proves

```text
forall s, 1 <= s -> s <= N+1 -> r <= H s
```

from

```text
x in paperEndpointFixedBaseSourceRankStratum W B Cedge r rEdge
forall k : Fin(N+1), H(k+1) = finrank K (W k).
```

It also provides

```text
AoyagiDefinition3SourceData.exists_selectedReducedWidthCeilData_of_sourceRankStratum
```

for `S : AoyagiDefinition3SourceData N ell H r C`.

The final-boundary wrappers already proved in `Theorem2FinalAssembly.lean` are

```text
AoyagiDefinition3SourceData.exists_theorem2SuppliedFinalBoundary_of_rankWidth
AoyagiDefinition3SourceData.exists_theorem2SuppliedChartFinalBoundary_of_rankWidth.
```

The Eq5 terminal-order wrappers already proved in
`Theorem2Eq5TerminalOrderBridge.lean` are

```text
AoyagiDefinition3SourceData.exists_theorem2SuppliedFinalBoundary_of_rankWidth_activePair_ratioCount_suppliedEq5EndpointBlockWidthPayload
AoyagiDefinition3SourceData.exists_theorem2SuppliedChartFinalBoundary_of_rankWidth_activePair_ratioCount_suppliedEq5EndpointBlockWidthPayload.
```

All four still ask for the explicit rank-width hypothesis.

## Pen-and-paper Composition

Fix a paper chain with layers `W_0,...,W_N`, base product `B`, and a source
rank-stratum point `x`.

Assume

```text
S : AoyagiDefinition3SourceData N ell H r C
x in paperEndpointFixedBaseSourceRankStratum W B Cedge r rEdge
H(k+1) = dim W_k.
```

By the preceding rank-width theorem,

```text
hr(s) : r <= H(s),  for 1 <= s <= N+1.
```

The existing source-data final-boundary handoff with `L=N` applies to `S` and
`hr`.  It produces selected reduced widths `m`, a Definition 3 ceiling datum
`data`, the final-boundary object, and the selected-width facts:

```text
m = selectedReducedWidths(H,r,C)
m_j = H(C_j)-r
0 <= m_j
ell*m_i < sum_j m_j
m_i <= data.ceilWidth - 1
0 <= selectedWidthNat(i).
```

The chart-certificate final-boundary version is the same composition, with
the extraction hypothesis attached to the supplied chart certificate.

For the Eq5 terminal-order handoff, specialize the existing Eq5 wrapper to
`L=N` and `ell=n+1`.  The same `hr` produced from the source-rank stratum lets
the wrapper first construct `m,data`; the existing Eq5 payload continuation is
then invoked for that produced `m,data`.  The compatibility condition
`P.cut = C` still ties the supplied Eq5 endpoint payload to the same selected
cutpoints as the Definition 3 source data.

Thus the Lean proof is pure composition:

```text
source-rank stratum + dimension convention
  -> source-range rank-width
  -> existing final-boundary/Eq5 rankWidth wrapper.
```

## Lean Shape

Add a leaf final-boundary bridge:

```text
DLNFibre.DLN.Aoyagi.Theorem2SourceRankFinalBridge
```

with

```text
AoyagiDefinition3SourceData.exists_theorem2SuppliedFinalBoundary_of_sourceRankStratum
AoyagiDefinition3SourceData.exists_theorem2SuppliedChartFinalBoundary_of_sourceRankStratum
```

Then add the Eq5-specific leaf bridge:

```text
DLNFibre.DLN.Aoyagi.Theorem2SourceRankEq5Bridge
```

with

```text
AoyagiDefinition3SourceData.exists_theorem2SuppliedFinalBoundary_of_sourceRankStratum_activePair_ratioCount_suppliedEq5EndpointBlockWidthPayload
AoyagiDefinition3SourceData.exists_theorem2SuppliedChartFinalBoundary_of_sourceRankStratum_activePair_ratioCount_suppliedEq5EndpointBlockWidthPayload
```

The final-boundary theorem inputs should use

```text
S : AoyagiDefinition3SourceData N ell H r C
```

and the Eq5 theorem inputs should use

```text
Ssrc : AoyagiDefinition3SourceData N (n+1) H r C.
```

The continuation hypotheses for finite exponent formulas, active ratios,
chart counts, Eq5 payloads, and A0 extraction should remain unchanged except
for replacing `L` by `N`.

## Nonclaims

These handoffs do not construct selected cutpoints or Definition 3 source
data.

They do not prove exact-rank strata are open, that any nearby point belongs to
the source-rank stratum, or that the dimension convention holds automatically.

They do not construct Eq5 endpoint families, prove Lemma 5 exactness, prove
active-ratio lower bounds, prove chart-count/order facts, construct
normal-crossing charts, prove finite exponent formulas, prove pole order, or
prove RLCT.
