# Statement Card - A6 Definition 3 Source-Data Eq5 Terminal-Order Bridge

## Lean File

`lean/DLNFibre/DLN/Aoyagi/Theorem2Eq5TerminalOrderBridge.lean`

## Claim

Definition 3 source data plus source-range rank-width hypotheses can produce
the selected-width family and ceiling datum consumed by the supplied Eq5
terminal-order bridge, provided the Eq5 payload is supplied for that produced
`m,data` and uses the same selected cutpoints.

## Lean Names

```text
AoyagiDefinition3SourceData
  .exists_theorem2SuppliedFinalBoundary_of_rankWidth_activePair_ratioCount_suppliedEq5EndpointBlockWidthPayload

AoyagiDefinition3SourceData
  .exists_theorem2SuppliedChartFinalBoundary_of_rankWidth_activePair_ratioCount_suppliedEq5EndpointBlockWidthPayload
```

## Proved

The theorems existentially produce `m` and `data`, then build either

```text
AoyagiTheorem2SuppliedFinalBoundary D L (n+1) H r C m data lambda poleOrder
```

or

```text
AoyagiTheorem2SuppliedChartFinalBoundary
  Cnc L (n+1) H r C m data lambda poleOrder.
```

They also return the selected-width provenance facts from the Definition 3
source-data layer.

## Inputs Kept Explicit

- supplied selected cutpoints `C`;
- source data `Ssrc : AoyagiDefinition3SourceData L (n+1) H r C`;
- source-range rank-width hypothesis;
- Eq5 payload for the produced `m,data`;
- compatibility `P.cut = C`;
- active coordinate and active-ratio lower bound;
- displayed-ratio chart count and all-chart upper bound;
- normal-crossing extraction hypothesis.

## Not Proved

No selected-cutpoint construction, no rank-width theorem from matrix data, no
Eq5 endpoint-family construction, no Lemma 5 exactness proof, no active-ratio
or chart-count theorem, no chart production, no pole order without A0, and no
RLCT extraction.

## Verification

Run:

```text
cd lean && scripts/lb DLNFibre.DLN.Aoyagi.Theorem2Eq5TerminalOrderBridge
cd lean && scripts/lb
cd lean && scripts/sorries
git diff --check
```
