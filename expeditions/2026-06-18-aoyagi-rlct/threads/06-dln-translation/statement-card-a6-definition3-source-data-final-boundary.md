# Statement card - A6 Definition 3 source-data final-boundary handoff

## Lean Artifact

File:

- `lean/DLNFibre/DLN/Aoyagi/Theorem2FinalAssembly.lean`

Names:

- `AoyagiDefinition3SourceData.exists_theorem2SuppliedFinalBoundary_of_rankWidth`
- `AoyagiDefinition3SourceData.exists_theorem2SuppliedChartFinalBoundary_of_rankWidth`

## Claim

Definition 3 source data plus an explicit source-range rank-width hypothesis
produce the selected-width family and ceiling datum needed by the supplied
Theorem 2 final-boundary structures.

## Inputs Kept Explicit

- supplied selected cutpoints `C`;
- supplied source data `S : AoyagiDefinition3SourceData L ell H r C`;
- source-range rank-width hypothesis
  `forall s, 1 <= s -> s <= L+1 -> r <= H s`;
- A0 extraction hypothesis;
- finite exponent formula hypothesis for the produced `m,data`.

## Proved

The theorems existentially produce `m` and `data` such that:

```text
AoyagiTheorem2SuppliedFinalBoundary D L ell H r C m data lambda poleOrder
```

or, for a chart certificate,

```text
AoyagiTheorem2SuppliedChartFinalBoundary Cnc L ell H r C m data lambda poleOrder.
```

They also return the selected-width provenance facts:

```text
m = aoyagiSelectedReducedWidths H r C
m_j = (H(C.cut j)-r : Nat)
0 <= m_j
ell*m_i < sum_j m_j
m_i <= data.ceilWidth - 1
0 <= selectedWidthNat(i).
```

## Not Proved

No selected-cutpoint construction, no rank-width theorem from matrix data, no
finite exponent formula proof, no active-ratio or chart-count proof, no chart
production, no pole order without A0, and no RLCT extraction.

## Review

Xhigh review passed.  Review artifact:
`review-definition3-source-data-final-boundary-a6.md`.
