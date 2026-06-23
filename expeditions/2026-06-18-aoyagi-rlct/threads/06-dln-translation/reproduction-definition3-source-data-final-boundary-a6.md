# Reproduction - Definition 3 source-data final-boundary handoff

Date: 2026-06-23.

Status: reproduced, formalised, and reviewed.

Review:
`review-definition3-source-data-final-boundary-a6.md`.

## Source Anchor

Aoyagi Definition 3, PDF pp. 8-9, supplies selected cutpoints
`S_1,...,S_{ell+1}` and selected reduced widths

```text
m_i = M^(S_i) = H^(S_i) - r.
```

The previous source-data provenance slice packaged this source material as
`AoyagiDefinition3SourceData L ell H r C`, still with selected cutpoints
`C` supplied, and proved that under an explicit source-range rank-width
hypothesis

```text
forall s, 1 <= s -> s <= L+1 -> r <= H s,
```

Lean can existentially produce the selected-width family `m`, a Definition 3
ceiling datum `data`, natural-width rewrites, nonnegativity, strict selected
inequalities, and selected upper bounds.

This slice feeds that produced `m,data` pair into the existing final-boundary
structures.  It does not construct cutpoints or prove any normal-crossing
chart/count obligation.

## Pen-and-Paper Calculation

Start with supplied source data

```text
S : AoyagiDefinition3SourceData L ell H r C
```

and the source-range rank-width hypothesis `hr`.  The already proved
source-data theorem gives

```text
exists m data,
  m = aoyagiSelectedReducedWidths H r C
```

together with:

```text
m_j = (H(C_j)-r : Nat)
0 <= m_j
ell*m_i < sum_j m_j
m_i <= data.ceilWidth - 1
0 <= selectedWidthNat(i).
```

The supplied final-boundary structure needs exactly three fields:

```text
selectedWidths_eq_reduced
extractionHypothesis
finiteExponentFormula
```

The produced equality `m = aoyagiSelectedReducedWidths H r C` fills the first
field.  The A0 extraction field remains the explicitly supplied cited
boundary.  The finite exponent formula field is still supplied, but now as a
continuation in the produced `m,data`:

```text
forall data, m = selectedReducedWidths -> finiteExponentFormula(D,m,data).
```

Thus source data and rank-width provenance produce an existential final
boundary:

```text
exists m data,
  AoyagiTheorem2SuppliedFinalBoundary D L ell H r C m data lambda poleOrder
```

plus the same selected-width provenance facts from the previous slice.  The
chart-certificate version is identical, except that the extraction hypothesis
is `Cnc.ExtractionHypothesis lambda poleOrder` and the finite formula is for
`Cnc.exponentData`.

## Lean Target

In `lean/DLNFibre/DLN/Aoyagi/Theorem2FinalAssembly.lean`, add:

```text
AoyagiDefinition3SourceData.exists_theorem2SuppliedFinalBoundary_of_rankWidth
AoyagiDefinition3SourceData.exists_theorem2SuppliedChartFinalBoundary_of_rankWidth
```

These should return existentially produced `m` and `data`, the corresponding
final-boundary object, and the selected-width provenance facts carried by
`exists_selectedReducedWidthCeilData_of_rankWidth`.

## Boundary

Still supplied:

- selected cutpoints `C`;
- source data `S`;
- source-range rank-width hypothesis `hr`;
- A0 extraction hypothesis;
- finite exponent formula hypothesis for the produced `m,data`.

Not proved: selected-cutpoint existence, rank-width hypotheses from concrete
matrix data, active-ratio lower bounds, chart-count/order facts,
normal-crossing chart production, pole order without A0, or RLCT extraction.
