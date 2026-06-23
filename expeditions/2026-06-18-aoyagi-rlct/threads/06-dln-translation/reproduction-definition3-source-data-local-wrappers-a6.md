# Reproduction - Definition 3 source-data local wrappers

Date: 2026-06-23.

Status: reproduced, formalised, and reviewed.

Review:
`review-definition3-source-data-local-wrappers-a6.md`.

## Source Anchor

Aoyagi Definition 3, PDF pp. 8-9, supplies selected cutpoints
`S_1,...,S_{ell+1}` and the selected reduced widths

```text
m_i = M^(S_i) = H^(S_i) - r.
```

It also includes the strict selected-width inequality

```text
ell * M^(S_i) < sum_j M^(S_j)
```

for each selected index.  Earlier Lean work packaged this source information
as

```text
AoyagiDefinition3SourceData L ell H r C
```

where `C` is still a supplied selected-cutpoint family.  This slice only
routes that already packaged strict inequality into the local Definition 3 /
Lemma 5 arithmetic wrappers.  It does not construct the cutpoints.

## Pen-and-Paper Calculation

Let

```text
m = aoyagiSelectedReducedWidths H r C.
```

Unfolding the definition gives

```text
m_i = aoyagiReducedWidthInt H r (C.cut i).
```

The `selected_strict` field of `AoyagiDefinition3SourceData` is exactly

```text
ell * aoyagiReducedWidthInt H r (C.cut i)
  < sum_j aoyagiReducedWidthInt H r (C.cut j).
```

Therefore, after the definitional rewrite `m_i =
aoyagiReducedWidthInt H r (C.cut i)`, the same field supplies

```text
ell * m_i < sum_j m_j.
```

The existing `AoyagiDefinition3CeilData` wrappers require precisely this
strict selected inequality:

```text
selectedWidth_le_pred_of_sourceSelectedInequality
htildeLowerNat_add_one_labelBounds_of_sourceSelectedInequality
lemma5Eq4_localData_of_sourceSelectedInequality
lemma5Eq5_labelBounds_of_sourceSelectedInequality
lemma5Eq3_localData_of_sourceSelectedInequality_and_slack
```

Thus source data plus a ceiling datum for the selected reduced widths can
feed those wrappers without carrying a separate `hsource` argument.

If we also supply the source-range rank-width hypothesis

```text
forall s, 1 <= s -> s <= L+1 -> r <= H s,
```

then the already supplied cutpoint bounds in `AoyagiDefinition3SourceData`
give `r <= H(C.cut j)` for each selected cutpoint.  Therefore the selected
reduced widths can also be read in natural-width form:

```text
m_j = (H(C.cut j)-r : Nat)
```

coerced to integers, and are nonnegative.  This packages the exact
selected-width provenance needed by the final socket, while keeping the
rank-width hypothesis explicit.

## Lean Target

In `lean/DLNFibre/DLN/Aoyagi/Definition3Bridge.lean`, add source-data
wrappers in namespace `AoyagiDefinition3SourceData`:

```text
selected_strict_selectedReducedWidths
selectedWidth_le_pred_of_ceilData
htildeLowerNat_add_one_labelBounds_of_ceilData
lemma5Eq4_localData_of_ceilData
lemma5Eq5_labelBounds_of_ceilData
lemma5Eq3_localData_of_ceilData_and_slack
exists_selectedReducedWidthCeilData_of_rankWidth
```

Each theorem should have

```text
S : AoyagiDefinition3SourceData L ell H r C
data : AoyagiDefinition3CeilData ell (aoyagiSelectedReducedWidths H r C)
```

as inputs and then call the existing `AoyagiDefinition3CeilData` theorem with
the strict inequality projected from `S`.

The final aggregator also takes the explicit source-range rank-width
hypothesis and returns:

```text
exists m data,
  m = aoyagiSelectedReducedWidths H r C
  and natural-width rewrites for all selected widths
  and selected-width nonnegativity
  and the strict selected inequality
  and m_i <= data.ceilWidth - 1
  and Nat-indexed selected-width nonnegativity.
```

## Boundary

This slice removes only a duplicated local hypothesis.  It does not prove
existence or uniqueness of selected cutpoints, does not prove the nonselected
Definition 3 inequalities from dimensions, does not prove rank-width
hypotheses, does not prove Lemma 5 coverage/no-extra exactness, and does not
construct normal-crossing charts, pole order, or RLCT extraction.
