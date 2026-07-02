# Reproduction - A6 Definition 3 `L=2` Pairwise-Distinct Rank-Width Removal

Date: 2026-07-02.

Status: formalised; xhigh review passed.

## Source Anchor

Aoyagi Definition 3, PDF pp. 8-9, defines selected source cutpoints and the
finite inequalities for the selected reduced widths.  This slice is only the
`L=2` pairwise-distinct finite classification already formalised in
`reproduction-definition3-l-eq-two-pairwise-distinct-classification-a6.md`;
it removes a now-stale rank-width input from that classifier.

## Existing Statement

The existing theorem

```text
AoyagiDefinition3SourceData.exists_sourceData_iff_allSourceStrict_of_L_eq_two_rankWidth_pairwiseDistinct
```

assumes pairwise distinctness of the three reduced widths and an explicit
source-range rank-width hypothesis

```text
hr : forall s, 1 <= s -> s <= 3 -> r <= H s.
```

It proves that Definition 3 source-data existence is equivalent to the three
all-source strict inequalities

```text
2 * M^(s) < M^(1) + M^(2) + M^(3),    s = 1,2,3.
```

## Calculation

For the forward implication, assume

```text
exists ell C, AoyagiDefinition3SourceData 2 ell H r C.
```

Choose such a source datum `S`.  The already-landed finite `L=2`
classification proves

```text
S.sourceRangeRankWidth_of_L_eq_two_sourceData :
  forall s, 1 <= s -> s <= 3 -> r <= H s.
```

The old pairwise-distinct classifier can therefore be applied to this
particular source datum, yielding the all-source strict inequalities.

For the reverse implication, assume the all-source strict inequalities.  The
already-landed strict-all-source rank-width lemma proves

```text
sourceRangeRankWidth_of_all_selected_strict :
  forall s, 1 <= s -> s <= 3 -> r <= H s.
```

Again the old pairwise-distinct classifier applies, yielding Definition 3
source data.  Equivalently, one can directly invoke the all-source selected
constructor; the wrapper route keeps the old reviewed theorem as the backend.

The companion `ell=2` wrapper is even smaller.  Given a concrete source datum
`S`, use `S.sourceRangeRankWidth_of_L_eq_two_sourceData` as the rank-width
input to

```text
S.ell_eq_two_of_L_eq_two_rankWidth_pairwiseDistinct.
```

## Lean Shape

Add in `lean/DLNFibre/DLN/Aoyagi/Definition3Bridge.lean`:

```text
AoyagiDefinition3SourceData.ell_eq_two_of_L_eq_two_pairwiseDistinct
AoyagiDefinition3SourceData.exists_sourceData_iff_allSourceStrict_of_L_eq_two_pairwiseDistinct
```

Both theorems keep the pairwise-distinct hypotheses explicit.  They only
remove the separate rank-width input.

## Boundary

This is finite Definition 3 bookkeeping for the `L=2` pairwise-distinct
branch.  It is not a repeated-width classifier, not a canonical branch
selection theorem, not a branch-independent Theorem 2 formula, not Eq5
construction, not chart production, not normal crossings, not pole order, and
not RLCT extraction.

## Lean Check

Implemented in `lean/DLNFibre/DLN/Aoyagi/Definition3Bridge.lean`.

Focused direct elaboration and focused module build passed:

```text
env LEAN_NUM_THREADS=3 lake env lean -E warning DLNFibre/DLN/Aoyagi/Definition3Bridge.lean
env LEAN_NUM_THREADS=3 lake build DLNFibre.DLN.Aoyagi.Definition3Bridge
```

Direct axiom probe for the two new declarations reports only:

```text
[propext, Classical.choice, Quot.sound]
```

Xhigh reviewer `Dalton the 2nd` passed the slice; review saved at
`review-definition3-l-eq-two-pairwise-distinct-rankwidth-removal-a6.md`.
