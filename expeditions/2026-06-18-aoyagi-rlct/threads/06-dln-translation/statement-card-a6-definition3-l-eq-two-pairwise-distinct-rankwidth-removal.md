# Statement Card - A6 Definition 3 `L=2` Pairwise-Distinct Rank-Width Removal

## Lean Targets

```text
AoyagiDefinition3SourceData.ell_eq_two_of_L_eq_two_pairwiseDistinct
AoyagiDefinition3SourceData.exists_sourceData_iff_allSourceStrict_of_L_eq_two_pairwiseDistinct
```

## Claim

In the `L=2` pairwise-distinct source-range case, the explicit rank-width
input in the reviewed pairwise-distinct classifier can be removed.  Source-data
existence supplies source-range rank-width by the existing `L=2`
source-data theorem; all-source strict inequalities supply source-range
rank-width by the existing strict-all-source theorem.

## Inputs

- Pairwise distinct reduced widths:
  `M^(1) != M^(2)`, `M^(1) != M^(3)`, and `M^(2) != M^(3)`.
- For the classifier theorem, no separate source-range rank-width hypothesis.

## Output

```text
(exists ell C, AoyagiDefinition3SourceData 2 ell H r C)
  iff
(forall s, 1 <= s -> s <= 3 ->
  2 * aoyagiReducedWidthInt H r s
    < sum j : Fin 3, aoyagiReducedWidthInt H r (j.val + 1)).
```

The companion theorem states that a concrete pairwise-distinct `L=2` source
datum must have `ell = 2`, again without a caller-supplied rank-width input.

## Nonclaims

This is finite Definition 3 bookkeeping only.  It does not classify repeated
widths, choose a canonical branch, prove branch-independent formula data,
construct Eq5 payloads or charts, prove normal crossings, identify pole order,
or extract RLCT.

## Verification

Focused direct elaboration, focused module build, and direct axiom probe
passed.  Xhigh independent review by `Dalton the 2nd` passed; review saved at
`review-definition3-l-eq-two-pairwise-distinct-rankwidth-removal-a6.md`.
