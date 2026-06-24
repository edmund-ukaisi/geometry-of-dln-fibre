# Review - A2 literal product-difference coordinate ideal bridge

Reviewer: Hubble the 4th, xhigh-effort subagent.

## Verdict

Pass.  No blocking findings.

## Findings

The bridge theorem has the intended statement:

```text
AoyagiProductDifferenceCoordinateIndex.matrixEntryIdeal_fromBlocks_neg_neg_sub_mul_eq_entryIdeal
```

It identifies the matrix-entry ideal of the literal signed/corrected p. 13
block

```text
fromBlocks X (-F2) (-F3) (D - F3 * F2)
```

with

```text
AoyagiProductDifferenceCoordinateIndex.entryIdeal X F2 F3 D.
```

The signs and block dimensions are correct.  With
`F2 : Matrix iota nu R` and `F3 : Matrix mu iota R`, the correction
`F3 * F2` has shape `Matrix mu nu R`, matching `D`.  The correction is
`F3*F2`, not `F2*F3`.

The required hypotheses are minimal for this bridge: `[CommRing R]` and
`[Fintype iota]`.  No finiteness of the other block indices, decidable
equality, determinant chart, inverse, topology, or analytic hypothesis is
needed.

For canonical suffix-state fields the intended instantiation is

```text
X  = S.Ctop - 1
F2 = -S.B
F3 = lowerLeftBlock S.L
D  = S.D.
```

## Nonclaims Checked

This is scalar entry-ideal algebra only.  It does not prove analytic
germ-ideal transport, chart coverage, regular-suspension construction, normal
crossings, pole order, RLCT, source-rank openness, or identify `S.D` with a
raw product of lower-right edge blocks.
