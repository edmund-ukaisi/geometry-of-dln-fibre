# Statement Card - Definition 3 three-width triangle constructor

## Lean Target

- `DLNFibre.DLN.Aoyagi.AoyagiDefinition3SourceData.exists_consecutive_three_widths_selectedReducedWidthCeilData_of_triangle_rankWidth`

## Files

- Lean: `lean/DLNFibre/DLN/Aoyagi/Definition3Bridge.lean`
- Reproduction:
  `threads/06-dln-translation/reproduction-definition3-three-width-triangle-a6.md`

## Claim

For `L=2`, if the three source-range reduced widths are `w1,w2,w3` and satisfy
the three strict inequalities

```text
2*w1 < w1+w2+w3,
2*w2 < w1+w2+w3,
2*w3 < w1+w2+w3,
```

then consecutive all-source selected cutpoints produce Definition 3 source
data, selected reduced widths, and a Definition 3 ceiling datum, under the
usual explicit source-range rank-width hypothesis.  The produced selected
width family satisfies `m 0=w1`, `m 1=w2`, and `m 2=w3`.

## Scope

This is a small all-source constructor for the three-width case.  It generalises
the diagnostic `(1,2,2)` example without claiming arbitrary source-data
existence, Definition 3 classification, closed-form ceiling data, Eq5 payloads,
chart production, pole order, or RLCT.

## Verification

Focused Lean check passed:

```text
LEAN_NUM_THREADS=1 ~/.elan/bin/lake env lean DLNFibre/DLN/Aoyagi/Definition3Bridge.lean
LEAN_NUM_THREADS=1 ~/.elan/bin/lake build DLNFibre.DLN.Aoyagi.Definition3Bridge
lean/scripts/sorries
git diff --check
```

Review passed:
`threads/06-dln-translation/review-definition3-three-width-triangle-a6.md`.
