# Statement Card - A6 Final Formula Notation

## Lean Artifact

File:

- `lean/DLNFibre/DLN/Aoyagi/FinalFormula.lean`

Aggregator:

- `lean/DLNFibre.lean`

Names:

- `DLNFibre.DLN.Aoyagi.aoyagiReducedWidthInt`
- `DLNFibre.DLN.Aoyagi.aoyagiSelectedReducedWidths`
- `DLNFibre.DLN.Aoyagi.aoyagiSelectedWidthValueSet`
- `DLNFibre.DLN.Aoyagi.AoyagiDefinition3CeilData`
- `DLNFibre.DLN.Aoyagi.AoyagiDefinition3CeilData.theorem2OrderFormula`
- `DLNFibre.DLN.Aoyagi.aoyagiTheorem2RegularTerm`
- `DLNFibre.DLN.Aoyagi.aoyagiSelectedWidthAverage`
- `DLNFibre.DLN.Aoyagi.aoyagiSelectedWidthPairSum`
- `DLNFibre.DLN.Aoyagi.AoyagiDefinition3CeilData.selectedWidthAverage_eq_ceil`
- `DLNFibre.DLN.Aoyagi.aoyagiTheorem2Lambda_average`
- `DLNFibre.DLN.Aoyagi.aoyagiTheorem2Lambda_ceil`
- `DLNFibre.DLN.Aoyagi.aoyagiTheorem2Lambda_expanded`
- `DLNFibre.DLN.Aoyagi.aoyagiTheorem2Lambda_fromCeilData`
- `DLNFibre.DLN.Aoyagi.aoyagiTheorem2Lambda_average_eq_ceil_of_average_eq`
- `DLNFibre.DLN.Aoyagi.aoyagiTheorem2Lambda_ceil_eq_expanded`
- `DLNFibre.DLN.Aoyagi.aoyagiTheorem2Lambda_average_eq_fromCeilData`
- `DLNFibre.DLN.Aoyagi.aoyagiTheorem2Lambda_average_eq_expanded_ofCeilData`

## Claim

Lean now has a source-facing formula layer for Aoyagi Definition 3 and
Theorem 2.  It names the selected reduced widths, the Definition 3 ceiling
integer and residue, Aoyagi's order formula, and the three displayed
`lambda` formulas.  It proves the elementary rational rewrites among the
displayed formulas under the explicit Definition 3 ceiling data.

## Proved

- Reduced widths are represented integer-valued as `(H s : Int) - r`.
- Definition 3's selected-sum identity rewrites the selected average as
  `ceilWidth + (aParam - ell)/ell`, assuming `0 < ell`.
- The first and second displayed `lambda` formulas agree for supplied
  Definition 3 ceiling data.
- The second and third displayed `lambda` formulas agree by rational
  arithmetic when `0 < ell`.
- Consequently, the average and expanded displayed formulas agree for
  supplied Definition 3 ceiling data.

## Assumed

- The selected cutpoints and selected width family are supplied.
- The Definition 3 ceiling datum is supplied: `0 < ell`, `ceilWidth`,
  `aParam`, `selectedSum_eq`, `0 < aParam`, and `aParam <= ell`.
- The source layer-width/rank hypotheses that make the reduced widths
  geometrically meaningful are not encoded in this notation slice.

## Cited

None in Lean.  This is finite arithmetic/formula bookkeeping.

## Deferred

- The full Definition 3 selection inequalities.
- Existence or uniqueness of the selected cutpoints and ceiling datum.
- Lemma 4 and Lemma 5 links from chart exponents to the formula.
- Normal crossings, pole-order interpretation, and RLCT extraction.
- The final Theorem 2 statement as a statistical RLCT theorem.

## Review

- Reproduction:
  `reproduction-definition3-theorem2-translation-a6.md`.
- Review artifact:
  `review-final-formula-notation-a6.md`.

## Verification

Run from `lean/`:

```text
lake env lean DLNFibre/DLN/Aoyagi/FinalFormula.lean
lake build DLNFibre.DLN.Aoyagi.FinalFormula
lake build DLNFibre
scripts/sorries
```
