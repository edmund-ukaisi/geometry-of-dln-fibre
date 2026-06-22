# Statement Card - A6 Dimension/Rank Convention

## Lean Artifact

File:

- `lean/DLNFibre/DLN/Aoyagi/FinalFormula.lean`

Aggregator:

- `lean/DLNFibre.lean`

Names:

- `DLNFibre.DLN.Aoyagi.aoyagiReducedWidthInt_eq_natCast_sub_of_rank_le`
- `DLNFibre.DLN.Aoyagi.aoyagiReducedWidthInt_nonneg_of_rank_le`
- `DLNFibre.DLN.Aoyagi.aoyagiSelectedReducedWidths_apply`
- `DLNFibre.DLN.Aoyagi.aoyagiSelectedReducedWidths_eq_natCast_sub_of_rank_le`
- `DLNFibre.DLN.Aoyagi.aoyagiSelectedReducedWidths_nonneg_of_rank_le`
- `DLNFibre.DLN.Aoyagi.aoyagiSelectedWidthNat_selectedReducedWidths_of_lt`
- `DLNFibre.DLN.Aoyagi.aoyagiSelectedWidthNat_selectedReducedWidths_fin`
- `DLNFibre.DLN.Aoyagi.aoyagiSelectedWidthNat_selectedReducedWidths_nonneg_of_rank_le`

## Claim

Lean now records the Aoyagi dimension/rank convention needed by Definition 3:
the reduced width `M^(s)=H^(s)-r` is represented by integer subtraction until
an explicit rank-width bound is supplied.  Under `r <= H s`, the integer
width is ordinary Nat subtraction coerced to `Int` and is nonnegative.

## Proved

- Pointwise `r <= H s` rewrites `aoyagiReducedWidthInt H r s` as
  `((H s-r : Nat) : Int)`.
- Pointwise `r <= H s` proves nonnegativity of `aoyagiReducedWidthInt H r s`.
- Pointwise selected bounds give the same rewrites and nonnegativity for
  `aoyagiSelectedReducedWidths`.
- The Nat-indexed Lemma 5 selected-width accessor agrees with selected reduced
  widths on selected-range indices and is nonnegative everywhere under
  pointwise selected rank-width bounds.

## Assumed

- The source layer widths are supplied as `H : Nat -> Nat`.
- The rank is supplied as `r : Nat`.
- The relevant pointwise or selected pointwise rank-width bound is supplied
  explicitly.

## Cited

None in Lean.  This is notation and integer/Nat arithmetic.

## Deferred

- Proving the rank-width inequalities from concrete matrix dimensions and a
  rank-`r` product.
- Product reduction, normal crossings, pole order, and RLCT extraction.

## Review

- Reproduction:
  `reproduction-dimension-rank-convention-a6.md`.
- Review artifact:
  `review-dimension-rank-convention-a6.md`.

## Verification

Run from `lean/`:

```text
lake env lean DLNFibre/DLN/Aoyagi/FinalFormula.lean
lake build DLNFibre.DLN.Aoyagi.FinalFormula
lake build DLNFibre
scripts/sorries
```
