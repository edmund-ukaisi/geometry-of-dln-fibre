# Statement card - A4 actual-width labels

## Lean artifacts

File: `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`.

Names:

- `DLNFibre.DLN.Aoyagi.prefixMinNat`
- `DLNFibre.DLN.Aoyagi.widthZ`
- `DLNFibre.DLN.Aoyagi.prefixMinNat_cast`
- `DLNFibre.DLN.Aoyagi.prefixMinNat_le_width`
- `DLNFibre.DLN.Aoyagi.actualWidthLabel`
- `DLNFibre.DLN.Aoyagi.prefixWidthLabel`
- `DLNFibre.DLN.Aoyagi.actualWidthLabel_of_prefixWidthLabel`
- `DLNFibre.DLN.Aoyagi.actualWidthLabel_not_prefixWidthLabel_of_prefixMinNat_lt_width`
- `DLNFibre.DLN.Aoyagi.actualWidthLabel_case2_new`
- `DLNFibre.DLN.Aoyagi.prefixWidthLabel_case2_new`
- `DLNFibre.DLN.Aoyagi.correctedCase2PivotVector`
- `DLNFibre.DLN.Aoyagi.terminalExponent_correctedCase2PivotVector`

## Statement

For natural actual widths `n`, Lean distinguishes two label ranges:

```text
actualWidthLabel L n s k  :  1 <= s <= L, 1 <= k <= n_(s+1),
prefixWidthLabel L n s k  :  1 <= s <= L, 1 <= k <= mu_(s+1).
```

It proves that prefix-width labels are actual-width labels, but that the
converse fails whenever `mu_(s+1) < n_(s+1)`: the label
`(s, mu_(s+1)+1)` is a valid actual-width label and is not a prefix-width
label.

Lean also proves the Case 2 new-label bookkeeping facts:

```text
J+1 <= n_(S+1)      -> (S,J+1) is an actual-width label,
J+1 <= mu_(S+1)     -> (S,J+1) is a prefix-width label.
```

Finally, Lean packages the corrected Case 2 pivot vector over natural widths
and proves its terminal exponent:

```text
terminalExponent L n_Z (correctedCase2PivotVector n S J)
  = (mu_S - J) * (n_(S+1) - J).
```

## Source role

This formalizes the repair report's notation lock: Aoyagi's source labels are
indexed by actual widths `M^(s+1)`, while prefix minima `M(S+1)` govern
diagonal lengths and continuation bounds. Using prefix minima as label ranges
undercounts labels when the actual width is larger.

The corrected Case 2 pivot vector is the prefix-minimum repair, not the vector
printed in the PDF.

## Proved

- `prefixMinNat n j <= n j` for positive `j`.
- `prefixWidthLabel` is a subset of `actualWidthLabel`.
- If `mu_(s+1) < n_(s+1)`, the first label after the prefix range witnesses
  strict undercounting.
- The new label `(S,J+1)` is valid under the actual-width bound, and under the
  prefix-width bound when the continuation test supplies that stronger bound.
- The corrected natural-width Case 2 vector evaluates to the prefix-minimum
  terminal exponent.

## Not proved

- No full finite vector invariant.
- No Case 1/2 transition theorem.
- No pivot-chart coverage, termination proof, normal-crossing certificate, or
  RLCT extraction.

## Status

- Sorry-free.
- Commit SHA pin pending until the Lean-theorem commit exists.

## Verification

- `lake build DLNFibre.DLN.Aoyagi.BlowupArithmetic`
