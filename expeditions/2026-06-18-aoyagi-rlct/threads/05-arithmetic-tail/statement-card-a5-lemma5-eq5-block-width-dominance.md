# Statement card - A5 Lemma 5 equation (5) block width dominance

## Lean Names

- `DLNFibre.DLN.Aoyagi.AoyagiSelectedCutpoints.block_sourceLayer_mem_Ico`
- `DLNFibre.DLN.Aoyagi.AoyagiSelectedCutpoints.block_sourceLayer_eq_left_or_between`
- `DLNFibre.DLN.Aoyagi.AoyagiSelectedCutpoints.point_ne_of_between_adjacent`
- `DLNFibre.DLN.Aoyagi.AoyagiSelectedCutpoints.selectedWidthNat_le_actualWidth_of_block`
- `DLNFibre.DLN.Aoyagi.AoyagiSelectedCutpoints.selectedWidthNat_le_actualWidth_of_block_of_leftEndpoint_min`
- `DLNFibre.DLN.Aoyagi.AoyagiSelectedCutpoints.selectedWidthNat_le_actualWidth_of_block_of_offSelected`
- `DLNFibre.DLN.Aoyagi.AoyagiSelectedCutpoints.selectedWidthNat_le_actualWidth_of_block_of_offSelected_lt`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma5Eq5_ownBlock_actualWidthLabel_of_lastPoint_blockWidth`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma5Eq5_ownBlock_actualWidthLabel_of_lastPoint_leftMin`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma5Eq5_piecewise_ownBlock_actualWidthLabel_of_lastPoint_offSelected`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma5Eq5_piecewise_ownBlock_actualWidthLabel_of_lastPoint_offSelected_lt`

## Claim

Lean now derives the Eq5 width bound `W_p <= n(S+1)` from explicit
index-level width hypotheses for selected blocks.

The primary helper says: if every source layer `r` in selected block `i`
satisfies

```text
W_i <= n(r),
```

then `C.block p S` gives `W_p <= n(S+1)`.  The Eq5 wrapper combines this
with last-cutpoint source range and the supplied Eq5 own-block value to prove

```text
T(S)=k-1
actualWidthLabel L n S k.
```

Lean also has two derived interfaces:

- left-endpoint width plus block-local minimum;
- selected-cutpoint width plus index-level off-selected-layer dominance.

## Inputs

- A supplied Eq5 piecewise certificate.
- Own-block membership `C.block p S`.
- Last selected cutpoint range compatibility `C.point ell <= L+1`.
- Explicit block-local width dominance, or one of the two derived dominance
  interfaces.

## Proves

- Source-layer interval `C.point p <= S+1 < C.point(p+1)`.
- A strict-between source layer is not any selected cutpoint.
- Eq5 actual source-label legality from explicit block-width data.

## Does Not Prove

- The width bound from Aoyagi Definition 3 alone.
- Any no-duplicate selected-width-value hypothesis.
- Equation `(5)` displayed-vector construction or existence.
- Terminal `tilde t=0`.
- Vector admissibility or source-vector-to-chain correspondence.
- Case 1(2) chart sequence.
- Lemma 5 order count, pole order, normal crossings, or RLCT extraction.

## Source

Aoyagi Definition 3, PDF pp. 8-9, and Lemma 5 equation `(5)`, PDF p. 27.

## Review

Paper/source scout: `McClintock the 2nd` (xhigh).
Lean/API scout: `Locke the 2nd` (xhigh).
