# Statement card - A5 Lemma 5 equation (5) source range and width bound

## Lean Names

- `DLNFibre.DLN.Aoyagi.AoyagiSelectedCutpoints.selectedSpan_sourceIndex_le_of_terminalEndpoint_le`
- `DLNFibre.DLN.Aoyagi.AoyagiSelectedCutpoints.selectedSpan_sourceIndex_le_of_lastPoint_le`
- `DLNFibre.DLN.Aoyagi.AoyagiSelectedCutpoints.block_sourceIndex_le_of_terminalEndpoint_le`
- `DLNFibre.DLN.Aoyagi.AoyagiSelectedCutpoints.block_sourceIndex_le_of_lastPoint_le`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma5Eq5_actualWidthLabel_at_of_widthBound`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma5Eq5_piecewise_block_actualWidthLabel_of_widthBound`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma5Eq5_piecewise_ownBlock_actualWidthLabel_of_widthBound`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma5Eq5_piecewise_ownBlock_actualWidthLabel_of_lastPoint_widthCompatibility`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma5Eq5_piecewise_ownBlock_actualWidthLabel_of_lastPoint_widthBound`

## Claim

Lean now has a source-shaped Eq5 own-block label wrapper using the last
selected cutpoint range and an actual-width lower bound.

If `S` lies in the Eq5 own selected block `C.block p S`, the last selected
cutpoint is source-compatible,

```text
C.point ell <= L+1,
```

and the actual layer at `S` is at least as wide as the selected width,

```text
W_p <= n(S+1),
```

then the supplied Eq5 certificate and Definition 3 label arithmetic prove

```text
T(S)=k-1
actualWidthLabel L n S k.
```

The older equality-shaped wrapper is kept, but the width-bound theorem is the
more source-faithful arbitrary-block interface.

## Inputs

- Definition 3 selected-width sum and strict selected-width inequalities.
- A supplied equation `(5)` piecewise certificate.
- Own-block membership `C.block p S`.
- Last selected cutpoint range compatibility `C.point ell <= L+1`.
- Actual-width lower bound `W_p <= n(S+1)`.

## Proves

- Selected-span and selected-block source upper range from last-cutpoint
  compatibility.
- Actual source-label legality under a width lower bound.
- Own-block value rewrite `T(S)=k-1`.

## Does Not Prove

- Actual-width lower bound `W_p <= n(S+1)` from Definition 3.
- Equation `(5)` displayed-vector construction or existence.
- Terminal `tilde t=0`.
- Vector admissibility or source-vector-to-chain correspondence.
- Case 1(2) chart sequence.
- Lemma 5 order count, pole order, normal crossings, or RLCT extraction.

## Source

Aoyagi Definition 3, PDF pp. 8-9, and Lemma 5 equation `(5)`, PDF p. 27.

## Review

Pen-and-paper/source scout: `Volta the 2nd` (xhigh).
Source-range reviewer: `Huygens the 2nd` (xhigh).
