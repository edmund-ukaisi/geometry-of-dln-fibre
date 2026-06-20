# Statement card - A5 Lemma 5 equation (3) boundary split

## Lean Artifact

File:

- `lean/DLNFibre/DLN/Aoyagi/Lemma5DisplayedVector.lean`

Names:

- `DLNFibre.DLN.Aoyagi.aoyagiLemma5Eq3_boundaryIndex_le_ell_of_piecewiseSourceVector`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma5Eq3_boundaryIndex_lt_ell_iff`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma5Eq3_boundaryEndpoint_mem_block_of_two_le`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma5Eq3_boundaryEndpoint_mem_selectedSpan_of_two_le`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma5Eq3_boundaryEndpoint_mem_selectedSpan_iff_two_le`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma5Eq3_boundaryEndpoint_eq_terminal_of_one`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma5Eq3_boundaryEndpoint_not_block_of_one`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma5Eq3_no_terminalEndpointZero_of_one`

## Statement

For a supplied Aoyagi Lemma 5 equation `(3)` branch certificate, the special
boundary `S_(ell-a+2)-1` is in range as `C.point (ell-a+1)-1`.

Under the source guards `a<=ell` and `1<=a`, this boundary is inside the
half-open selected span exactly in the strict case `2<=a`; then it is the left
endpoint of selected block `ell-a+1`. In the terminal case `a=1`, it is the
terminal selected endpoint and is not in any half-open selected block.

The terminal case also has the no-zero corollary: combined with the selected-sum
identity, the supplied equation `(3)` branch value is `1`, so it cannot also be
`0`.

## Proved

- The boundary index satisfies `ell-a+1<=ell`.
- The strict selected-span case is equivalent to `2<=a`.
- In the strict case, the boundary belongs to selected block `ell-a+1` and to
  the selected span.
- In the terminal case `a=1`, the boundary is `S_(ell+1)-1` and is in no
  selected block.
- In the terminal case, the supplied branch certificate is incompatible with
  terminal endpoint zero under the selected-sum identity.

## Assumed

- A supplied equation `(3)` piecewise branch certificate.
- For the no-zero corollary, the selected-sum identity with `a=1`.

## Cited

- None in Lean. This is finite selected-cutpoint arithmetic.

## Deferred

- Construction or existence of the displayed vector.
- Terminal `tilde t=0`.
- Case 1(2) chart sequence, introduced-label status, vector admissibility,
  Lemma 5 order count, normal crossings, and RLCT extraction.

## Verification

- `lake env lean DLNFibre/DLN/Aoyagi/Lemma5DisplayedVector.lean`
