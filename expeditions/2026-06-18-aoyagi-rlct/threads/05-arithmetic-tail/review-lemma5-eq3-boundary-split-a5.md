# Review - Lemma 5 equation (3) boundary split

Reviewer: xhigh `Mill`.

Scope:

- `aoyagiLemma5Eq3_boundaryIndex_le_ell_of_piecewiseSourceVector`
- `aoyagiLemma5Eq3_boundaryIndex_lt_ell_iff`
- `aoyagiLemma5Eq3_boundaryEndpoint_mem_block_of_two_le`
- `aoyagiLemma5Eq3_boundaryEndpoint_mem_selectedSpan_of_two_le`
- `aoyagiLemma5Eq3_boundaryEndpoint_mem_selectedSpan_iff_two_le`
- `aoyagiLemma5Eq3_boundaryEndpoint_eq_terminal_of_one`
- `aoyagiLemma5Eq3_boundaryEndpoint_not_block_of_one`
- `aoyagiLemma5Eq3_no_terminalEndpointZero_of_one`
- reproduction, statement card, and ledger updates.

## Findings

None blocking.

## Verdict

Pass.

The Lean statements are conditional on a supplied equation `(3)` certificate,
not a construction of Aoyagi's displayed vector.  The record carries the
needed guards `a<=ell` and `1<=a`, and the boundary/tail split remains encoded
separately.

The new theorems correctly split the special boundary index `ell-a+1`.
In the strict case `2<=a`, the point is a true half-open selected-block left
endpoint and lies in the selected span.  In the terminal case `a=1`, the point
rewrites to `C.point ell - 1` and is excluded from every selected block.  The
selected-span iff theorem is also sound: the forward direction reduces
`not 2<=a` to `a=1` using the certificate guard `1<=a`, then contradicts the
strict upper half-open span bound after rewriting to the terminal endpoint.

The no-zero corollary is properly scoped.  It uses the selected-sum identity
and the existing value-one theorem; it does not assume terminal zero.

## Source Fidelity

Aoyagi PDF p. 27 equation `(3)` gives the special assignment at
`S_(ell-a+2)-1` with value `Htilde'_(ell-a+1)+1`.  Since Lean uses
`C.point i = S_(i+1)`, the Lean boundary `C.point (ell-a+1)-1` is the correct
zero-based translation.  The source branch range `2<=j<=ell-a+1` maps to Lean
block indices `1<=b<=ell-a`, and the strict tail condition keeps the special
boundary from being absorbed into the tail.

## Caveats

Do not phrase this as a displayed-vector construction, terminal `tilde t=0`,
introduced-label theorem, chart-sequence theorem, Lemma 5 order count, normal
crossing theorem, or RLCT extraction.  It is finite boundary bookkeeping for a
supplied branch certificate.

## Commands Run

- `pdftotext -f 27 -l 27 -layout ... -`
- `pdftotext -f 26 -l 28 -layout ... -`
- `lake env lean DLNFibre/DLN/Aoyagi/Lemma5DisplayedVector.lean`
- `lake build DLNFibre.DLN.Aoyagi.Lemma5DisplayedVector`
- `scripts/sorries DLNFibre/DLN/Aoyagi/Lemma5DisplayedVector.lean`
- `git diff --check`
