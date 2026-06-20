# Review - Lemma 5 equation (4) terminal collision

Reviewer: xhigh `Hubble`.

Scope:

- `aoyagiHtildeUpperNat_pred_eq_sub_lastWidth_of_selectedSum`;
- `aoyagiLemma5Eq4_terminalEndpoint_value_of_predBoundary`;
- `aoyagiLemma5Eq4_terminalEndpoint_zero_iff_lastWidth_of_predBoundary`;
- reproduction, statement card, and ledger updates.

## Findings

None.

## Verdict

Pass as-is.

The Lean statements match the narrow claim: under `p+1=a`, the equation `(4)`
special boundary is the terminal selected endpoint, its supplied branch value
is `M-W_(ell+1)-p+1`, and zero is equivalent to the extra condition
`W_(ell+1)=M-p+1`.

The off-by-one translation checks against Aoyagi PDF p. 27: the displayed
boundary `S_(j0+ell-a+2)-1` and value `Htilde'_(j-1)-j0+1` correspond to
`C.point (p+(ell-a)+1)-1` and
`aoyagiHtildeUpperNat ... (p+(ell-a))-p+1`.

The notes stay conditional and do not overclaim terminal-vector construction,
chart coverage, or Lemma 5.

## Commands Run

- `lake env lean DLNFibre/DLN/Aoyagi/HtildeChainArithmetic.lean`
- `lake env lean DLNFibre/DLN/Aoyagi/Lemma5DisplayedVector.lean`
- `lake build DLNFibre.DLN.Aoyagi.HtildeChainArithmetic`
- `lake build DLNFibre.DLN.Aoyagi.Lemma5DisplayedVector`
- `git diff --check`
- source PDF extraction around Definition 3 and Lemma 5 equation `(4)`
