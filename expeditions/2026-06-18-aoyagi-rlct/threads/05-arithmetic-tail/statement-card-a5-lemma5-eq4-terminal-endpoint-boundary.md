# Statement card - A5 Lemma 5 equation (4) terminal endpoint boundary

## Lean Artifacts

Files:

- `lean/DLNFibre/DLN/Aoyagi/HtildeChainArithmetic.lean`
- `lean/DLNFibre/DLN/Aoyagi/Lemma5DisplayedVector.lean`

Names:

- `DLNFibre.DLN.Aoyagi.aoyagiHtildeLowerNat_last_eq_zero_of_selectedSum`
- `DLNFibre.DLN.Aoyagi.aoyagiHtildeUpperNat_last_eq_zero_of_selectedSum`
- `DLNFibre.DLN.Aoyagi.AoyagiSelectedCutpoints.not_block_terminalEndpoint`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma5Eq4_prefix_leftEndpoint`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma5Eq4_middle_leftEndpoint`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma5Eq4_tail_leftEndpoint_of_cutoff_lt`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma5Eq4_terminalEndpoint_zero_of_upperNatExtension`

## Statement

Lean now has a narrow conditional terminal-endpoint package for Aoyagi Lemma 5
equation `(4)`.

The package proves:

- Nat-indexed terminal zero for both displayed `Htilde` chains under
  Definition 3's selected-sum identity.
- The terminal selected endpoint `S_(ell+1)-1` is not in a half-open selected
  block.
- Left-endpoint values for the supplied prefix, middle, and strict-tail
  branches.
- If a supplied endpoint extension assigns
  `T(S_(ell+1)-1)=Htilde'_ell`, then `T(S_(ell+1)-1)=0`.

## Assumed

- Selected cutpoints and their strict order.
- The supplied equation `(4)` branch certificate for branch endpoint facts.
- A supplied terminal endpoint assignment for the endpoint-zero theorem.
- Definition 3's selected-sum identity.

## Cited

- None in Lean.  This is finite endpoint and supplied-data bookkeeping.

## Deferred

- Construction/existence of equation `(4)`'s displayed vector.
- Terminal `tilde t=0` as a full vector property.
- Case 1(2) chart sequence and repeated gap checks.
- Vector admissibility, source vector-to-chain correspondence, Lemma 5 order
  count, pole order, normal crossings, and RLCT extraction.

## Review

- Source audit: xhigh `Kuhn`.
- Lean/API audit: xhigh `Hilbert`.
- Review artifact:
  `review-lemma5-eq4-terminal-endpoint-boundary-a5.md`.

## Verification

- `lake env lean DLNFibre/DLN/Aoyagi/HtildeChainArithmetic.lean`
- `lake env lean DLNFibre/DLN/Aoyagi/Lemma5DisplayedVector.lean`
- `git diff --check`
