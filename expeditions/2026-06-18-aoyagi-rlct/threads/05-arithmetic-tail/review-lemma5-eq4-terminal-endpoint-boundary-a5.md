# Review - Lemma 5 equation (4) terminal endpoint boundary

Reviewers: xhigh `Kuhn` source audit and xhigh `Hilbert` Lean/API audit.

Status: passed for the narrow conditional endpoint package; full source
realisation remains blocked.

## Scope

This review covers:

```text
aoyagiHtildeLowerNat_last_eq_zero_of_selectedSum
aoyagiHtildeUpperNat_last_eq_zero_of_selectedSum
AoyagiSelectedCutpoints.not_block_terminalEndpoint
aoyagiLemma5Eq4_prefix_leftEndpoint
aoyagiLemma5Eq4_middle_leftEndpoint
aoyagiLemma5Eq4_tail_leftEndpoint_of_cutoff_lt
aoyagiLemma5Eq4_terminalEndpoint_zero_of_upperNatExtension
```

## Findings

No blocking findings for these narrow statements.

The source audit found a genuine gap for promoting equation `(4)` to a
terminal displayed-vector theorem: the printed Lemma 5 text does not supply
the Case 1(2) chart sequence, repeated gap checks, final endpoint convention,
or proof of `tilde t_{s,k}=0`.

The Lean/API audit recommended finite consequences of the current supplied
piecewise certificate rather than a broad displayed-vector construction
record.  The left-endpoint branch lemmas are direct projections of the supplied
branch certificate.  The terminal endpoint theorem is correctly conditional:
it assumes the endpoint assignment and derives zero from the already-proved
upper-chain terminal zero.

`AoyagiSelectedCutpoints.not_block_terminalEndpoint` is important guardrail
bookkeeping: selected-span coverage is half-open and excludes
`S_(ell+1)-1`.

## Verification

Controller ran:

```text
lake env lean DLNFibre/DLN/Aoyagi/HtildeChainArithmetic.lean
lake env lean DLNFibre/DLN/Aoyagi/Lemma5DisplayedVector.lean
git diff --check
```
