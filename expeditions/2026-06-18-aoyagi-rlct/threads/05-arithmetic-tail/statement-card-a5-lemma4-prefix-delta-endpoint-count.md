# Statement card - A5 Lemma 4 prefix-delta endpoint count

## Lean Artifact

Files:

- `lean/DLNFibre/DLN/Aoyagi/HtildeChainArithmetic.lean`

Names:

- `DLNFibre.DLN.Aoyagi.aoyagiLemma4IncrementPrefixDelta`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma4F_eq_pred_add_incrementPrefixDelta_def`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma4IncrementPrefix_zero_of_H0`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma4IncrementPrefix_last_eq_a_of_terminalH`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma4IncrementPrefixDelta_sum_eq_last_sub_zero`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma4IncrementPrefixDelta_sum_eq_a_of_terminalH`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma4_binaryIncrementPrefix_count_eq`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma4_binaryIncrementPrefix_count_eq_of_HtildeChainBounds`

## Statement

Lean now proves endpoint and count bookkeeping for the Lemma 4 prefix-delta
interface.  With

```text
D_j = P(j)-H_j-j*(M-1),
Delta_j = D_(j+1)-D_j,
```

the source convention `H_0=m_0` gives `D_0=0`, while terminal `H_ell=0` plus
the selected-width sum gives `D_ell=a`.  The sum of successive deltas
telescopes to `D_ell-D_0`, so under those endpoint hypotheses

```text
sum_j Delta_j = a.
```

If the deltas are also binary, exactly `a` of them are `1` and exactly
`ell-a` are `0`.

## Proved

- Named prefix-delta difference `aoyagiLemma4IncrementPrefixDelta`.
- Definitional wrapper for `F_j=(M-1)+Delta_j`.
- `D_0=0` under `H_0=m_0`.
- `D_ell=a` under terminal `H_ell=0` and selected-width sum.
- Finite telescoping of successive deltas.
- Sum of deltas is `a` under the terminal source hypotheses.
- Binary delta count under the terminal source hypotheses.
- Same-coordinate `Htilde`-chain-bound version, where the chain bounds provide
  `H_ell=0` but the binary hypothesis remains explicit.

## Assumed

- `H_0=m_0` and `H_ell=0` for the terminal-source count.
- The selected-width sum.
- Binary deltas for the count theorem.
- For the `Htilde`-chain-bound wrapper, same-coordinate chain bounds and
  `a <= ell`.

## Cited

- None in Lean.  This is finite arithmetic.

## Deferred

- Source exponent vectors imply binary prefix deltas.
- Same-coordinate `Htilde <= H <= Htilde'` bounds imply binary prefix deltas.
- A source-faithful `T -> (H_j),(S_j)` correspondence.
- Vector admissibility and correspondence to `lambda`.
- Lemma 5 chart-family admissibility, coverage, exclusions, and pole-order
  interpretation.
- Normal crossings and RLCT extraction.

## Review

- Reproduction:
  `reproduction-lemma4-prefix-delta-endpoint-count-a5.md`.
- Review artifact:
  `review-lemma4-prefix-delta-endpoint-count-a5.md`.

## Verification

- From `lean/`: `lake env lean DLNFibre/DLN/Aoyagi/HtildeChainArithmetic.lean`
- From `lean/`: `lake env lean DLNFibre.lean`
- From `lean/`: `lake build DLNFibre`
- From `lean/`: `./scripts/sorries`
