# Statement card - A5 Lemma 4 source sum bridge

## Lean Artifact

Files:

- `lean/DLNFibre/DLN/Aoyagi/Lemma4CountArithmetic.lean`

Names:

- `DLNFibre.DLN.Aoyagi.aoyagiLemma4F`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma4F_sum_eq_selectedSum`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma4F_sum_eq_of_selectedSum_eq_pred_add_a`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma4_twoValueCount_of_terminalH`
- `DLNFibre.DLN.Aoyagi.aoyagiLemma4_twoValueCount_of_terminalH_le_ell`

## Statement

Lean now proves the finite source-sum bridge in Aoyagi's Lemma 4.  If

```text
F_j = H_(j-1) - H_j + M(S_(j+1))
```

is interpreted with the explicit convention `H_0 = M(S_1)`, then the terminal
condition `H_ell = 0` gives

```text
sum_j F_j = sum_j M(S_j).
```

With Definition 3's indexed selected-width sum

```text
sum_j M(S_j) = ell*(M-1)+a,
```

the source sum identity used by the two-value count follows.

## Proved

- The finite increment definition `aoyagiLemma4F`.
- The telescoping identity `sum F_j = sum M(S_j)` under `H_0 = M(S_1)` and
  `H_ell = 0`.
- The source-shaped identity `sum F_j = ell*(M-1)+a` when the selected widths
  have Definition 3's total sum.
- A source-shaped wrapper: if the increments are all `M-1` or `M`, then exactly
  `a` increments are `M` and exactly `ell-a` are `M-1`.
- The same hypotheses force `a <= ell`.

## Assumed

- The selected widths are already indexed as `m : Fin (ell+1) -> Z`.
- `H` is extended by the convention `H 0 = m 0`.
- The terminal condition `H (Fin.last ell) = 0`.
- Definition 3's selected-width sum identity.
- The two-value increment hypothesis for the count wrapper.

## Cited

- None in Lean.  This is finite arithmetic.

## Deferred

- The proof that a source vector satisfies the two-value hypothesis.
- The inequalities `Ttilde <= T <= Ttilde'`.
- The endpoint-corrected Lemma 3 bridge from the count to minimisation.
- Lemma 4's full conclusion that the vector corresponds to `lambda`.
- Lemma 5's chart-family admissibility, coverage, and order-count theorem.

## Review

- Reproduction:
  `reproduction-lemma4-sum-bridge-a5.md`.
- Review artifact:
  `review-lemma4-sum-bridge-a5.md`.

## Verification

- From `lean/`: `lake env lean DLNFibre/DLN/Aoyagi/Lemma4CountArithmetic.lean`
