# Review - A5 Lemma 4 source sum bridge

Reviewed objects:

- `lean/DLNFibre/DLN/Aoyagi/Lemma4CountArithmetic.lean`
- `reproduction-lemma4-sum-bridge-a5.md`
- `statement-card-a5-lemma4-sum-bridge.md`

Verdict: no blocking arithmetic or scope issue found for the finite
source-sum bridge sub-slice.

Independent xhigh source checker `Dewey the 5th` derived the same identity:

```text
sum_{j=1}^ell F_j = B - H_ell,
```

where `B = sum_{j=1}^{ell+1} M(S_j)`.  With Aoyagi's terminal condition
`H_ell=0` and Definition 3's `B=ell*(M-1)+a`, this proves the sum identity
previously assumed by the two-value count theorem.

The reviewer caveat is decisive for scope: Lemma 4's later uniform expression
for `F_j` is source-faithful at `j=1` only after making the convention
`H_0 := M(S_1)` explicit.  Lean encodes this as the hypothesis `H 0 = m 0`.

Independent xhigh Lean scout `Zeno the 5th` flagged the main API risk: source
indexing must specify whether the selected-width array stores
`W_1,...,W_(ell+1)` directly or has an additional dummy zero slot.  The landed
API uses the direct storage convention `m : Fin (ell+1) -> Z`; with
`j : Fin ell` representing source indices `1,...,ell`, the term `m j.succ`
is source `W_(j+1)`.  The convention `H 0 = m 0` supplies the missing source
`W_1` in `F_1`.

Independent xhigh reviewer `Volta the 5th` audited the landed Lean and found
no blocking issue.  Volta confirmed that `H j.castSucc`, `H j.succ`, and
`m j.succ` encode source `H_(j-1)`, `H_j`, and `W_(j+1)`, and that
`aoyagiLemma4_twoValueCount_of_terminalH` assumes both the selected-width sum
identity and the two-value condition rather than proving vector admissibility
or correspondence to `lambda`.  Volta's naming recommendation was incorporated:
the selected-sum wrapper is named
`aoyagiLemma4F_sum_eq_of_selectedSum_eq_pred_add_a`, avoiding any implication
that Lean has proved the ceiling property of Definition 3.

This must not be presented as Lemma 4 itself.  It proves only the finite
telescoping bridge from terminal `H` bookkeeping to the sum identity, plus the
already-formalised two-value count wrapper.  It does not prove the two-value
hypothesis, vector admissibility, the endpoint-corrected Lemma 3 minimisation
bridge, Lemma 4's correspondence-to-`lambda` conclusion, Lemma 5, pole order,
normal crossings, or RLCT extraction.

Controller verification ran
`lake env lean DLNFibre/DLN/Aoyagi/Lemma4CountArithmetic.lean`.
