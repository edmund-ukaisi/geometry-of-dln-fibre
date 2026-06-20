# Review - Lemma 5 equation (3) slack counterexample

Reviewer: xhigh `Harvey`.

Scope:

- `aoyagiLemma5Eq3_slack_not_forced_by_selectedWidthHypotheses_example`;
- reproduction, statement card, and ledger updates.

## Findings

None blocking.

## Verdict

Pass, with the caveats below.

The theorem is valid for the intended API boundary: it shows that Definition
3's selected-width hypotheses do not force Lemma 5 equation `(3)`'s extra
slack or selected-label legality.

For `ell=3`, `a=2`, `M=3`, and all selected widths equal to `2`, Lean proves
the range and interior guards, the equation `(3)` selected-index guard,
positivity of all selected widths, the selected-sum identity, the strict
selected-width inequalities, the lower guard `M-1<=W_1+W_2`, failure of
`W_1+2<=M`, `Htilde'_1+1=3`, `W_2=2`, and failure of the selected-label upper
bound.

Source/API fidelity is good when the statement is kept at the Definition
3 selected-width-hypothesis level.  Aoyagi equation `(3)` uses
`s=S_2-1, k=Htilde'_1+1`, and the local arithmetic theorem identifies the
bounds for this label as equivalent to `M-1<=W_1+W_2` and `W_1+2<=M`.  The
actual-label bridge correctly keeps the missing slack explicit.

## Caveats

Do not phrase this as disproving Lemma 5 or constructing an invalid Aoyagi
vector.  It is a closed finite counterexample to one missing implication:
Definition 3 selected-width arithmetic alone does not supply equation `(3)`'s
`W_1+2<=M` slack or selected-label upper bound.  It does not assert actual
source-width compatibility, a displayed vector, introduced-label status,
terminal `tilde t=0`, chart-family coverage, Lemma 5 order count, pole order,
normal crossings, or RLCT extraction.

## Commands Run

- `lake env lean DLNFibre/DLN/Aoyagi/HtildeChainArithmetic.lean`
