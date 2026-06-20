# Statement card - A5 Lemma 5 equation (3) slack counterexample

## Lean Artifact

File:

- `lean/DLNFibre/DLN/Aoyagi/HtildeChainArithmetic.lean`

Name:

- `DLNFibre.DLN.Aoyagi.aoyagiLemma5Eq3_slack_not_forced_by_selectedWidthHypotheses_example`

## Statement

Lean now records the concrete selected-width tuple

```text
ell=3, a=2, M=3, W_1=W_2=W_3=W_4=2
```

as a Definition 3-shaped counterexample to equation `(3)`'s one-unit slack and
selected-label upper bound being forced by the selected-width hypotheses.

The theorem proves:

```text
1<=ell,
a<=ell,
1<=a,
a<ell,
ell-a+2<=ell+1,
all W_i positive,
sum_i W_i = ell*(M-1)+a,
forall i, ell*W_i < sum_j W_j,
M-1 <= W_1+W_2,
not W_1+2<=M,
Htilde'_1+1 = 3,
W_2 = 2,
not Htilde'_1+1<=W_2,
not (1<=Htilde'_1+1 and Htilde'_1+1<=W_2).
```

## Proved

- The concrete selected-width tuple satisfies the selected-sum identity.
- It satisfies the strict selected-width inequalities.
- It satisfies the lower width guard `M-1<=W_1+W_2`.
- It fails the one-unit slack `W_1+2<=M`.
- It fails the selected-label upper bound for `k=Htilde'_1+1`.

## Assumed

- None.  This is a closed finite calculation in Lean.

## Cited

- None in Lean.

## Deferred

- Construction of a supplied equation `(3)` branch certificate for this tuple.
- Actual source-width compatibility.
- Displayed-vector construction, introduced-label status, terminal
  `tilde t=0`, Case 1(2) chart sequence, Lemma 5 order count, pole order,
  normal crossings, and RLCT extraction.

## Review

- Source/API review passed by xhigh `Harvey`:
  `review-lemma5-eq3-slack-counterexample-a5.md`.

## Verification

- `lake env lean DLNFibre/DLN/Aoyagi/HtildeChainArithmetic.lean`
