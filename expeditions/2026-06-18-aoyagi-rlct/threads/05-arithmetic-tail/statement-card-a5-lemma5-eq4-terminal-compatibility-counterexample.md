# Statement card - A5 Lemma 5 equation (4) terminal compatibility counterexample

## Lean Artifact

File:

- `lean/DLNFibre/DLN/Aoyagi/HtildeChainArithmetic.lean`

Name:

- `DLNFibre.DLN.Aoyagi.aoyagiLemma5Eq4_lastWidthCompatibility_not_forced_by_selectedWidthHypotheses_example`

## Statement

Lean now records the concrete selected-width tuple

```text
ell=3, a=2, p=1, M=3, W_1=W_2=W_3=W_4=2
```

as a Definition 3-shaped counterexample to equation `(4)`'s terminal
last-width compatibility being forced by the selected-width hypotheses.

The theorem proves:

```text
1<=ell,
a<=ell,
1<=p,
p<=ell-a,
p+1=a,
p+(ell-a)+2<=ell+1,
p+(ell-a)+1=ell,
all W_i positive,
sum_i W_i = ell*(M-1)+a,
forall i, ell*W_i < sum_j W_j,
W_(ell+1) != M-p+1.
```

## Proved

- The concrete selected-width tuple satisfies the selected-sum identity.
- It satisfies the strict selected-width inequalities.
- It is in the terminal-collision equation `(4)` index case.
- It fails the last-width compatibility `W_(ell+1)=M-p+1`.

## Assumed

- None.  This is a closed finite calculation in Lean.

## Cited

- None in Lean.

## Deferred

- Construction of a supplied equation `(4)` branch certificate for this tuple.
- Construction of any terminal extension.
- Displayed-vector construction, terminal `tilde t=0`, Case 1(2) chart
  sequence, Lemma 5 order count, pole order, normal crossings, and RLCT
  extraction.

## Review

- Source/API review passed by xhigh `Boole`:
  `review-lemma5-eq4-terminal-compatibility-counterexample-a5.md`.

## Verification

- `lake env lean DLNFibre/DLN/Aoyagi/HtildeChainArithmetic.lean`
- `lake env lean DLNFibre.lean`
- `lake build DLNFibre.DLN.Aoyagi.HtildeChainArithmetic`
- `lake build DLNFibre`
- `git diff --check`
- `./lean/scripts/sorries`
