# Review - Lemma 5 equation (5) width-bound counterexample

Reviewers: `Galileo the 2nd` (xhigh paper/source scout), `Dalton the 2nd`
(xhigh Lean validation), `Hilbert the 2nd` (xhigh Lean/API scout), and
`Hume the 2nd` (xhigh Lean/API scout).  Verdict: valid guardrail.

## Findings

No issue was found with the mathematical counterexample.

For cutpoints `1,3,5,7`, the condition `C.block 2 5` holds because

```text
5 - 1 <= 5 < 7 - 1.
```

The relevant source layer is therefore `S+1=6`.  The selected width in block
`p=2` is `2`, while the actual width at layer `6` is `1`; hence the needed
bound `2 <= 1` is false.

The selected-width hypotheses are also satisfied:

```text
1+2+2+2 = 7 = 3*(3-1)+1,
3*1 < 7,
3*2 < 7.
```

The selected cutpoint compatibility holds by construction:

```text
n(1)=1, n(3)=2, n(5)=2, n(7)=2.
```

## Source Fidelity

This is source-faithful as a guardrail because the failure exploits exactly the
difference between value-level and position-level non-selected conditions.
The bad layer `6` is not a selected cutpoint, but its width value `1` is a
selected width value.  Aoyagi Definition 3's value-level condition therefore
does not force it to dominate the selected widths.

The Lean theorem includes the value-level non-selected dominance condition, so
it records more than a bare arithmetic failure.  It shows that this
Definition 3-shaped condition is insufficient for the Eq5 actual-label bound.

## Lean Placement

The theorem is placed in
`lean/DLNFibre/DLN/Aoyagi/Lemma5DisplayedVector.lean`, next to the selected
cutpoint and block-width API.  The nearby positive bridges keep block-local or
index-level dominance hypotheses explicit.

## Checks

Controller verification for the first Lean check:

```text
lake env lean DLNFibre/DLN/Aoyagi/Lemma5DisplayedVector.lean
```

The initial proof needed explicit `Fin.sum_univ_four` expansion for the finite
sum goals.  After that correction, the file type-checks.

## Residual Risks

This theorem does not decide whether a stronger source interpretation of
Aoyagi Definition 3 includes an implicit no-duplicate or position-level
dominance condition.  Under the text currently reproduced in this expedition,
no such extra hypothesis is formalised.

It also does not construct the equation `(5)` vector, prove its admissibility,
count charts, prove pole order, prove normal crossings, or extract RLCT.
