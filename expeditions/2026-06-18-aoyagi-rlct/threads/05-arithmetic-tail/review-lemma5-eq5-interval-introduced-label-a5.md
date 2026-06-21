# Review - Lemma 5 equation (5) interval and introduced-label wrappers

Reviewers: controller review plus xhigh scouts `Arendt the 2nd`,
`Heisenberg the 2nd`, and exact-diff reviewer `Turing the 2nd`.
Verdict: valid as conditional finite-set/API bookkeeping.

## Findings

No issue was found in the controller check of the Lean statements.
No issue was found in the exact-diff review of the two Lean files.

The inserted-set count is a direct consequence of already-proved facts:

```text
card(strict Eq5 offsets) = min(excess_p,p-1)
excess_p = p
Htilde_p notin strict Eq5 offsets
```

in the rising region.  Therefore inserting `Htilde_p` gives cardinality
`p=excess_p`.

The subset theorem is also source-faithful: lower endpoint membership is just
the lower bound of the closed same-coordinate interval, and strict offset
membership was already proved to imply same-coordinate interval membership.

The introduced-label wrapper is an API adapter.  It combines:

- own-block interval membership from the supplied Eq5 branch;
- the existing own-block actual-label wrapper;
- the generic post-advance rule `introducedLabel_of_eq_stage_le`.

## Source Fidelity

The theorem names and docstrings correctly say `intervalValue`,
`offsetValueSet`, and `introducedLabel`, not Lemma 5 or order count.  The
explicit width lower bound remains in the source-label wrapper, which is
required by the duplicate-width obstruction already formalised in this
expedition.

## Checks

Controller checks:

```text
lake env lean DLNFibre/DLN/Aoyagi/Lemma5DisplayedVector.lean
lake env lean DLNFibre/DLN/Aoyagi/Lemma5SourceLabel.lean
lake build DLNFibre.DLN.Aoyagi.Lemma5SourceLabel
```

passed before this note was finalised.  The exact-diff reviewer also ran
`git diff --check c07e331 -- ...` and both touched Lean files.

## Residual Risks

This is not displayed-vector construction.  It does not prove terminal
`tilde t=0`, vector admissibility, chart coverage, Case 1(2) sequence,
pole order, normal crossings, or RLCT extraction.
