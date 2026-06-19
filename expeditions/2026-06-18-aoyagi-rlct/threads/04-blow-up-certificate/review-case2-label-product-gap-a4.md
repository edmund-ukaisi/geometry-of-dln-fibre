# A4 Case 2 Label-Product Gap Review

Date: 2026-06-19.

Scope: independent xhigh review of the finite label-product gap bridge for the
displayed Case 2 row-weight recurrence. This review covers the pen-and-paper
reproduction, the Lean statement shape, and the expedition ledgers/cards.

## Reviewers

- Lean/API reviewer: `Parfit the 2nd`.
- Source/ledger fidelity reviewer: `Laplace the 2nd`.
- Controller follow-up: patched the ledgers/cards to keep the caveats adjacent
  to the proved bridge.

## Verdict

The Lean API is narrow and mathematically honest. `levelProductStep` is only a
finite product over a supplied `Finset` of labels at a requested level, and the
gap lemmas prove only the resulting empty-product consequence. The Case 2
wrappers assume the supplied finite label set and do not identify it with
Aoyagi's actual introduced-label state.

No hidden global `Fintype` or `DecidableEq` assumptions on the label type were
found. The generic label-product lemmas expose only a local finite set of labels;
the displayed matrix wrapper remains a finite Nat-indexed matrix statement.

The source/ledger review found no mathematical contradiction in the new
reproduction/card, but flagged that the top-level summaries needed the same
caveats next to the new "proved" bridge and that the reproduction check path
should be explicit.

## Required Caveats

- The supplied finite `labels` set must be the same set used by the recurrence
  factor.
- Lean does not prove that this supplied set is Aoyagi's actual introduced-label
  set at the recursive state.
- Displayed Case 2 residual rows are `J+1..mu_S`, with
  `mu_S = prefixMinNat n S`.
- Displayed Case 2 residual columns remain actual-width columns
  `J+1..n_(S+1)`.
- The selected variable is counted once, in the updated weights
  `newWeight_i = u * oldWeight_i`.
- This is not an arbitrary-pivot chart, chart-coverage theorem,
  coordinate-regularity/Jacobian theorem, exponent update, transition invariant,
  termination proof, normal-crossing certificate, or RLCT extraction.

## Follow-up Edits

The controller added this review artifact and patched the statement card, A4
claim, priorities, synthesis, thread notes, repair blocker list, and theorem
ledger so that the caveats and review path survive compaction.
