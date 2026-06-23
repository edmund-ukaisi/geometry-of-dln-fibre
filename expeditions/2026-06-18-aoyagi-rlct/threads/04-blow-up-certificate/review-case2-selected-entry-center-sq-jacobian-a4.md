# Review - A4 Case 2 selected-entry center square and formal Jacobian

Date: 2026-06-23.

Verdict: PASS.

Reviewers:

- source/math fidelity: `Chandrasekhar the 2nd`, xhigh;
- Lean/API: `Dewey the 2nd`, xhigh.

## Source/Math Findings

No blocking source/math issue was found.  The square-sum identity is
source-faithful: Aoyagi p. 5 uses the sum of squares of ideal generators, and
the Case 2 chart on pp. 19-21 selects `d_(J+1,J+1)=u` while scaling every
other residual-block entry by `u`.

The formal determinant exponent is correct for the finite selected-entry
coordinate matrix.  After pivot-first ordering, the matrix is block lower
triangular:

```text
[ 1 0; y uI ].
```

Its determinant is `u` to the number of non-pivot coordinates.  The Case 2
wrapper ties that count to the erased displayed pivot and separately proves
that this erased-center cardinality is the full residual-block center
cardinality minus one.

## Required Caveats

This is only the initial selected-entry blow-up arithmetic.  Aoyagi's later
regular `P` and `Q` variable changes on pp. 20-21 still need separate
analytic/unit/Jacobian treatment before a full chart certificate can be
claimed.

The normalized square-sum factor is only a unit candidate at this finite
algebra layer.  No theorem here proves analytic nonvanishing on a real chart
neighbourhood.

## Lean/API Findings

No blocking Lean/API issue was found.  The names and statements denote exactly
what is proved:

- `selectedEntryCenterSq` is the finite square-sum.
- `selectedEntryCenterSq_selectedEntryChartMap` is the selected-entry
  substitution factorization.
- `selectedEntryPivotFirstJacobian` and
  `selectedEntryPivotFirstJacobian_det` are a formal block-matrix determinant
  certificate, not an analytic derivative theorem.
- `SelectedEntryChartFamilyData.centerSq_chartMap` projects the generic
  square-sum identity through supplied chart-family data.
- the Case 2 wrappers specialize the generic facts to the displayed
  residual-block pivot while keeping the determinant exponent and
  erase-cardinality fact separate.

`Mathlib.Data.Fintype.Sets` is justified because the determinant wrapper uses
an erased `Finset` as a finite type.  The square-sum lemmas are stated over
`CommSemiring`; the determinant theorem uses `CommRing`, matching the current
matrix determinant context and not creating meaningful API debt.

The only watchpoint is wording in the reproduction doc saying the selected
coordinate has loss exponent `1`.  This is acceptable because it is
immediately tied to the A0 convention and surrounded by the explicit
unit-candidate and no-A0-certificate caveats.

## Checks

Reviewers and controller ran:

```text
cd lean && lake env lean DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean
cd lean && lake build DLNFibre.DLN.Aoyagi.BlowupArithmetic
cd lean && scripts/sorries
git diff --check
```

`scripts/sorries` reports `0 sorry`, `0 #exit`, `0 native_decide`, and
`0 axiom`.
