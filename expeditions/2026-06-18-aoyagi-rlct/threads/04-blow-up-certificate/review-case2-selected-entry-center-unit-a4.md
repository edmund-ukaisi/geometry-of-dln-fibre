# Review - A4 Case 2 selected-entry center unit factor

Date: 2026-06-23.

Verdict: PASS.

Reviewers:

- source/math fidelity: `Pascal the 2nd`, xhigh;
- Lean/API: `Hegel the 2nd`, xhigh.

## Source/Math Findings

No source/math fidelity issue was found.  The slice matches Aoyagi's p. 5
sum-of-squares convention and the displayed Case 2 selected-entry chart on
PDF pp. 19-21: the pivot `(J+1,J+1)` maps to `u`, and every other
residual-block center coordinate maps to `u` times a residual coordinate.

The proved factor is exactly the normalized finite square-sum factor

```text
1 + sum y_i^2.
```

Under ordered commutative semiring hypotheses with the usual square
nonnegativity facts, the sum of squares is nonnegative, so the factor is
positive and nonzero.  Over an ordered field this nonzero element is a unit.
The ordered-field boundary is necessary; no arbitrary-field or complex-field
unit statement is source-faithful.

## Lean/API Findings

No Lean/API issue was found.  The theorem names and statements denote the
finite algebra they prove:

- `selectedEntryCenterSq_nonneg` proves nonnegativity of the finite
  square-sum;
- `selectedEntryCenterSqUnitFactor` names `1 + selectedEntryCenterSq`;
- `selectedEntryCenterSqUnitFactor_pos`,
  `selectedEntryCenterSqUnitFactor_ne_zero`, and
  `selectedEntryCenterSqUnitFactor_isUnit` prove positivity, nonzero, and
  field-unit status;
- the displayed Case 2 wrappers specialize these facts to
  `(case2ResidualBlockPivotEntries n S J).erase (J+1,J+1)`.

The field-unit theorem uses a fresh ordered-field variable, and the Case 2
unit wrapper omits the ambient `CommRing R` section variable.  This avoids the
semiring/ring typeclass diamond while keeping the generic positivity and
nonzero wrappers at semiring-level and the displayed wrappers available over
the ambient ordered commutative ring.

## Required Caveats

This is only pointwise finite algebra for one selected-entry normalized
square-sum factor.  It does not prove chart coverage, analytic unit control
for Aoyagi's later `P`/`Q` regular changes, a total loss unit, a differentiable
Jacobian or volume-form theorem, an A0 normal-crossing chart certificate, pole
order, or RLCT extraction.

## Checks

Controller ran:

```text
cd lean && lake env lean DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean
cd lean && lake build DLNFibre.DLN.Aoyagi.BlowupArithmetic
cd lean && lake env lean DLNFibre.lean
cd lean && lake build DLNFibre
cd lean && scripts/sorries
git diff --check
```

`scripts/sorries` reports `0 sorry`, `0 #exit`, `0 native_decide`, and
`0 axiom`.  The full build succeeds with only pre-existing Core warnings.

The xhigh reviewers worked read-only and made no file edits.
