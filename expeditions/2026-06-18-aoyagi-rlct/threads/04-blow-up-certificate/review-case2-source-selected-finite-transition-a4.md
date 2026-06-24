# Review - A4 Case 2 source-selected finite transition

Date: 2026-06-24.

Reviewer: xhigh independent reviewer `Bohr the 2nd`.

Verdict: pass.

## Scope Reviewed

- Lean changes in `lean/DLNFibre/DLN/Aoyagi/BlowupArithmetic.lean`;
- Lean changes in
  `lean/DLNFibre/DLN/Aoyagi/SelectedEntryNormalCrossing.lean`;
- reproduction note
  `reproduction-case2-source-selected-finite-transition-a4.md`;
- statement card
  `statement-card-a4-case2-source-selected-finite-transition.md`.

## Findings

No mathematical or Lean-fidelity blocking findings.

The reviewer confirmed that the denominator is the normalized target
coordinate, not the finite center value `u*x_q`.  In the generic theorem the
hypothesis is

```text
selectedEntryNormalizedMap sourcePivot residual targetPivot != 0
```

and the target residuals divide by that same normalized value.  The Case 2
supplied-pivot wrapper and chart-index wrapper preserve the same denominator
condition.

The reviewer found no analytic or `Q/P` overclaiming.  The Lean docstrings
and docs restrict the result to finite selected-entry chart-map equality and
explicitly exclude analytic transition regularity, chart coverage, Q/P
reduced-block transition, successor/suffix production, global normal
crossings, pole order, and RLCT extraction.

The Lean statements match the reproduction: source values `d_i = u*x_i`,
overlap condition `x_q != 0`, target data `u_q = u*x_q` and
`y_i = x_i/x_q`, and equality of finite center values only.

## Verification

The reviewer ran:

```text
lean/scripts/lb DLNFibre.DLN.Aoyagi.SelectedEntryNormalCrossing
lean/scripts/sorries
git diff --check
```

The controller additionally ran:

```text
lean/scripts/lb DLNFibre.DLN.Aoyagi.SelectedEntryNormalCrossing
lean/scripts/lb DLNFibre
lean/scripts/sorries
git diff --check
```

The sorry audit reported `0 sorry`, `0 #exit`, `0 native_decide`, and
`0 axiom`.  The full build still reports pre-existing unrelated Core/style
warnings.
