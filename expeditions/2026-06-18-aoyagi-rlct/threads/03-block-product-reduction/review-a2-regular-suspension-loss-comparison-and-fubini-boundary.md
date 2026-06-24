# Review - A2 regular-suspension finite loss comparison

Date: 2026-06-24.

Reviewer: xhigh `Schrodinger the 4th`.

Verdict: pass after wording repairs.

## Scope Checked

The reviewer inspected the dirty worktree slice in
`lean/DLNFibre/DLN/Aoyagi/RegularSuspensionCoordinates.lean` and the new
reproduction and statement-card documents.

## Findings

The Lean finite algebra checked out.  The reviewer confirmed that the
residual/corrected-residual estimates, finite row-column Cauchy-Schwarz,
`4P <= A` product-control lemma, and two factor-`2` comparison theorems support
the documented literal-vs-cleaned p. 13 square-sum comparison.

Two wording issues were required before commit:

- Lean docstrings for the factor-`2` theorems said the `F2` and `F3`
  square-sums are each at most `1`; the theorem hypothesis is the combined
  condition `squareSum(F2)+squareSum(F3) <= 1`.
- The statement card called the factor-`2` comparison "sharp"; Lean does not
  prove optimality of the constant.

Both wording issues were repaired.

## Checks

The reviewer reported:

```text
lake env lean DLNFibre/DLN/Aoyagi/RegularSuspensionCoordinates.lean passed
git diff --check on the requested files passed
no sorry, axiom, native_decide, or #exit found in the reviewed slice
```

The controller separately used the repository build wrapper:

```text
lean/scripts/lb DLNFibre.DLN.Aoyagi.RegularSuspensionCoordinates
```

and the focused module build passed before the wording repairs.

## Nonclaims Confirmed

No analytic chart, continuity-to-neighborhood shrink, regular-coordinate
theorem, Fubini/polar shift theorem, normal-crossing construction, pole-order
theorem, or RLCT extraction is asserted.
