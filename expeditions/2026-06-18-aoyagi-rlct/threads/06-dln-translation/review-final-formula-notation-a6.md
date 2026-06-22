# Review - A6 Final Formula Notation

Date: 2026-06-22.

Reviewer posture: xhigh source check plus controller review.

Verdict: pass as a formula-notation and rational-arithmetic slice.

## Source Fidelity

The source checker confirmed that Aoyagi Definition 3 and Theorem 2 are on
PDF pp. 8-9, and that the same algebra reappears around pp. 24-25.  The Lean
translation preserves the two source notational hazards:

- the selected object and the ceiling integer are not both called `M`;
- selected widths are kept as an indexed family, not merely a value set.

The denominator in Aoyagi's average is `ell`, although there are `ell+1`
selected widths.  The Lean definitions intentionally use `(ell : Rat)` as the
denominator and require `0 < ell` in the supplied ceiling datum.

## Arithmetic Review

The Lean proof of `selectedWidthAverage_eq_ceil` is the source calculation

```text
sum selected = ell*(ceilWidth - 1) + a
             = ell*ceilWidth + (a - ell).
```

The Lean proof of the ceil-to-expanded formula is the source square expansion.
It keeps the pole-order symbol out of theorem names except as
`theorem2OrderFormula`, so it cannot be confused with the repository's
component-count `theta`.

## Boundary Review

The slice does not assert that the formula is the RLCT.  It does not prove
normal crossings, pole order, chart coverage, Lemma 4/5 exponent minimisation,
or the analytic extraction theorem.  Those remain outside this notation file.

## Applied Hardening

- Replaced Nat subtraction for `M^(s)=H^(s)-r` by integer subtraction.
- Added explicit rank-width bridge lemmas: under pointwise `r <= H s`, the
  integer reduced width agrees with Nat subtraction coerced to `Int` and is
  nonnegative.  Selected-width and Nat-indexed accessor wrappers keep the same
  pointwise hypothesis explicit.
- Renamed the Definition 3 package to `AoyagiDefinition3CeilData`, making it
  data rather than a `Prop` interface.
- Added `ell_pos` and `aParam_pos`, while keeping `aParam_le`.
- Used `theorem2OrderFormula` instead of a bare `theta` or `rlctOrder` name.
- Added the second-to-third displayed-form equality, not only the
  average-to-ceiling equality.

## Residual Risks

- The selected cutpoint inequalities from Definition 3 are still not encoded.
- The formula layer does not prove that a supplied ceiling datum exists for a
  source-selected family.
- The current selected value set helper is only a naming aid; it must not be
  used in place of the indexed selected widths for sums.

## Verification

Controller verification passed:

```text
lake env lean DLNFibre/DLN/Aoyagi/FinalFormula.lean
lake build DLNFibre.DLN.Aoyagi.FinalFormula
lake build DLNFibre
scripts/sorries
git diff --check
```

The full build reported only pre-existing Core warnings.  The scanner reported
`0 sorry`, `0 #exit`, `0 native_decide`, and `0 axiom`.
