# Review - A6 Definition 3 Bridge

Date: 2026-06-22.

Reviewer posture: xhigh source check plus controller review.

Verdict: pass as a thin wrapper layer.

## Scope Review

The bridge does not introduce new mathematics beyond existing theorem calls.
It repackages:

- positivity of `ell` and `aParam`;
- selected-sum endpoint zero;
- lower/upper Htilde terminal zero;
- Htilde chain-bounds-to-terminal-zero;
- penultimate upper endpoint arithmetic;
- selected-width upper bounds and label bounds only under separately supplied
  source-selected inequalities.

The source-selected inequality remains an explicit hypothesis on the wrapper
theorems.  This avoids treating `AoyagiDefinition3CeilData` as the whole of
Definition 3.

## Boundary Review

The bridge does not prove vector admissibility, displayed-vector construction,
two-value increments, terminal-minimum exactness, pole order, normal
crossings, or RLCT extraction.  It also does not prove existence or uniqueness
of selected cutpoints or the ceiling datum.

The xhigh source checker confirmed that Definition 3's `1 <= a <= ell` safely
feeds the existing APIs requiring `a <= ell`, that the Htilde terminal endpoint
calculation is exactly the selected-sum cancellation on Aoyagi pp. 24-25, and
that selected-width upper bounds require the strict selected inequality as an
extra hypothesis.

## Verification

Controller verification passed:

```text
lake env lean DLNFibre/DLN/Aoyagi/Definition3Bridge.lean
lake build DLNFibre.DLN.Aoyagi.Definition3Bridge
lake build DLNFibre
scripts/sorries
git diff --check
```

The full build reported only pre-existing Core warnings.  The scanner reported
`0 sorry`, `0 #exit`, `0 native_decide`, and `0 axiom`.
