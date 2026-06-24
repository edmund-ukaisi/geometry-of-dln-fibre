# Review - selected-entry affine transition regularity

Date: 2026-06-24.

Reviewer: Sagan the 3rd, xhigh independent check.

Status: PASS after wording repair.

## Verdict

No blocking mathematical issue.  The proposed predicate is sound as finite
selected-entry overlap algebra when formalised against the existing Lean
transition point and the overlap hypothesis is exactly

```text
selectedEntryNormalizedMap sourcePivot residual targetPivot != 0.
```

This matches the existing raw Lean lemmas for the transition point, chart-map
equality, inverse, and cocycle.

## Required correction applied

The reproduction note previously risked reading the overlap as "another center
entry is nonzero."  That is too strong if interpreted as the ambient value
`u * d != 0`, since it would exclude exceptional-divisor points with `u = 0`.
The note now states the correct condition: the normalised target coordinate
`d` is nonzero.

## Lean recommendations

- Keep the certificate finite and algebraic; do not call it analytic atlas
  transition regularity.
- Include a field exposing the full transition point formula, or otherwise
  make clear that the predicate references the actual
  `sourceChartTransitionPoint` definition where the residual formula
  `N_source(i) / denom` is present.
- Include fields for target coordinate, chart-map equality on the normalised
  overlap, inverse transition, self-transition, and cocycle on triple
  overlaps.
- Case 2 and displayed-pivot specialisations are source-faithful as finite
  all-pivot residual-block algebra, provided they keep the same normalised
  denominator condition and do not claim source production for every pivot.

## Nonclaims checked

The note and statement card do not claim analytic chart coverage, analytic
regular maps, source production, normal crossings, pole order, or RLCT
extraction.

## Second xhigh API review

Reviewer: Halley the 3rd.

Verdict: PASS with required API/wording corrections.

Additional requirements:

- Prefer a family-level certificate, because self-transition and cocycle data
  naturally belong to the whole chart family rather than to one fixed ordered
  pair.
- Provide pair extraction only as a convenience theorem.
- Use finite wording throughout; do not call this analytic transition
  regularity.
- State that this can instantiate a finite selected-entry transition predicate
  only when that predicate is explicitly chosen to mean the algebraic overlap
  identities.
- Do not imply that Aoyagi printed arbitrary non-displayed pivot charts; the
  all-pivot version is the standard finite selected-entry extension of the
  displayed blow-up chart algebra.

The Lean implementation follows these corrections with
`SelectedEntryFiniteAffineTransitionRegularFamily`,
`SelectedEntryFiniteAffineTransitionRegularPair`, and displayed-pivot pair
extraction from the family certificate.
