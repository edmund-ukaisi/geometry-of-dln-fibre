# Review - A2 source-stratum local-subset local-source finite-integral consumer

Date: 2026-06-26.

Reviewers: xhigh scout check-ins from `Bohr the 2nd`, `Dirac the 2nd`, and
`Heisenberg the 2nd`, plus controller Lean/API review.

## Verdict

Accepted for the stated conditional measure-bookkeeping scope.

The scouts agreed that current Lean supports one-way p.13 product-coordinate
source-rank image membership, but not local source-rank coverage or raw-Haar
pushforward.  This theorem respects that boundary: it consumes a local
inclusion into a supplied `localSource` and does not attempt to prove the
inclusion.

## Checks

The proof calls the existing local-source finite-integral theorem, shrinks the
returned open set by `Ulocal`, and compares restricted product measures using
the subset

```text
(Uchart ∩ Ulocal) ∩ sourceStratum ⊆ Uchart ∩ localSource.
```

The added `[SFinite mu]` hypothesis is justified by the Mathlib
`Measure.restrict_prod_eq_prod_univ` route used for the product-measure
comparison.  It is a measure-theoretic bookkeeping condition, not a hidden
source-coverage assumption.

## Boundary

This is not an Aoyagi p.13 chart construction.  It does not prove exact-rank
openness, local inverse, source/image equality, raw determinant-chart
coverage, density/Jacobian transport, normal crossings, pole order, or RLCT.

The next source-moving target remains a genuine local source-coverage/inverse
theorem, or a source-backed theorem identifying the correct local source image
and transported measure.
