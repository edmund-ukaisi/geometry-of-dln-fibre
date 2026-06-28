# Review - A2 generic shear/product abs-det wrappers

Date: 2026-06-28.

Reviewer: xhigh `Avicenna the 2nd`.

Verdict: PASS.  No required fixes.

## Checks

- The four new lemmas are narrow and true:
  `linearEquiv_prodCongr_abs_det_eq_one`,
  `linearEquiv_skewProd_refl_refl_det_eq_one`,
  `linearEquiv_skewProd_refl_refl_abs_det_eq_one`, and
  `linearEquivUpperShear_abs_det_eq_one`.
- The order hypotheses `[CommRing R] [LinearOrder R] [IsOrderedRing R]` are
  adequate for this Mathlib pin: the imported absolute-value API uses this
  unbundled ordered-ring shape, and the determinant infrastructure already
  requires `[CommRing R]`.
- The proof dependencies are the existing product, skew-product, and
  upper-shear determinant lemmas plus `abs_mul`/simp.
- No name conflicts were found.
- The notes explicitly avoid claiming a retained-passive target normalizer,
  determinant equality for the raw coordinate map, measure transport, normal
  crossings, pole order, RLCT, or analytic extraction.
- No forbidden Lean proof markers were introduced in the modified Lean file or
  the two new notes.
