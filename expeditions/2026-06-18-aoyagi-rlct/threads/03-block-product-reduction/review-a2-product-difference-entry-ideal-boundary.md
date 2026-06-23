# Review - A2 product-difference entry-ideal boundary

Date: 2026-06-23.

Reviewer: xhigh read-only scout `Dewey`.

## Verdict

Conditionally approved, with the required repository-convention fix applied:
the new `ProductReductionEntryIdealBoundary` import was moved to the end of
`DLNFibre.lean`.

The source-level block algebra and scalar entry-ideal transport are
mathematically sound and faithful to Aoyagi p. 13 at the intended elementary
scope.

## Math Review

- The p. 13 product-difference display is matched: after Theorem 3, Aoyagi has
  the block entries `Ctop - I`, `-F2`, `-F3`, and the lower-right correction
  `D - F3F2`.  The Lean identity keeps the same sign pattern and the correctly
  typed lower-right product `F3 * F2`.
- The determinant-unit transport is correct: determinant-unit left and right
  multiplication preserve the scalar matrix-entry ideal by inverse
  multiplication.
- The cleanup from
  `<X, F2, F3, D - F3F2>` to `<X, F2, F3, D>` is correct because each entry of
  `F3 * F2` is a finite sum of products of entries of `F3` and `F2`.
- The boundary wrapper stays scoped to scalar matrix-entry ideals.

## Caveats to Preserve

- This is not an analytic germ-ideal equality, RLCT invariance, normal
  crossings, pole order, or RLCT extraction.
- The local statements are `nhdsWithin` relative to the source rank stratum;
  they do not prove exact-rank openness or stratum nonemptiness.
- The lower-right block should remain described as the residual product exposed
  by the endpoint certificate, not as an unqualified raw product of original
  lower-right edge blocks.
- `IsUnit Ctop.det` is carried data in the endpoint package, but the
  entry-ideal equality itself uses determinant units only for the triangular
  endpoint multipliers.  No regular-suspension conclusion follows here.
