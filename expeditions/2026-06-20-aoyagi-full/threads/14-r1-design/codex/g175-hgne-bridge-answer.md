1. **THE LIGHTEST ROUTE:** choose **(b), but not the line/ray variant**: use a direct last-layer Fubini/fiber argument. It is lightest in v4.29 because Mathlib already has “proper finite-dimensional real subspace has volume zero,” so you avoid proving any general multivariate-polynomial zero-set theorem.

2. **KEY Mathlib Lemmas:**
   `Measure.addHaar_submodule` [confident]; `Matrix.mulLeftLinearMap`, `Matrix.mulLeftLinearMap_apply`, `Matrix.mulLeftLinearMap_eq_zero_iff` [confident]; `LinearMap.ker_eq_top` [confident]; `ae_prod_iff_ae_ae`, `Measure.prod_apply`, `Measure.prod_prod` [confident]; `MeasurableEquiv.piFinSuccAbove`, `measurePreserving_piFinSuccAbove`, `volume_preserving_piFinSuccAbove` [confident]; `ae_iff`, `ae_restrict_of_ae`, `measure_mono_null`, `measure_union_null`, `Measure.preimage_null_of_map_null` [confident]. Local repo lemmas: `measurePreserving_paramsEquivFlat`, `optimalSet_eq_loss_zero`, `prod_one_layer` [confident]. No ready `MvPolynomial` null-zero-set lemma in v4.29 [confident enough]; `Polynomial.finite_setOf_isRoot` exists [confident] but is for the heavier route.

3. **SUBLEMMA DECOMPOSITION:**
   1. `prod_split_last`: after splitting `Params M` as `(prefix params) × (last matrix)`, prove `prod M A = prod Mprefix Aprefix * Blast`. Estimate: 25-50 LoC.
   2. `last_fiber_null_of_prefix_ne_zero`: for fixed `P ≠ 0`, `{B | P * B = 0}` is `LinearMap.ker (Matrix.mulLeftLinearMap _ ℝ P)`, a proper submodule, hence null by `Measure.addHaar_submodule`. Estimate: 15-30 LoC.
   3. `prod_zero_null_by_layers`: induction on `L`; use Fubini on the split-last product, induction for prefix-bad fibers, and step 2 for good-prefix fibers. Estimate: 60-100 LoC.
   4. `dlnLoss_zero_iff_prod_zero`: specialize/use `optimalSet_eq_loss_zero` with `B = 0`. Estimate: 5-15 LoC.
   5. `transport_to_flat_restrict`: transport the global a.e. statement through `paramsEquivFlat`; choose `U = univ`, then apply `ae_restrict_of_ae`. Estimate: 15-30 LoC.

4. **BIGGEST RISK:** dependent-index splitting/casts for “prefix product times last layer,” not measure theory. Cheapest mitigation: prove the null theorem on an explicit split product type using `MeasurableEquiv.piFinSuccAbove`, keep algebraic statements close to `prodAux`, and use `Matrix.mulLeftLinearMap` instead of defining a custom linear map.

5. **AVOID MEASURE-ZERO ENTIRELY?** No, for `L ≥ 1`. Every neighborhood of `0` contains `0`, and `(paramsEquivFlat M).symm 0 = 0`, while `prod M 0 = 0`, hence `dlnLoss M 0 0 = 0`. A small open set around a nonzero witness exists by continuity, but it is not a neighborhood of the origin and cannot discharge this `hGne`.
## crux2 route de-risk (post-consult, 2026-06-22)

Probed both routes' Lean foundations:
- **addHaar route (Codex's recommendation):** `Measure.addHaar_submodule` EXISTS at v4.29 and is the right
  tool, BUT bare `Matrix (Fin k) (Fin n) ℝ` has NO `MeasureSpace` instance, and giving it one (via the
  Pi instance `letI`) is not enough — `addHaar_submodule` needs the matrix volume to be
  `IsAddHaarMeasure`, which requires the full `NormedAddCommGroup` + `NormedSpace ℝ` + matching-Haar
  instance stack on the matrix type. Real instance-plumbing friction (the matrix-factor measure setup).
- **Fubini-to-1D (controller's suggestion):** works on the FLAT space `Fin N → ℝ` (clean volume) but uses
  the analytic 1-D `IsolatedZeros` + slicing.
- **#69 overlap:** the controller dispatched the general nonzero-MvPolynomial-null lemma to a sibling;
  the addHaar route (option (a)) makes #69 unnecessary AND dodges the prod→MvPolynomial encoding.

Decision (route + #69 ownership + matrix-instance approach) put to the controller. Both routes have real
cost; the addHaar route is lighter in principle but needs the matrix Haar-instance stack set up.
