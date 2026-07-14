1. **VERDICT: YES, certainly.** The inequality holds in `ℝ≥0∞` for every real `c'`, independently of thresholds. The likeliest implementation error is reversing `blockSplitEquiv κ` and its inverse during reindexing.

2. Dropping `IsUnit P` is sound at every threshold as domain monotonicity; only the finiteness inference is threshold-dependent. Indeed, for `u ≥ 1`, singular `P` form a determinant-zero Lebesgue-null set, so for the measurable nonnegative integrand this drop is actually equality. What fails at `T2` is that the resulting full off-shell majorant has threshold `T1`, hence can diverge for `T1 ≤ c' < T2`. If the prior hunt removed *only* `IsUnit`, its divergence also applies to the original integral; the substantial enlargement is dropping the shell.

3. Let `e := blockSplitEquiv κ`. Exactly,
\[
B(P.\mathrm{submatrix}\ e\ \mathrm{id})
=(B.\mathrm{submatrix}\ \mathrm{id}\ e^{-1})P,
\]
entrywise by reindexing the finite contraction sum. If `r : (Fin u ⊕ Fin a) ≃ Fin M0` and
`B' i k := B (r.symm i) (e.symm k)`, then
`(B' * P) i j = (B * Q_sub) (r.symm i) j`. Therefore `frobSq` agrees because finite sums of squares are invariant under row—and generally column—permutations.

4. **Circular for the intended induction, but valid standalone.** If shell finiteness is used to prove `RouteMBoxThresholdFinite M`, bounding every shell by that same unproved chain-`M` box gives no progress. Given `RouteMBoxThresholdFinite M` as an explicit hypothesis, however, the conditional theorem is legitimate. The `L=0` conclusion is unconditional through `routeMBoxThresholdFinite_mnp`.

5. Tonelli is sound: the integrand is nonnegative, and the raw reindexed integrand is measurable; the banked measure-preserving front split supplies the needed product-measure equality. Shell measurability is unnecessary merely to drop it, though required for any separate Fubini rewrite involving the shell. Ensure the finiteness theorem uses `c' : NNReal` (or handle real `c' ≤ 0` separately). Finally, “RLCT exactly `T1`” needs a lower/divergence result; the named hypothesis proves only finiteness below `T1`.