1. **Verdict:** **TRUE mathematically, cheaply true in Lean if isolated generically.** The opaque `Fintype.equivFin` does not matter for a uniform product box: any bijection/permutation preserves `∀ coord, x coord ∈ Set.Icc (-ε) ε`.

2. **Cheapest Honest Architecture: Route A, then use a separate explicit entry flattening.**
   1. Define `paramsBox M ε := {A | ∀ s i j, A s i j ∈ Set.Icc (-ε) ε}`.
   2. Prove the generic reshuffle lemma: for any equivalence of finite coordinate types, uniform pi-box membership is invariant. Likely by `Set.mem_pi`, `Set.mem_univ`, `Equiv.surjective.forall`; exact simp strength is an inference.
   3. Specialize it to `paramsEquivFlat M` to get  
      `(paramsEquivFlat M) ⁻¹' cubeBox (flatDim M) ε = paramsBox M ε`.
   4. Transport the target integral to `Params` using measure preservation. Known family: `lintegral_map`, `MeasurePreserving.lintegral_comp`; set-restricted exact name is likely `MeasurePreserving.setLIntegral_comp_preimage` or proved via indicators.
   5. Prove divergence on `paramsBox M ε` by monotonicity from a wedge image contained in `paramsBox`. Use `lintegral_mono_set` / `setLIntegral_mono` family; exact name inferred.
   6. Build the wedge in explicit entry coordinates, prove `dlnLoss M 0 (φ y) = u^2 * U y`, `0 < c0 ≤ U`, and crucially also `U ≤ C` on the chosen bounded slice.
   7. Apply existing `pivotBlowupOn` COV infrastructure, ultimately `lintegral_image_eq_lintegral_abs_det_fderiv_mul` and the existing monomial leaf `monomialIntegrand_lintegral_box_eq_top`.

3. **Coordinate Decision:** choose **3(ii)**: transport `Params M` to `Fin N → ℝ` via your own explicit entry enumeration and reuse `pivotBlowupOn`. Reason: proving a bespoke fderiv/determinant/COV theorem directly on dependent matrix coordinates is much more expensive than one explicit linear/measure-preserving coordinate seam.

4. **Biggest Trap + Test:** the comparison direction for the unit. For divergence, `U ≥ c0` alone gives an upper bound on the integrand; you need `U ≤ C` to lower-bound by the divergent monomial. Cheapest test: before generalizing, prove the exact inequality  
   `C' * u^(minAdm-1-2*c') ≤ chartIntegrand`  
   on the chart. If Lean only lets you prove the reverse from `U ≥ c0`, the proof is unsound.

5. **Deliverable Scope:** ship concrete `(3,3,4)` first if acceptable. It tests the Route A seam, the entry enumeration, the one-blow-up COV, and the unit comparison without symbolic `minAdm`/active-set bookkeeping. General `(M0,M1,M2)` should come after the certificate data API is stable.