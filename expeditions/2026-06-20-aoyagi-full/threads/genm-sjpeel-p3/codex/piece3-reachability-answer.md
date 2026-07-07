1. **VERDICT:** NO. `box ≤ Σ C_κ · gammaPeelIntegral κ t c'` is not sorry-free reachable from banked (i)-(iii) alone.

2. **Sub-lemma 2:** FALSE as the claimed identity. Mathematical fact from the block algebra:
   ```text
   A0 Q =
   [ A (Q_p + A⁻¹ B Q_b)
     C (Q_p + A⁻¹ B Q_b) + Γ Q_b ]
   ```
   so the exact integrand is
   ```text
   (‖A Q̃_p‖² + ‖C Q̃_p + Γ Q_b‖²)^(-c')
   ```
   with `Q̃_p = Q_p + A⁻¹B Q_b`, not `(P_tail_κ(Q) + ‖Γ Q_bκ(Q)‖²)^(-c')`. Also, the shear sends the `D`-box to a shifted `Γ`-box unless carried as an indicator. `schur_cov` gives Schur block algebra and Jacobian-one reparametrisation; it does not preserve Frobenius norm. Correct sorry-free replacement: a `schurShear_chart_lintegral_exact` lemma with the pivot-dependent integrand above.

3. **Sub-lemma 3:** No, not from plumbing. A uniform finite `C_κ` independent of `A'` requires an analytic fibre integral estimate over `(A,B,C)` and singular loci. For unrestricted `c'` it is even false: in the scalar case `∫_{[-1,1]} |aQ|^{-2c'} da` diverges for `c' ≥ 1/2` while the Γ-free target is finite for `Q ≠ 0`. In convergence ranges, proving the bound is still radial/Beta-type analytic content, not a consequence of measure preservation or Schur algebra.

4. **Honest decomposition:**
   - `pivotChartCover_lintegral_le_sum`: **[SORRY-FREE plumbing]**
   - claimed `schurShear_chart_lintegral`: **FALSE as stated**. Replace by **[SORRY-FREE plumbing]** `schurShear_chart_lintegral_exact_pivotDependent`.
   - `chartRadialBlock_to_gammaPeel`: **[IRREDUCIBLE analytic, keep named sorry]**
   - `sjBoundaryPeel_explicitGamma`: **[SORRY-FREE assembly]** once the analytic sorries are assumed.

   The two project-level sorries should be:
   - `schurChart_loss_to_gammaModel_bound`: handles non-orthogonal Schur factors, shifted Γ-domains, and comparison to the model loss.
   - `chartPivotFiber_betaBound_to_gammaPeel`: integrates pivot variables and supplies the radial/Beta exponent analysis and null-set hypotheses.

5. **Your analysis:** the block computation and “not an exact identity” conclusion are correct mathematical facts. The “exponent shift” point is the right analytic warning, but as a logical matter it does not alone disprove every coarser same-exponent upper bound in subcritical ranges; it shows such a bound needs genuine analytic proof. Null rank-deficient `Q(A')` fibres are also an a.e. issue, not automatically fatal globally.