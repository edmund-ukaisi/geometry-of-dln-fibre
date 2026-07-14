### Q1

[FACT: Mathlib v4.29 has] `Matrix.IsHermitian.eigenvalues`, `eigenvalues₀`, `eigenvalues₀_antitone`, and `eigenvectorUnitary`.  
[FACT: Mathlib v4.29 has] Matrix measurability through its function type, with `measurable_pi_apply` and `measurable_pi_lambda`.  
[FACT: Mathlib v4.29 lacks] any `Continuous` or `Measurable` theorem for those eigenvalue/eigenvector definitions.  
[FACT: Mathlib v4.29 has] `Matrix.IsHermitian.cfc`, `cfc_eq`, `ContinuousOn.cfc`, and `Continuous.cfc_of_mem_nhdsSet`.  
[FACT: Mathlib v4.29 lacks] a packaged Borel functional calculus or named sharp `spectralProjection`.  
[FACT: Mathlib v4.29 has] `eigenvectorUnitary` only as a pointwise classical choice through `eigenvectorBasis`, with no parametric regularity.  
[INFERENCE] Ordered eigenvalues are mathematically continuous and Borel frames exist, but global continuous eigenframes generally do not: crossings permit rotations, while signs and eigenline bundles obstruct continuity even off crossings.  
[INFERENCE] A measurable sharp projection can be constructed from continuous ramp functions using CFC continuity, `tendsto_cfc_fun`, and `measurable_of_tendsto_metrizable`, but v4.29 does not package that lemma.

### Q2

[FACT: repository, not a Mathlib claim] The actual witness in `shell_corankOffSector_le` is `ofReal (Cresid …) * Wenn Z`, and `Wenn Z` contains no `U_s`; `U_s` proves only `Wenn Z < ⊤`.  
[FACT: Mathlib v4.29 has] `Measurable.lintegral_prod_right`, so an explicit-bound restatement could prove measurability of `Wenn` from the jointly measurable determinant-Gram integrand.  
[INFERENCE] Thus one may choose a frame separately inside each pointwise proof and eliminate it before forming the outer integrand; no measurable choice function is required.  
[INFERENCE] A measurable spectral projection is also viable, but it adds work without improving this logical interface.  
[FACT: repository plus Mathlib v4.29] `strongBlock_lintegral_lt_top` already encloses the rotated box using an orthogonal extension, and `Matrix.entry_norm_bound_of_unitary` bounds every extension entry by one.  
[INFERENCE] Replacing its frame-dependent radius by the uniform radius `M₂` yields one finite constant independent of both `Z` and `U_s`, making option (c) the cheapest route.  
[FACT: Mathlib v4.29 lacks] the needed multivariate-polynomial null-zero-set theorem, although this repository has `MvPolynomial.ae_eval_ne_zero`; it makes `det (ZZᵀ-ε²I)=0` null because that polynomial is nonzero.  
[INFERENCE] Option (b) is therefore possible but still requires local frame charts and does not remove the global continuous-frame obstruction.

### Q3

[INFERENCE] The projection algebra is sound: congruence sends `ZZᵀ ⪰ ε²P` to `AZZᵀAᵀ ⪰ ε²APAᵀ`.  
[FACT: Mathlib v4.29 has] `Matrix.PosSemidef.mul_mul_conjTranspose_same`; the repository supplies `det_le_det_of_posSemidef_sub` for the determinant comparison.  
[INFERENCE] For a symmetric rank-`m` projection, a pointwise orthonormal factorization `P=UUᵀ` gives `APAᵀ=(AU)(AU)ᵀ`, exactly recovering the existing elimination argument.  
[INFERENCE] That factorization need not be measurable when it is used only to prove a uniform conclusion that does not mention `U`.  
[FACT: Mathlib v4.29 lacks] a packaged measurable map from rank-`m` projections to rectangular orthonormal frames.  
[FACT: Mathlib v4.29 has] `CFC.sqrt` and `CFC.sqrt_mul_sqrt_self`, but no `Matrix.PosSemidef.sqrt`; moreover, the square root of a projection is the same square projection, not an `M₂ × m` factor.  
[INFERENCE] A measurable frame could be built by finitely partitioning according to the first nonsingular principal minor and applying explicit Gram–Schmidt or inverse-square-root normalization, but that is substantial new infrastructure.

### Q4

[FACT: Mathlib v4.29 lacks] a measurable eigenframe or measurable projection-to-Stiefel selector theorem.  
[INFERENCE] A Borel selector exists mathematically, but insisting on formalizing it is a genuine Mathlib API gap rather than a banked-adjacent lemma.  
[INFERENCE] The Borel spectral-projection lemma alone would be bounded CFC labour, yet it is unnecessary here.  
[INFERENCE] The smallest native workaround is to strengthen the banked pointwise result to the following selector-erasing uniform statement:

```lean
theorem shell_corankOffSector_uniform_le
    {a b M₂ m n : ℕ} (hbm : b ≤ m) (hmM : m ≤ M₂)
    {ε c' : ℝ} (hε : 0 < ε)
    (haM : (a : ℝ) < (m : ℝ) - b + 1)
    (hc' : (a * b : ℝ) / 2 < c') :
    ∃ K : ℝ≥0∞, K < ⊤ ∧
      ∀ (Z : Matrix (Fin M₂) (Fin n) ℝ), m ≤ Z.rank →
      (∃ U : Matrix (Fin M₂) (Fin m) ℝ,
        Uᵀ * U = 1 ∧
        (Z * Zᵀ - (ε ^ 2) • (U * Uᵀ)).PosSemidef) →
      ∀ (Ccross : Matrix (Fin a) (Fin n) ℝ)
        (sΓ : Set (Fin a → Fin b → ℝ)) (w : ℝ), 0 < w →
        ∫⁻ A_cor in matBox b M₂ 1,
          ∫⁻ Γ in sΓ, ENNReal.ofReal
            ((w + frobSq
              (Ccross + Matrix.of Γ * (Matrix.of A_cor * Z))) ^ (-c'))
        ≤ K * ENNReal.ofReal
            (w ^ (-(c' - (a * b : ℝ) / 2)))
```

VERDICT (a): A Borel frame selector exists mathematically, but its v4.29 formalization is a Mathlib gap.  
VERDICT (b): Use the `Z`-uniform majorant; neither a global selector nor a measurable projection is needed.  
VERDICT (c): Target `shell_corankOffSector_uniform_le` with the displayed signature.