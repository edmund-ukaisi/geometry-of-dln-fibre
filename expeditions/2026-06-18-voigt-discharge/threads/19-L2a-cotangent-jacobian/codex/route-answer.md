**1. ROUTE CHOICE**

Pick **(C)**: use Mathlib’s presentation cotangent-complex API for the quotient presentation, plus one split-augmentation lemma for the rational point.

This has the fewest absent-brick risks. The core exact sequence and Jacobian computation are already packaged:

`Algebra.Presentation.naive` [CONFIRMED] gives the presentation of `A = MvPolynomial σ k ⧸ span (range g)`.
`Algebra.Extension.exact_cotangentComplex_toKaehler` [CONFIRMED] gives
`I/I² → A ⊗[R] Ω[R⁄k] → Ω[A⁄k]`.
`Algebra.Generators.cotangentSpaceBasis_repr_one_tmul` and `cotangentRestrict_mk` [CONFIRMED] compute the Jacobian entries.

Avoid raw Route B as the main proof: the sequence
`m_R/m_R² → m_A/m_A²`
is mathematically right, but the exact quotient-by-image statement is not packaged. Avoid Route A alone: `A → k` conormal only gives surjectivity from `m_A/m_A²` to `k ⊗[A] Ω[A⁄k]`; injectivity needs a split-augmentation proof.

**2. THE KEY IDENTITY**

Let `ε : A →ₐ[k] k` be induced by `MvPolynomial.eval a`, and `m := RingHom.ker ε`.

Define the transpose Jacobian

```lean
Jt : (Fin m → k) →ₗ[k] (σ → k)
Jt c x = ∑ i, c i * MvPolynomial.eval a (MvPolynomial.pderiv x (g i))
```

Then prove this chain:

```text
m.Cotangent
  ≃ₗ[k] k ⊗[A] Ω[A⁄k]
  ≃ₗ[k] (k ⊗[A] P.toExtension.CotangentSpace) ⧸ range(baseChanged cotangentComplex)
  ≃ₗ[k] (σ → k) ⧸ range Jt
```

Lemmas carrying the arrows:

`m.Cotangent ≃ k ⊗[A] Ω[A⁄k]`: **ABSENT — prove by hand**. Precise goal: `KaehlerDifferential.kerCotangentToTensor k A k` is bijective for the split augmentation `ε` with section `algebraMap k A`.

Second arrow: use `Algebra.Extension.exact_cotangentComplex_toKaehler`, `Algebra.Extension.toKaehler_surjective`, `LinearMap.lTensor_exact`, `LinearMap.quotKerEquivOfSurjective` [all CONFIRMED].

Third arrow: use `AlgebraTensorModule.cancelBaseChange`, `KaehlerDifferential.mvPolynomialBasis_repr_apply`, `Algebra.Generators.cotangentSpaceBasis_repr_one_tmul`; range equality with `Jt` is **ABSENT — prove by hand**, using `P.span_range_relation_eq_ker` and `Algebra.Presentation.naive_relation_apply`.

Then:

```text
finrank k ((σ → k) ⧸ range Jt)
  = finrank k (ker jac)
```

Use `Submodule.finrank_quotient`, `LinearMap.finrank_range_add_finrank_ker`, and either `LinearMap.finrank_range_dualMap_eq_finrank_range` or `Matrix.rank_transpose` [CONFIRMED]. Need a small extensional lemma that `jac` is the dual/transpose of `Jt`.

**3. LOCALIZATION**

No clean one-shot finrank-preservation lemma found. Use `Ideal.tensorCotangentEquiv`.

For `T := Localization.AtPrime m`:

```text
T ⊗[A] m.Cotangent
  ≃ (m.map (algebraMap A T)).Cotangent
  = (IsLocalRing.maximalIdeal T).Cotangent
  = CotangentSpace T
```

Use `Ideal.tensorCotangentEquiv A T m` [CONFIRMED], `Algebra.TensorProduct.cancelBaseChange` [CONFIRMED], and `Localization.AtPrime.map_eq_maximalIdeal` [CONFIRMED].

Residue-field bookkeeping: `Ideal.ResidueField m` is definitionally the residue field of `Localization.AtPrime m`. Since `m = ker ε` and `ε` is surjective, get `A ⧸ m ≃ₐ[k] k`; combine with `Ideal.bijective_algebraMap_quotient_residueField` [CONFIRMED] to transport scalars from the local residue field to `k`.

For the final `k`-finrank, use `TensorProduct.lidOfCompatibleSMul` [CONFIRMED] for `k ⊗[A] m.Cotangent ≃ m.Cotangent`.

**4. ABSENT-BRICK VERDICT**

**Bounded. No genuinely absent commutative-algebra sub-library is needed.**

But there are three non-packaged helper lemmas:

1. Split augmentation cotangent equivalence:
`(ker ε).Cotangent ≃ₗ[k] k ⊗[A] Ω[A⁄k]`.
Estimate: 80–150 lines.

2. Range of base-changed presentation cotangent complex equals span of gradient rows.
Estimate: 80–150 lines.

3. Localization/global cotangent finrank comparison.
Estimate: 80–140 lines.

These are local glue lemmas, not multi-module sub-libraries.

**5. DECOMPOSITION**

1. `eval_desc_quotient`:
Define `ε : A →ₐ[k] k`; prove `Function.Surjective ε` and `RingHom.ker ε = m_A`.

2. `cotangent_equiv_tensor_kaehler_of_split_aug`:
For split `ε : A →ₐ[k] k`, prove `(RingHom.ker ε).Cotangent ≃ₗ[k] k ⊗[A] Ω[A⁄k]`.

3. `presentation_basechange_kaehler_coker`:
For `P := Algebra.Presentation.naive g`, prove `k ⊗[A] Ω[A⁄k]` is the quotient of `k ⊗[A] P.toExtension.CotangentSpace` by the range of the base-changed cotangent complex.

4. `presentation_cotangentSpace_eval_basis`:
Build `k ⊗[A] P.toExtension.CotangentSpace ≃ₗ[k] (σ → k)` and compute images of `D g_i`.

5. `range_baseChanged_cotangentComplex_eq_range_Jt`:
Under the previous equivalence, prove the range is `LinearMap.range Jt`.

6. `finrank_global_cotangent_eq_coker_Jt`:
Conclude `Module.finrank k m_A.Cotangent = Module.finrank k ((σ → k) ⧸ LinearMap.range Jt)`.

7. `finrank_coker_Jt_eq_finrank_ker_jac`:
Prove the linear algebra transpose/rank-nullity step.

8. `finrank_local_cotangent_eq_global`:
Use `Ideal.tensorCotangentEquiv` and residue-field transport to replace `CotangentSpace (Localization.AtPrime m_A)` by `m_A.Cotangent`.