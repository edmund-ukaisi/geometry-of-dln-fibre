<task>
Lean 4 + Mathlib v4.29. I am proving (sorry-free, no new axioms) one intermediate lemma of the
"Zariski cotangent = Jacobian kernel" formalisation. The crux (split-augmentation bijectivity) is DONE.
I need the cleanest Lean assembly for STEP 2 only.

SETUP (all CONFIRMED to compile):
- `k : Field`, `σ : Fintype, DecidableEq`, `R := MvPolynomial σ k`, `g : Fin m → R`,
  `I := Ideal.span (Set.range g)`, `A := R ⧸ I`. Point `a : σ → k`, `hg : ∀ i, eval a (g i) = 0`.
- `aug : A →ₐ[k] k` (descends `aeval a`), surjective; `m_A := RingHom.ker aug`.
- `jacobianTranspose g a : (Fin m → k) →ₗ[k] (σ → k)`, `c ↦ fun x ↦ ∑ i, eval a (pderiv x (g i)) • c i`
  (= `(jacobianMatrix g a)ᵀ.mulVecLin`, `jacobianMatrix g a i x = eval a (pderiv x (g i))`).

GOAL (the lemma):
  `finrank k (k ⊗[A] Ω[A⁄k]) = finrank k ((σ → k) ⧸ LinearMap.range (jacobianTranspose g a))`
(the `Algebra A k` instance is `aug.toRingHom.toAlgebra`, with `IsScalarTower k A k`.)

CONFIRMED BRICKS:
- Conormal of `R ↠ A`: `KaehlerDifferential.kerCotangentToTensor k R A : I'.Cotangent →ₗ[R] A ⊗[R] Ω[R⁄k]`
  where `I' = RingHom.ker (algebraMap R A) = I` (need `I' = I`: `Ideal.Quotient` ker is `I`).
  `mapBaseChange k R A : A ⊗[R] Ω[R⁄k] →ₗ[A] Ω[A⁄k]`, surjective (`mapBaseChange_surjective`),
  `exact_kerCotangentToTensor_mapBaseChange` (range kerCot = ker mapBaseChange), as A-submodules
  (the range lemma uses `.restrictScalars A`).
- `mvPolynomialBasis k σ : Basis σ R Ω[R⁄k]`, `Module.Free`, `mvPolynomialBasis_repr_apply x i = pderiv i x`.
- `AlgebraTensorModule.cancelBaseChange R A A k (A ⊗[R] Ω[R⁄k]) ... : k ⊗[A] (A ⊗[R] Ω[R⁄k]) ≃ₗ[?] k ⊗[R] Ω[R⁄k]`.
- `lTensor_exact Q hExact hSurj : Function.Exact (lTensor Q e) (lTensor Q f)` for right-exactness.
- `LinearMap.lTensor_range`, `TensorProduct.lTensor.equiv...`, `LinearMap.quotKerEquivOfSurjective`,
  `Submodule.finrank_quotient_add_finrank`, `LinearEquiv.finrank_eq`.
- `k ⊗[R] Ω[R⁄k] ≅ (σ → k)`: via `mvPolynomialBasis` and `Basis.baseChange`/`basis tensor`, plus
  `Finsupp.linearEquivFunOnFinite` / `Pi`-basis. (Ω[R⁄k] free with basis σ; tensor k over R gives σ→k.)

KEY DIFFICULTY: tracking the conormal generators through cancelBaseChange + mvPolynomialBasis so that
`range (k ⊗ kerCotangentToTensor) = range (jacobianTranspose)` under the iso `k ⊗[R] Ω[R⁄k] ≅ (σ→k)`.
The conormal sends `toCotangent ⟨g i⟩ ↦ 1 ⊗ D g_i`; base-changing and using `D g_i = ∑_x pderiv_x(g_i) dx`
should give the gradient row. But proving the RANGE equality (not just generator images) is the work.

I only need a FINRANK equality, not the explicit equiv. So I can avoid constructing the cokernel iso and
instead: finrank(k⊗Ω[A/k]) = finrank(k⊗(A⊗Ω[R/k])) − finrank(range of base-changed conormal), and
finrank(coker Jᵀ) = card σ − finrank(range Jᵀ); reduce to `finrank(range bc-conormal) = finrank(range Jᵀ)`
under the iso. Is that finrank-only route materially shorter in Lean? Or is building the explicit
`LinearEquiv ... ≃ₗ[k] (σ→k)/range Jᵀ` and `LinearEquiv.finrank_eq` cleaner?
</task>

<output_contract>
Terse. Three sections:
1. ROUTE: finrank-subtraction route vs explicit-coker-equiv route — which is shorter/safer in Lean v4.29,
   and the precise lemma sequence (named) for that route.
2. THE RANGE/GENERATOR STEP: the cleanest way to prove the conormal range maps to range(jacobianTranspose)
   under the `k ⊗[R] Ω[R⁄k] ≅ (σ→k)` iso. Give the key `simp`/`ext`/`Submodule.map_span` skeleton.
   Name the iso construction for `k ⊗[R] Ω[R⁄k] ≅ (σ → k)` precisely (which Mathlib basis/equiv lemmas).
3. PITFALLS: the 2–3 things most likely to fight back (scalar-tower/`restrictScalars` mismatches, the
   `I' = I` ker identification, `Module.Free`/`Finite` instances for finrank). For each, the fix.
</output_contract>

<grounding_rules>
- Tag any lemma name you are not CONFIDENT exists at v4.29 as "verify name".
- Prefer a route that minimises constructing explicit linear equivs by hand. I value the finrank-only
  shortcut if it is genuinely shorter.
- Be concrete about the `k ⊗[R] Ω[R⁄k] ≅ (σ→k)` iso — that is where I expect the most friction.
</grounding_rules>
