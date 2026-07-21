import DLNFibre.Core.Aoyagi.IdealInvariance
import Meta.Cordon

/-!
# `Core.Aoyagi.MonomialRLCT` — Object C: the monomial-ideal RLCT (Newton / S2 boxed rule)

**BLUEPRINT (v3).** The RLCT of a **sum of squared monomials** against a monomial Jacobian weight.
This is Aoyagi's boxed rule S2 (worked.tex:173–189): after the resolution, the pulled-back loss is a
monomial times a unit, and `rlct = min_j (hⱼ+1)/(2kⱼ)`.

## The soundness fix (v2 defect 2): the rule is stated at its genuine hypothesis, not axis-only

v2 asserted the **axis value** `⨅ⱼ (hⱼ+1)/(2·minᵢ eᵢⱼ)` from `kⱼ = minᵢ eᵢⱼ` alone. That is FALSE
for coupled monomial families: for `b = (u₀u₁², u₀²u₁)` (`e = ![[1,2],[2,1]]`) the axis value is `1`
but the true weighted threshold is `2/3` (a coupled Newton valuation the coordinate minima miss).

The rule holds under Aoyagi's own **divisibility chain** `b₁ | b₂ | … | b_M` (`DivChain`;
worked.tex:483–488), i.e. some generator's exponent vector is pointwise-minimal. That is exactly the
**principal normal-crossing** condition: with `b_{k₀} | b_k` for all `k`, the ideal `⟨b₁,…,b_M⟩` is
principal `= ⟨b_{k₀}⟩`, so `∑ bₖ² = b_{k₀}² · (unit)` with the unit nonvanishing at `0`, and the sum
collapses to a single dominant monomial `b_{k₀}` whose axis exponents `k_d = e_{k₀ d} = minₖ e_{k d}`
DO give the threshold. The coupled counterexample is correctly **excluded** — it is not a chain
(`not_divChain_coupled_example`).

The DLN divisors have unit multiplicity `k_d ∈ {0,1}` (worked.tex:495: `∑ bᵢ²` vanishes to order 2
along each `u_{s,k}=0`), so on binding axes `k_d = 1` and `2·rlct = minⱼ (hⱼ+1)` — an integer min of
divisor exponents, which is what Object D consumes.
-/

open MeasureTheory Set Filter Topology RLCT
open Meta.Cordon

namespace DLNFibre.Core.Aoyagi

/-! ## Monomials, the Jacobian weight, and the divisibility chain -/

/-- The monomial family `bₖ(u) = ∏_d u_d ^ (e k d)` of an exponent matrix `e : Fin M → Fin D → ℕ`. -/
noncomputable def monomialFam {M D : ℕ} (e : Fin M → Fin D → ℕ) : Fin M → (Fin D → ℝ) → ℝ :=
  fun k u ↦ ∏ d, (u d) ^ (e k d)

/-- The **monomial Jacobian weight** `W(u) = ∏_d |u_d| ^ (h_d)` — the absolute change-of-variables
determinant `|det Dg|` of a resolution chart in Aoyagi's normal form (worked.tex:177, 492–494). -/
def jacWeight {D : ℕ} (h : Fin D → ℕ) : (Fin D → ℝ) → ℝ :=
  fun u ↦ ∏ d, |u d| ^ (h d)

/-- **The divisibility chain / principal normal-crossing condition** (Aoyagi worked.tex:483–488):
some generator `b_{k₀}` divides every `bₖ`, i.e. `e k₀` is pointwise ≤ every `e k`. Under it the
monomial ideal `⟨b₁,…,b_M⟩` is principal (`= ⟨b_{k₀}⟩`) and the boxed axis rule applies. -/
def DivChain {M D : ℕ} (e : Fin M → Fin D → ℕ) : Prop :=
  ∃ k₀ : Fin M, ∀ k d, e k₀ d ≤ e k d

/-- The **binding axes** of an exponent vector `kexp`: the variables `u_d` it actually vanishes
along (`0 < kexp d`). Off these the germ is regular in `u_d` and contributes `+∞` to the boxed min
(excluded). -/
def bindingAxes {D : ℕ} (kexp : Fin D → ℕ) : Finset (Fin D) :=
  Finset.univ.filter (fun d ↦ 0 < kexp d)

/-- **The boxed monomial threshold** `min_{d : k_d>0} (h_d + 1)/(2 k_d)` (worked.tex:181), over the
binding axes of the dominant monomial's exponent `kexp`. Requires a binding axis to exist (the
singular regime — at a regular point the RLCT is `+∞`, out of scope). -/
noncomputable def monomialThreshold {D : ℕ} (kexp h : Fin D → ℕ)
    (hne : (bindingAxes kexp).Nonempty) : ℝ :=
  (bindingAxes kexp).inf' hne (fun d ↦ (h d + 1 : ℝ) / (2 * kexp d))

/-! ## The negative-example guard (defect 1/2): the coupled family is not a chain -/

/-- **Negative example (the v2 counterexample, guarded out).** `b = (u₀u₁², u₀²u₁)`
(`e = ![[1,2],[2,1]]`) is NOT a divisibility chain — neither exponent vector is pointwise ≤ the
other — so the axis rule of `monomialSumSq_wrlctAt_eq` does not apply to it. This matches the
verified truth that its weighted threshold is `2/3`, not the axis value `1`
(`∫ r·r²·r^(-6c) dr < ∞ ⟺ c < 2/3`). The `DivChain` hypothesis is exactly what excludes it. -/
theorem not_divChain_coupled_example :
    ¬ DivChain (M := 2) (D := 2) ![![1, 2], ![2, 1]] := by
  rintro ⟨k₀, hk₀⟩
  fin_cases k₀
  · exact absurd (hk₀ 1 1) (by decide)
  · exact absurd (hk₀ 0 0) (by decide)

/-! ## The strike-able reduction and the S2 rule (the analytic leaf) -/

/-- **STRIKE-ABLE leaf — the chain collapses the sum to a dominant monomial times a unit.** Under
`DivChain` with minimal generator `b_{k₀}`, `∑ₖ bₖ² = b_{k₀}² · U` where `U(u) = ∑ₖ (bₖ/b_{k₀})²` is
continuous with `U 0 = #{k : b_k = b_{k₀}} ≥ 1 > 0` (each `bₖ/b_{k₀}` is a monomial with nonnegative
exponents, vanishing at `0` unless `bₖ = b_{k₀}`). Polynomial bookkeeping; no new mathematics. -/
theorem exists_unit_sumSqFam_monomial {M D : ℕ} {e : Fin M → Fin D → ℕ} {k₀ : Fin M}
    (hchain : ∀ k d, e k₀ d ≤ e k d) :
    ∃ U : (Fin D → ℝ) → ℝ, ContinuousAt U 0 ∧ 0 < U 0 ∧
      ∀ u, sumSqFam (monomialFam e) u = (monomialFam e k₀ u) ^ 2 * U u := by
  classical
  -- `U u = ∑ₖ (bₖ/b_{k₀})²` where `bₖ/b_{k₀} = ∏_d u_d^(e k d − e k₀ d)` (an honest monomial:
  -- the exponents are `≥ 0` by the chain). At `0` only the `k₀` term survives, giving `U 0 ≥ 1`.
  refine ⟨fun u ↦ ∑ k, (∏ d, (u d) ^ (e k d - e k₀ d)) ^ 2, ?_, ?_, ?_⟩
  · -- `U` is a polynomial, hence continuous.
    refine Continuous.continuousAt ?_
    refine continuous_finset_sum _ (fun k _ ↦ ?_)
    exact (continuous_finset_prod _ (fun d _ ↦ (continuous_apply d).pow _)).pow 2
  · -- `0 < U 0`: the `k₀` summand is `1`, all summands are `≥ 0`.
    refine Finset.sum_pos' (fun k _ ↦ sq_nonneg _) ⟨k₀, Finset.mem_univ k₀, ?_⟩
    have h1 : (∏ d, (0 : Fin D → ℝ) d ^ (e k₀ d - e k₀ d)) = 1 := by
      refine Finset.prod_eq_one (fun d _ ↦ ?_)
      rw [Nat.sub_self, pow_zero]
    rw [h1]; norm_num
  · -- the collapse identity, term by term.
    intro u
    simp only [sumSqFam, monomialFam]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k _ ↦ ?_)
    rw [← mul_pow]
    congr 1
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl (fun d _ ↦ ?_)
    rw [← pow_add]
    congr 1
    have := hchain k d
    omega

/-- **Object C — the monomial RLCT (S2 boxed rule; the analytic frontier leaf).** For a monomial
family whose exponents form a divisibility chain with minimal generator `b_{k₀}`, against a Jacobian
weight `W = jacWeight h · unit` with `unit` continuous and nonzero at `0`, the weighted RLCT at the
origin is the boxed threshold `min_{d : k_d>0} (h_d+1)/(2 k_d)` on the dominant monomial's exponents
`k = e k₀`. This is Aoyagi's boxed rule S2 (worked.tex:181–189) — the one analytic input the paper's
method permits citing; here it is a `@[blueprint]` frontier leaf with a TRUE statement (the
monomial-integral / Newton computation for a single normal-crossing monomial times a unit). The
`DivChain` hypothesis is load-bearing: it is what makes the axis exponents `e k₀` the genuine orders
and excludes the coupled counterexample (`not_divChain_coupled_example`). -/
@[blueprint]
theorem monomialSumSq_wrlctAt_eq {M D : ℕ} {e : Fin M → Fin D → ℕ} {h : Fin D → ℕ}
    {W unit : (Fin D → ℝ) → ℝ} {k₀ : Fin M}
    (hchain : ∀ k d, e k₀ d ≤ e k d)
    (hbind : (bindingAxes (e k₀)).Nonempty)
    (hunit : ContinuousAt unit 0) (hunit0 : unit 0 ≠ 0)
    (hW : ∀ᶠ u in 𝓝 (0 : Fin D → ℝ), W u = jacWeight h u * unit u) :
    wrlctAt W (sumSqFam (monomialFam e)) 0 = monomialThreshold (e k₀) h hbind := by
  -- map: C-monomial-rule (S2 boxed monomial RLCT under principal normal crossing; worked.tex:181-189)
  sorry

/-- **Object C, DLN normal-crossing form: `2·rlct = minⱼ (hⱼ+1)`.** When every binding divisor has
**unit multiplicity** (`e k₀ d = 1` on the binding axes — the DLN case, worked.tex:495), the boxed
threshold is `½ · min` of the integer divisor exponents `h_d + 1`, so `2·wrlctAt = ⨅ binding (h_d+1)`.
This is the integer min-of-divisor-exponents Object D bridges to `qipMin`/`cCodim`. -/
@[blueprint]
theorem monomialSumSq_two_mul_wrlctAt_eq_min {M D : ℕ} {e : Fin M → Fin D → ℕ} {h : Fin D → ℕ}
    {W unit : (Fin D → ℝ) → ℝ} {k₀ : Fin M}
    (hchain : ∀ k d, e k₀ d ≤ e k d)
    (hbind : (bindingAxes (e k₀)).Nonempty)
    (hunit1 : ∀ d ∈ bindingAxes (e k₀), e k₀ d = 1)
    (hunit : ContinuousAt unit 0) (hunit0 : unit 0 ≠ 0)
    (hW : ∀ᶠ u in 𝓝 (0 : Fin D → ℝ), W u = jacWeight h u * unit u) :
    2 * wrlctAt W (sumSqFam (monomialFam e)) 0
      = ((bindingAxes (e k₀)).inf' hbind (fun d ↦ (h d + 1 : ℝ))) := by
  -- map: C-dln-unit-multiplicity (k_d = 1 ⟹ boxed min is ½·min integer divisor exponents)
  sorry

end DLNFibre.Core.Aoyagi
