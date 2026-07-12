import DLNFibre.DLN.RLCT.Validate.RouteMSJCorankPeel
import DLNFibre.DLN.RLCT.Validate.RouteMSJProductTube

set_option linter.style.longLine false

/-!
# `DLNFibre.DLN.RLCT.Validate.RouteMSJOffSectorB1` — the `b=1` corank-integrability lemma (Obl-1)

**Thread `genm-sj5-domination` off-sector, Obligation 1.** The foundational off-sector estimate of the
`#5 DecoratedStepHyp` route-ii `(□)` discharge: for a SINGLE corank row (`b = 1`), the corank-block
integral (the freed-corner inner `Γ`-integral, integrated over the free corank block `A_cor`) is
bounded by a constant times a power of the fixed pivot energy `w`.

## The design (`offsector-il-design-cert.md` §2, §2a; decorrelated-Codex-concurred)

Write `Q_b = A_cor · Z` (the single corank row, `A_cor : 1×M₂` free, `Z : M₂×n` the deeper product).
Fixing the pivot energy `w > 0` and the cross-shift `Ccross` (the design's `G(w,Z)`; `w` is
`A_cor`-independent after the absorption CoV, so it is a genuine parameter along the `A_cor`-fibre):

    G := ∫_{A_cor ∈ box} [ ∫_Γ (w + frobSq (Ccross + Γ·(A_cor·Z)))^{−c'} dΓ ] dA_cor
       ≤ C₁ · w^{−(c'−a/2)}  +  C₂ · w^{−(c'−M₂/2)},   C₁,C₂ finite, w-independent.

via a **two-regime split** on `τ = ‖A_cor·Z‖ = σ_min(Q_b)` (b=1) vs `√w`:
* `τ ≥ √w` (`w ≤ frobSq(A_cor·Z)`): the coupling `Q_bQ_bᵀ = [τ²]` is PosDef, so the banked ATOM
  (`corankBlock_morsePeel_setLE`) applies, contributing `det(Q_bQ_bᵀ)^{−a/2} = τ^{−a}` and the shifted
  core; `∫_box τ^{−a}` is a FINITE box-clipped constant (`detGram_lintegral_lt_top` at `r=1`, needs
  `a < M₂`), giving the `w^{−(c'−a/2)}` part.
* `τ < √w` (`frobSq(A_cor·Z) < w`): the BOUNDED bound `≤ w^{−c'}·vol(box)` caps the would-be `τ^{−a}`
  blow-up; the small-`τ` box `{A_cor : frobSq(A_cor·Z) < w}` has volume `≲ w^{M₂/2}` (cube-clipping),
  giving the `w^{−(c'−M₂/2)}` part.

## The full-rank-tail hypothesis (`hZ`) and its scope — a literal-shape correction

The uniform constant needs the STRICT full-rank-tail bound `frobSq(A_cor·Z) ≥ c₀²·frobSq A_cor`
(equivalently `σ_min(Z) ≥ c₀`, i.e. ALL `M₂` singular values of `Z` bounded below). The design cert's
"top `M₂−1` singular values ≥ c₀" is INSUFFICIENT for the b=1 uniform estimate (decorrelated Codex,
`codex/obl1-statement-answer.md` Q2): with only the top `M₂−1` bounded below and `σ_min(Z)→0`, a log
already appears at `a=M₂−1` and the small-`τ` volume scales as `w^{(M₂−1)/2}`, not `w^{M₂/2}`. The
rank-drop strata (where fewer singulars survive) are a DEEPER flag level / shorter chain — Obl-3
(piece A, uniform adapted charts), NOT this lemma. Here `a < M₂` (strict) gives the clean uniform
constant with no log; `a = M₂` (the harmless log correction) is a flagged follow-up.

S2-FREE: the banked corank atom (`corankBlock_morsePeel_setLE`) + the box-clipped determinant integral
(`detGram_lintegral_lt_top`) + cube volume; no `monomial_rlct`. Intended axiom footprint
`[propext, Classical.choice, Quot.sound]`.
-/

namespace DLNFibre.DLN.RLCT

open Matrix MeasureTheory
open scoped BigOperators ENNReal

/-! ## Small algebraic facts about the single corank row `b = 1` -/

/-- **The `1×1` Gram determinant is the row's Frobenius square.** For a single row `v : Fin 1 → Fin n`,
`det (of v · (of v)ᵀ) = frobSq v`. -/
theorem det_gramRow {n : ℕ} (v : Fin 1 → Fin n → ℝ) :
    ((Matrix.of v) * (Matrix.of v)ᵀ).det = frobSq v := by
  rw [Matrix.det_fin_one]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply]
  rw [frobSq, Fin.sum_univ_one]
  exact Finset.sum_congr rfl (fun j _ => (pow_two (v 0 j)).symm)

/-- **The `1×1` Gram is PosDef when the row is nonzero.** For `v : Fin 1 → Fin n` with
`0 < frobSq v`, the coupling `of v · (of v)ᵀ` is positive definite. -/
theorem posDef_gramRow {n : ℕ} (v : Fin 1 → Fin n → ℝ) (hv : 0 < frobSq v) :
    ((Matrix.of v) * (Matrix.of v)ᵀ).PosDef := by
  have hM00 : ((Matrix.of v) * (Matrix.of v)ᵀ) 0 0 = frobSq v := by
    have := det_gramRow v; rwa [Matrix.det_fin_one] at this
  refine Matrix.posDef_iff_dotProduct_mulVec.mpr ⟨?_, ?_⟩
  · -- Hermitian: `A · Aᵀ = A · Aᴴ` over ℝ (`TrivialStar`), which is `isHermitian_mul_conjTranspose_self`.
    rw [show (Matrix.of v)ᵀ = (Matrix.of v)ᴴ from
      (Matrix.conjTranspose_eq_transpose_of_trivial (Matrix.of v)).symm]
    exact Matrix.isHermitian_mul_conjTranspose_self (Matrix.of v)
  · intro x hx
    have hx0 : x 0 ≠ 0 := by
      intro h0; apply hx; funext i; rw [Fin.eq_zero i]; simpa using h0
    have hval : star x ⬝ᵥ (((Matrix.of v) * (Matrix.of v)ᵀ) *ᵥ x) = (x 0) ^ 2 * frobSq v := by
      simp only [dotProduct, mulVec, Fin.sum_univ_one, Pi.star_apply, star_trivial, hM00]
      ring
    rw [hval]
    have hxsq : (0 : ℝ) < (x 0) ^ 2 := by
      rcases (sq_nonneg (x 0)).lt_or_eq with h | h
      · exact h
      · exact absurd ((pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0)).mp h.symm) hx0
    exact mul_pos hxsq hv

/-! ## The bounded atom (the `τ < √w` regime's inner-`Γ` bound) -/

/-- **The bounded corank atom.** Over any domain `s`, dropping the nonneg corank term, the freed
`Γ`-integral is bounded by the constant `w^{−c'}` times `volume s`: the core `w` lower-bounds the
integrand, and `−c' ≤ 0` makes the integrand `≤ w^{−c'}`. The atom-inapplicable branch's value. -/
theorem corankBlock_bounded_le {a n : ℕ} (Ccross : Matrix (Fin a) (Fin n) ℝ)
    (Qb : Matrix (Fin 1) (Fin n) ℝ) (c' : ℝ) (hc0 : 0 ≤ c') (w : ℝ) (hw : 0 < w)
    (s : Set (Fin a → Fin 1 → ℝ)) :
    ∫⁻ Γ in s, ENNReal.ofReal ((w + frobSq (Ccross + (Matrix.of Γ) * Qb)) ^ (-c'))
      ≤ ENNReal.ofReal (w ^ (-c')) * volume s := by
  have hle : ∀ Γ : Fin a → Fin 1 → ℝ, w ≤ w + frobSq (Ccross + (Matrix.of Γ) * Qb) :=
    fun Γ => le_add_of_nonneg_right (frobSq_nonneg _)
  calc ∫⁻ Γ in s, ENNReal.ofReal ((w + frobSq (Ccross + (Matrix.of Γ) * Qb)) ^ (-c'))
      ≤ ∫⁻ _Γ in s, ENNReal.ofReal (w ^ (-c')) := by
        refine lintegral_mono (fun Γ => ENNReal.ofReal_le_ofReal ?_)
        exact Real.rpow_le_rpow_of_nonpos hw (hle Γ) (neg_nonpos.mpr hc0)
    _ = ENNReal.ofReal (w ^ (-c')) * volume s := setLIntegral_const s _

/-- **A matrix with vanishing Frobenius square is zero.** `frobSq M = 0 → M = 0` (each entry's square
is a nonneg summand of the zero sum, hence zero). -/
theorem eq_zero_of_frobSq_eq_zero {p m : ℕ} (M : Fin p → Fin m → ℝ) (hM : frobSq M = 0) :
    M = 0 := by
  funext i j
  have hsum : ∑ i', ∑ j', (M i' j') ^ 2 = 0 := hM
  have h1 := (Finset.sum_eq_zero_iff_of_nonneg
    (fun i' _ => Finset.sum_nonneg fun _ _ => sq_nonneg _)).mp hsum i (Finset.mem_univ i)
  have h2 := (Finset.sum_eq_zero_iff_of_nonneg
    (fun _ _ => sq_nonneg (M i _))).mp h1 j (Finset.mem_univ j)
  simpa using (pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0)).mp h2

/-! ## Box-clipping: the corank weight is finite, the small-`τ` box is small -/

/-- **The corank weight is finite (box-clipped).** For `a < M₂` and the full-rank-tail bound
`frobSq(A·Z) ≥ c₀²·frobSq A`, the corank weight `∫_{box} frobSq(A·Z)^{−a/2}` is finite: the uniform
lower bound reduces it (up to `c₀^{−a}`) to `∫_{matBox 1 M₂ 1} det(A Aᵀ)^{−a/2}`, finite by
`detGram_lintegral_lt_top` (`r = 1 ≤ M₂`, `a < M₂ = M₂ − 1 + 1`). -/
theorem corankWeight_lt_top {a M₂ n : ℕ} (Z : Matrix (Fin M₂) (Fin n) ℝ) (c₀ : ℝ) (hc₀ : 0 < c₀)
    (haM : a < M₂)
    (hZ : ∀ A : Fin 1 → Fin M₂ → ℝ, c₀ ^ 2 * frobSq A ≤ frobSq (Matrix.of A * Z)) :
    ∫⁻ A in matBox 1 M₂ 1, ENNReal.ofReal ((frobSq (Matrix.of A * Z)) ^ (-(a : ℝ) / 2)) < ⊤ := by
  have hM₂ : 1 ≤ M₂ := by omega
  set s : ℝ := -(a : ℝ) / 2 with hs
  have hsnonpos : s ≤ 0 := by
    rw [hs]
    have h : (0:ℝ) ≤ (a:ℝ) := by positivity
    linarith
  -- The pointwise reduction to the isotropic weight via the uniform lower bound.
  have hpt : ∀ A : Fin 1 → Fin M₂ → ℝ,
      (frobSq (Matrix.of A * Z)) ^ s
        ≤ (c₀ ^ 2) ^ s * (frobSq A) ^ s := by
    intro A
    rcases eq_or_lt_of_le (frobSq_nonneg A) with hA | hA
    · -- frobSq A = 0 ⟹ A = 0 ⟹ frobSq (of A * Z) = 0, so both sides collapse.
      have hA0 : A = 0 := eq_zero_of_frobSq_eq_zero A hA.symm
      have hAZ : frobSq (Matrix.of A * Z) = 0 := by
        simp only [frobSq]
        refine Finset.sum_eq_zero (fun p _ => Finset.sum_eq_zero (fun k _ => ?_))
        have : (Matrix.of A * Z) p k = 0 := by
          simp only [Matrix.mul_apply, Matrix.of_apply]
          exact Finset.sum_eq_zero (fun m _ => by rw [show A p m = 0 by simp [hA0], zero_mul])
        rw [this]; ring
      rw [hAZ, ← hA]
      rcases eq_or_lt_of_le hsnonpos with hs0 | hspos
      · rw [hs0]; simp
      · simp [Real.zero_rpow (ne_of_lt hspos)]
    · -- 0 < frobSq A ⟹ use antitone rpow on the positive lower bound.
      have hpos : (0 : ℝ) < c₀ ^ 2 * frobSq A := by positivity
      calc (frobSq (Matrix.of A * Z)) ^ s
          ≤ (c₀ ^ 2 * frobSq A) ^ s := Real.rpow_le_rpow_of_nonpos hpos (hZ A) hsnonpos
        _ = (c₀ ^ 2) ^ s * (frobSq A) ^ s :=
            Real.mul_rpow (by positivity) (frobSq_nonneg A)
  calc ∫⁻ A in matBox 1 M₂ 1, ENNReal.ofReal ((frobSq (Matrix.of A * Z)) ^ s)
      ≤ ∫⁻ A in matBox 1 M₂ 1,
          ENNReal.ofReal ((c₀ ^ 2) ^ s) * ENNReal.ofReal ((frobSq A) ^ s) := by
        refine lintegral_mono (fun A => ?_)
        rw [← ENNReal.ofReal_mul (by positivity)]
        exact ENNReal.ofReal_le_ofReal (hpt A)
    _ = ENNReal.ofReal ((c₀ ^ 2) ^ s)
          * ∫⁻ A in matBox 1 M₂ 1, ENNReal.ofReal ((frobSq A) ^ s) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = ENNReal.ofReal ((c₀ ^ 2) ^ s)
          * ∫⁻ A in matBox 1 M₂ 1,
              ENNReal.ofReal (((Matrix.of A) * (Matrix.of A)ᵀ).det ^ s) := by
        congr 1
        refine setLIntegral_congr_fun (matBox_measurableSet 1 M₂ 1) (fun A _ => ?_)
        rw [det_gramRow]
    _ < ⊤ := by
        refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_
        have h := detGram_lintegral_lt_top (r := 1) (n := M₂) hM₂
          (a := (a : ℝ)) (by have : (a : ℝ) < (M₂ : ℝ) := by exact_mod_cast haM
                             push_cast; linarith)
        rw [hs]
        simpa using h

/-- **The small-`τ` corank box has volume `≲ w^{M₂/2}` (cube-clipping).** For the full-rank-tail bound
`frobSq(A·Z) ≥ c₀²·frobSq A` and `0 ≤ w`, the set `{A : frobSq(A·Z) < w}` is contained in the cube
`{A : ∀ k, |A 0 k| < √w/c₀}` (each coordinate square is `≤ frobSq A < w/c₀²`), whose volume is
`(2√w/c₀)^{M₂} = (2/c₀)^{M₂}·w^{M₂/2}`. -/
theorem smallCorank_volume_le {M₂ n : ℕ} (Z : Matrix (Fin M₂) (Fin n) ℝ) (c₀ : ℝ) (hc₀ : 0 < c₀)
    (hZ : ∀ A : Fin 1 → Fin M₂ → ℝ, c₀ ^ 2 * frobSq A ≤ frobSq (Matrix.of A * Z))
    (w : ℝ) (hw : 0 ≤ w) :
    volume {A : Fin 1 → Fin M₂ → ℝ | frobSq (Matrix.of A * Z) < w}
      ≤ ENNReal.ofReal ((2 / c₀) ^ M₂ * w ^ ((M₂ : ℝ) / 2)) := by
  set R : ℝ := Real.sqrt w / c₀ with hR
  have hRnn : 0 ≤ R := by rw [hR]; positivity
  have hRsq : R ^ 2 = w / c₀ ^ 2 := by
    rw [hR, div_pow, Real.sq_sqrt hw]
  -- the small-`τ` set sits inside the cube `∏ Ioo (-R) R`
  have hsub : {A : Fin 1 → Fin M₂ → ℝ | frobSq (Matrix.of A * Z) < w}
      ⊆ Set.univ.pi (fun _ : Fin 1 => Set.univ.pi (fun _ : Fin M₂ => Set.Ioo (-R) R)) := by
    intro A hA
    simp only [Set.mem_setOf_eq] at hA
    have hfrob : frobSq A < w / c₀ ^ 2 := by
      have h1 : c₀ ^ 2 * frobSq A < w := lt_of_le_of_lt (hZ A) hA
      rw [lt_div_iff₀ (by positivity)]; nlinarith [h1]
    simp only [Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Ioo]
    intro i k
    have hik : (A i k) ^ 2 ≤ frobSq A := by
      have : (A 0 k) ^ 2 ≤ ∑ j, (A 0 j) ^ 2 :=
        Finset.single_le_sum (fun j _ => sq_nonneg _) (Finset.mem_univ k)
      rw [frobSq, Fin.sum_univ_one]
      simpa [Fin.eq_zero i] using this
    have hik2 : (A i k) ^ 2 < R ^ 2 := by rw [hRsq]; linarith
    constructor
    · nlinarith [hik2, hRnn, sq_nonneg (A i k + R)]
    · nlinarith [hik2, hRnn, sq_nonneg (A i k - R)]
  calc volume {A : Fin 1 → Fin M₂ → ℝ | frobSq (Matrix.of A * Z) < w}
      ≤ volume (Set.univ.pi (fun _ : Fin 1 => Set.univ.pi (fun _ : Fin M₂ => Set.Ioo (-R) R))) :=
        measure_mono hsub
    _ = ENNReal.ofReal ((2 / c₀) ^ M₂ * w ^ ((M₂ : ℝ) / 2)) := by
        simp only [volume_pi_pi, Real.volume_Ioo, Finset.prod_const, Finset.card_univ,
          Fintype.card_fin, pow_one]
        rw [← ENNReal.ofReal_pow (by linarith [hRnn] : (0:ℝ) ≤ R - -R)]
        congr 1
        have hsqrt : (Real.sqrt w) ^ M₂ = w ^ ((M₂ : ℝ) / 2) := by
          rw [← Real.rpow_natCast (Real.sqrt w) M₂, Real.sqrt_eq_rpow, ← Real.rpow_mul hw]
          ring_nf
        rw [show R - -R = (2 / c₀) * Real.sqrt w by rw [hR]; ring, mul_pow, hsqrt]

/-! ## The main lemma — the `b=1` corank-integrability bound -/

/-- **Obl-1: the `b=1` corank-integrability bound (the foundational off-sector estimate).** For a single
corank row (`b = 1`), a fixed pivot energy `w > 0`, cross-shift `Ccross`, the deeper product `Z` on the
full-rank-tail chart (`frobSq(A·Z) ≥ c₀²·frobSq A`, `c₀ > 0`), `a < M₂`, and `c'` above the block Morse
threshold `a/2`, the corank-block integral (freed inner `Γ`-integral over any finite-measure domain
`sΓ`, integrated over the free corank block `A_cor ∈ matBox 1 M₂ 1`) is bounded by finite,
`w`-independent constants times the two shifted powers of `w`:

    ∫_{A_cor} [ ∫_{Γ∈sΓ} (w + frobSq (Ccross + Γ·(A_cor·Z)))^{−c'} ] dA_cor
      ≤ C₁ · w^{−(c'−a/2)}  +  C₂ · w^{−(c'−M₂/2)}.

Two-regime split on `frobSq(A_cor·Z)` vs `w`: the atom (`corankBlock_morsePeel_setLE`) where PosDef
holds, the bounded bound elsewhere; box-clipping (`corankWeight_lt_top`, `smallCorank_volume_le`) makes
`C₁, C₂` finite and uniform in `Z`. -/
theorem corankOffSector_b1_le {a M₂ n : ℕ} (Z : Matrix (Fin M₂) (Fin n) ℝ)
    (Ccross : Matrix (Fin a) (Fin n) ℝ) (c₀ w c' : ℝ)
    (hc₀ : 0 < c₀) (hw : 0 < w) (haM : a < M₂) (hc' : (a : ℝ) / 2 < c')
    (hZ : ∀ A : Fin 1 → Fin M₂ → ℝ, c₀ ^ 2 * frobSq A ≤ frobSq (Matrix.of A * Z))
    (sΓ : Set (Fin a → Fin 1 → ℝ)) (hsΓ : volume sΓ < ⊤) :
    ∃ C₁ C₂ : ℝ≥0∞, C₁ < ⊤ ∧ C₂ < ⊤ ∧
      ∫⁻ A_cor in matBox 1 M₂ 1,
          ∫⁻ Γ in sΓ, ENNReal.ofReal
            ((w + frobSq (Ccross + (Matrix.of Γ) * (Matrix.of A_cor * Z))) ^ (-c'))
        ≤ C₁ * ENNReal.ofReal (w ^ (-(c' - (a : ℝ) / 2)))
            + C₂ * ENNReal.ofReal (w ^ (-(c' - (M₂ : ℝ) / 2))) := by
  classical
  -- The pivot-energy sector `P` (where the atom's PosDef holds); it is measurable.
  set P : Set (Fin 1 → Fin M₂ → ℝ) := {A | w ≤ frobSq (Matrix.of A * Z)} with hPdef
  have hmeasF : Measurable (fun A : Fin 1 → Fin M₂ → ℝ => frobSq (Matrix.of A * Z)) := by
    have hentry : ∀ i j, Measurable (fun A : Fin 1 → Fin M₂ → ℝ => (Matrix.of A * Z) i j) := by
      intro i j
      simp only [Matrix.mul_apply, Matrix.of_apply]
      exact Finset.measurable_sum _ (fun k _ =>
        (((measurable_pi_apply k).comp (measurable_pi_apply i)).mul measurable_const))
    unfold frobSq
    exact Finset.measurable_sum _
      (fun i _ => Finset.measurable_sum _ (fun j _ => (hentry i j).pow_const 2))
  have hPmeas : MeasurableSet P := measurableSet_le measurable_const hmeasF
  set F : (Fin 1 → Fin M₂ → ℝ) → ℝ≥0∞ := fun A =>
    ∫⁻ Γ in sΓ, ENNReal.ofReal
      ((w + frobSq (Ccross + (Matrix.of Γ) * (Matrix.of A * Z))) ^ (-c')) with hFdef
  -- The finite corank weight `Wenn` (box-clipped).
  set Wenn : ℝ≥0∞ := ∫⁻ A in matBox 1 M₂ 1,
      ENNReal.ofReal ((frobSq (Matrix.of A * Z)) ^ (-(a : ℝ) / 2)) with hWdef
  have hWfin : Wenn < ⊤ := corankWeight_lt_top Z c₀ hc₀ haM hZ
  refine ⟨ENNReal.ofReal (Cresid a c') * Wenn, ENNReal.ofReal ((2 / c₀) ^ M₂) * volume sΓ,
    ENNReal.mul_lt_top ENNReal.ofReal_lt_top hWfin,
    ENNReal.mul_lt_top ENNReal.ofReal_lt_top hsΓ, ?_⟩
  -- Split the corank-block integral by `P` (atom regime) vs `Pᶜ` (bounded regime).
  have hunion : matBox 1 M₂ 1 = (P ∩ matBox 1 M₂ 1) ∪ (Pᶜ ∩ matBox 1 M₂ 1) := by
    rw [← Set.union_inter_distrib_right, Set.union_compl_self, Set.univ_inter]
  have hdisj : Disjoint (P ∩ matBox 1 M₂ 1) (Pᶜ ∩ matBox 1 M₂ 1) :=
    Set.disjoint_left.mpr (by rintro A ⟨hAP, _⟩ ⟨hAPc, _⟩; exact hAPc hAP)
  have hsplit : ∫⁻ A in matBox 1 M₂ 1, F A
      = (∫⁻ A in P ∩ matBox 1 M₂ 1, F A) + (∫⁻ A in Pᶜ ∩ matBox 1 M₂ 1, F A) := by
    conv_lhs => rw [hunion]
    exact lintegral_union (hPmeas.compl.inter (matBox_measurableSet 1 M₂ 1)) hdisj
  rw [hsplit]
  refine add_le_add ?_ ?_
  · -- REGION P (atom regime): the freed-corner atom, then drop the residual core and box-clip the weight.
    have hfz : frobSq (0 : Matrix (Fin 0) (Fin n) ℝ) = 0 := by simp [frobSq]
    have hcorepow : ∀ X : Matrix (Fin a) (Fin n) ℝ,
        (w + frobSq (0 : Matrix (Fin 0) (Fin n) ℝ) + frobSq X) ^ (-(c' - (a : ℝ) / 2))
          ≤ w ^ (-(c' - (a : ℝ) / 2)) := fun X =>
      Real.rpow_le_rpow_of_nonpos hw
        (by rw [hfz, add_zero]; exact le_add_of_nonneg_right (frobSq_nonneg _))
        (by linarith [hc'])
    -- pointwise atom bound on the sector `P`
    have hpt : ∀ A ∈ P ∩ matBox 1 M₂ 1,
        F A ≤ ENNReal.ofReal (Cresid a c' * w ^ (-(c' - (a : ℝ) / 2)))
                * ENNReal.ofReal ((frobSq (Matrix.of A * Z)) ^ (-(a : ℝ) / 2)) := by
      rintro A ⟨hAP, _⟩
      have hpos : 0 < frobSq (Matrix.of A * Z) := lt_of_lt_of_le hw hAP
      have hPD := posDef_gramRow (Matrix.of A * Z) hpos
      have hatom := corankBlock_morsePeel_setLE (Apiv := (0 : Matrix (Fin 0) (Fin n) ℝ))
        (Ccross := Ccross) (Qb := Matrix.of A * Z) hPD c' (by simpa using hc') w hw sΓ
      have hFeq : F A = ∫⁻ Γ in sΓ, ENNReal.ofReal
          ((w + frobSq (0 : Matrix (Fin 0) (Fin n) ℝ)
            + frobSq (Ccross + (Matrix.of Γ) * (Matrix.of A * Z))) ^ (-c')) := by
        simp only [hFdef]
        exact lintegral_congr (fun Γ => by rw [hfz, add_zero])
      rw [hFeq]
      refine le_trans hatom ?_
      rw [← ENNReal.ofReal_mul
        (mul_nonneg (Cresid_nonneg a c') (Real.rpow_nonneg hw.le _))]
      refine ENNReal.ofReal_le_ofReal ?_
      have hdet : ((Matrix.of A * Z) * (Matrix.of A * Z)ᵀ).det = frobSq (Matrix.of A * Z) :=
        det_gramRow _
      rw [hdet]
      simp only [Nat.cast_one, mul_one]
      rw [show Cresid a c' * w ^ (-(c' - (a : ℝ) / 2)) * frobSq (Matrix.of A * Z) ^ (-(a : ℝ) / 2)
          = frobSq (Matrix.of A * Z) ^ (-(a : ℝ) / 2) * Cresid a c' * w ^ (-(c' - (a : ℝ) / 2))
          from by ring]
      exact mul_le_mul_of_nonneg_left (hcorepow _)
        (mul_nonneg (Real.rpow_nonneg (frobSq_nonneg _) _) (Cresid_nonneg a c'))
    -- integrate the pointwise bound; pull the constant out and box-clip the corank weight.
    have hmeasPbox : MeasurableSet (P ∩ matBox 1 M₂ 1) :=
      hPmeas.inter (matBox_measurableSet 1 M₂ 1)
    calc ∫⁻ A in P ∩ matBox 1 M₂ 1, F A
        ≤ ∫⁻ A in P ∩ matBox 1 M₂ 1, ENNReal.ofReal (Cresid a c' * w ^ (-(c' - (a : ℝ) / 2)))
              * ENNReal.ofReal ((frobSq (Matrix.of A * Z)) ^ (-(a : ℝ) / 2)) :=
          lintegral_mono_ae ((ae_restrict_iff' hmeasPbox).mpr
            (Filter.Eventually.of_forall (fun A hA => hpt A hA)))
      _ = ENNReal.ofReal (Cresid a c' * w ^ (-(c' - (a : ℝ) / 2)))
            * ∫⁻ A in P ∩ matBox 1 M₂ 1, ENNReal.ofReal ((frobSq (Matrix.of A * Z)) ^ (-(a : ℝ) / 2)) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal (Cresid a c' * w ^ (-(c' - (a : ℝ) / 2))) * Wenn :=
          mul_le_mul_left' (lintegral_mono_set Set.inter_subset_right) _
      _ = ENNReal.ofReal (Cresid a c') * Wenn * ENNReal.ofReal (w ^ (-(c' - (a : ℝ) / 2))) := by
          rw [ENNReal.ofReal_mul (Cresid_nonneg a c')]; ring
  · -- REGION Pᶜ (bounded regime): drop the corank term (`≤ w^{−c'}·vol`), then cube-clip the domain.
    have hc0 : (0 : ℝ) ≤ c' := le_of_lt (lt_of_le_of_lt (by positivity) hc')
    have hPc : Pᶜ = {A : Fin 1 → Fin M₂ → ℝ | frobSq (Matrix.of A * Z) < w} := by
      ext A; simp only [hPdef, Set.mem_compl_iff, Set.mem_setOf_eq, not_le]
    have hAC : ENNReal.ofReal (w ^ (-c')) * ENNReal.ofReal (w ^ ((M₂ : ℝ) / 2))
        = ENNReal.ofReal (w ^ (-(c' - (M₂ : ℝ) / 2))) := by
      rw [← ENNReal.ofReal_mul (by positivity), ← Real.rpow_add hw]
      congr 2; ring
    calc ∫⁻ A in Pᶜ ∩ matBox 1 M₂ 1, F A
        ≤ ∫⁻ _A in Pᶜ ∩ matBox 1 M₂ 1, ENNReal.ofReal (w ^ (-c')) * volume sΓ :=
          lintegral_mono (fun A =>
            corankBlock_bounded_le Ccross (Matrix.of A * Z) c' hc0 w hw sΓ)
      _ = ENNReal.ofReal (w ^ (-c')) * volume sΓ * volume (Pᶜ ∩ matBox 1 M₂ 1) :=
          setLIntegral_const _ _
      _ ≤ ENNReal.ofReal (w ^ (-c')) * volume sΓ
            * ENNReal.ofReal ((2 / c₀) ^ M₂ * w ^ ((M₂ : ℝ) / 2)) := by
          refine mul_le_mul_left' (le_trans (measure_mono Set.inter_subset_left) ?_) _
          rw [hPc]
          exact smallCorank_volume_le Z c₀ hc₀ hZ w hw.le
      _ = ENNReal.ofReal ((2 / c₀) ^ M₂) * volume sΓ
            * ENNReal.ofReal (w ^ (-(c' - (M₂ : ℝ) / 2))) := by
          rw [ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ (2 / c₀) ^ M₂), ← hAC]
          ring

end DLNFibre.DLN.RLCT
