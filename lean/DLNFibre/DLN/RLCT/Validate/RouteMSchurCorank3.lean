import DLNFibre.DLN.RLCT.Validate.RouteMSchurDepth2
import DLNFibre.DLN.RLCT.Validate.RadialResidualPower

/-!
# `DLNFibre.DLN.RLCT.Validate.RouteMSchurCorank3` — the corank-3 recursion STEP (the first real firing)

The corank-3 instance of the rank-stratified radial-Schur recursion — the FIRST case where the recursion
genuinely fires (the residual Schur complement `Sc` becomes `2×2`, NOT a scalar, so it is a corank-2 core
that bottoms out in the closed `core_schur2_lt_top` at a SHIFTED exponent — not a Morse leaf). This
validates the inductive STEP `corank-r → corank-(r−1)`-at-shifted-exponent (cert §4 N4 / §3); the full
arbitrary-depth WellFounded-on-corank recursion is the next milestone.

## The threshold (CONFIRMED `c' < 4 = λ_{3,4}` — the JOINT-core SUM, not the corank-2 `2`)
The binding inner threshold is the SUM `jp/2 + λ_{r−j,p}` = (j=1, p=4 ⟹ `jp/2 = 2`) + (`λ_{2,4} = 2`) = 4
= ½·minAdm(3,3,4). Reusing the corank-2 threshold-`2` lemma for the corank-3 leaf would UNDERSHOOT (the
cert §6 trap: it drops the `+jp/2` Morse gain). The shifted-exponent peel is what carries the `+jp/2`.

## The mechanism (the inductive STEP)
`schurInner3_S_le` (the per-chart inner-S heart, at a fixed `3×3` angular `R` with pivot `(0,0)`):
`∫_{S ∈ matBox 3 4 T} frobSq (R·S)^{−c'} < ⊤` for `0 < c' < 4`, via:
* N2b (`schur_minorPivot_split`, `r=3, j=1`) → the JOINT split `frobSq (R·S) ≳ frobSq (R·S)_row0 (Morse,
  p entries) + frobSq (Sc · S_bot)` (`Sc` the `2×2` Schur complement, `S_bot` rows 1,2 of S);
* the SHIFTED-EXPONENT Morse peel of the top block (`radial_morse_residual_power_le`, threshold `p/2 = 2`)
  → the corank-2 residual at exponent `c' − 2`;
* the translation-domination `M22 ↦ Sc` (Jac ≡ 1, `lintegral_translate_le_local` +
  `rowShear_entry_le_one`) confines `Sc` to a fixed box → `core_schur2_lt_top` at exponent `c' − 2 < 2`.

The OUTER 9-chart radial-Δ cover (mirror of the corank-2 `matBox2_*` cover) assembling
`∫_Δ ∫_S frobSq (Δ·S)^{−c'} < ⊤` is built on top (`core_schur3_lt_top`).

## S2-hygiene
S2-FREE: the shifted peel (`radial_morse_residual_power_le`, `radial_ball_iff`-based), `core_schur2_lt_top`
(S2-free), the translation domination, the radial Jacobian dets. No `monomial_rlct`, no new axiom.
-/

namespace DLNFibre.DLN.RLCT

open MeasureTheory Set
open scoped ENNReal BigOperators

/-! ## The corank-3 outer radial-Δ 9-chart cover (mirror of the corank-2 `matBox2_*` atoms) -/

/-- Local `matToFlatEquiv 3 3 : (Fin 3 → Fin 3 → ℝ) ≃ᵐ (Fin 9 → ℝ)` (uncurry + the `Fin 3 × Fin 3 ≃ Fin 9`
index reindex). -/
noncomputable def matToFlat3 : (Fin 3 → Fin 3 → ℝ) ≃ᵐ (Fin (3 * 3) → ℝ) :=
  (MeasurableEquiv.piCurry (fun (_ : Fin 3) (_ : Fin 3) => ℝ)).symm.trans
    (MeasurableEquiv.arrowCongr'
      ((Equiv.sigmaEquivProd (Fin 3) (Fin 3)).trans finProdFinEquiv) (MeasurableEquiv.refl ℝ))

theorem measurePreserving_matToFlat3 :
    MeasurePreserving matToFlat3 (volume : Measure (Fin 3 → Fin 3 → ℝ))
      (volume : Measure (Fin (3 * 3) → ℝ)) := by
  unfold matToFlat3
  refine MeasurePreserving.trans ?_ (volume_preserving_arrowCongr'
    ((Equiv.sigmaEquivProd (Fin 3) (Fin 3)).trans finProdFinEquiv)
    (MeasurableEquiv.refl ℝ) (MeasurePreserving.id _))
  exact (measurePreserving_piCurry (fun (_ : Fin 3) (_ : Fin 3) => ℝ)
    (fun _ _ => (volume : Measure ℝ))).symm
    (MeasurableEquiv.piCurry (fun (_ : Fin 3) (_ : Fin 3) => ℝ))

/-- The flattened `Δ`-box on the `Fin 9` carrier: `[−T,T]^9`. -/
def flatBox3 (T : ℝ) : Set (Fin (3 * 3) → ℝ) := {y | ∀ i, y i ∈ Set.Icc (-T) T}

theorem flatBox3_measurableSet (T : ℝ) : MeasurableSet (flatBox3 T) := by
  rw [flatBox3, Set.setOf_forall]
  exact MeasurableSet.iInter (fun i => (measurable_pi_apply i) measurableSet_Icc)

/-- `matBox 3 3 T = matToFlat3 ⁻¹' flatBox3 T`. -/
theorem matBox3_flatBox_preimage (T : ℝ) : matBox 3 3 T = matToFlat3 ⁻¹' flatBox3 T := by
  ext Δ
  simp only [matBox, flatBox3, Set.mem_setOf_eq, Set.mem_preimage]
  set e : (Σ _ : Fin 3, Fin 3) ≃ Fin (3 * 3) :=
    (Equiv.sigmaEquivProd (Fin 3) (Fin 3)).trans finProdFinEquiv with he
  have hcoord : ∀ i : Fin (3 * 3), (matToFlat3 Δ) i = Δ (e.symm i).1 (e.symm i).2 := fun i => rfl
  constructor
  · intro h i; rw [hcoord i]; exact h (e.symm i).1 (e.symm i).2
  · intro h k j
    have := h (e ⟨k, j⟩)
    rw [hcoord (e ⟨k, j⟩), Equiv.symm_apply_apply] at this
    exact this

/-- The flat-`Δ` cover integrand: `gFlat3 c' T y = ∫_{S∈box 3 4} frobSq(rmatMul (matToFlat3.symm y) S)^{−c'}`. -/
noncomputable def gFlat3 (c' : ℝ) (T : ℝ) (y : Fin (3 * 3) → ℝ) : ℝ≥0∞ :=
  ∫⁻ S in matBox 3 4 T,
    ENNReal.ofReal ((frobSq (rmatMul (matToFlat3.symm y) S)) ^ (-c'))

/-- The `Δ`-outer integral reindexes to the flat `gFlat3` integral over `flatBox3`. -/
theorem matBox3_outer_flat (c' : ℝ) (T : ℝ) :
    (∫⁻ Δ in matBox 3 3 T, ∫⁻ S in matBox 3 4 T,
        ENNReal.ofReal ((frobSq (rmatMul Δ S)) ^ (-c')))
      = ∫⁻ y in flatBox3 T, gFlat3 c' T y := by
  have hmp := measurePreserving_matToFlat3
  have hcomp := hmp.setLIntegral_comp_preimage_emb matToFlat3.measurableEmbedding
    (gFlat3 c' T) (flatBox3 T)
  rw [matBox3_flatBox_preimage, ← hcomp]
  refine setLIntegral_congr_fun (matToFlat3.measurable (flatBox3_measurableSet T)) (fun Δ _ => ?_)
  rw [gFlat3, MeasurableEquiv.symm_apply_apply]

/-- The cover-to-sum on the `Fin 9` flat carrier (`recStep`, the 9-entry argmax cover). -/
theorem gFlat3_cover_sum (c' : ℝ) (T : ℝ) :
    (∫⁻ y in flatBox3 T, gFlat3 c' T y)
      = ∑ p ∈ (Finset.univ : Finset (Fin (3 * 3))),
          ∫⁻ y in chartDomOn (Finset.univ : Finset (Fin (3 * 3))) p \ pivotZeroOn p,
            ENNReal.ofReal |(pivotBlowupOnDeriv (Finset.univ : Finset (Fin (3 * 3))) p y).det|
              * (flatBox3 T).indicator (gFlat3 c' T) (pivotBlowupOn
                  (Finset.univ : Finset (Fin (3 * 3))) p y) := by
  exact recStep (Finset.univ : Finset (Fin (3 * 3))) 0 (Finset.mem_univ 0)
    (flatBox3 T) (flatBox3_measurableSet T) (gFlat3 c' T)

/-- The unflattened angular matrix on chart `p`: `Rmat3 p y` is the `3×3` matrix with `R_p = 1`,
`R_k = y_k` (`k ≠ p`). -/
noncomputable def Rmat3 (p : Fin (3 * 3)) (y : Fin (3 * 3) → ℝ) : Fin 3 → Fin 3 → ℝ :=
  matToFlat3.symm (fun i => if i = p then 1 else y i)

/-- **The radial pull-out** (N1 degree-2 homogeneity): `gFlat3 c' T (blowup) = ∫_S ((y p)²·frobSq(Rmat3·S))^{−c'}`. -/
theorem gFlat3_blowup_radial (c' : ℝ) (T : ℝ) (p : Fin (3 * 3)) (y : Fin (3 * 3) → ℝ) :
    gFlat3 c' T (pivotBlowupOn (Finset.univ : Finset (Fin (3 * 3))) p y)
      = ∫⁻ S in matBox 3 4 T,
          ENNReal.ofReal (((y p) ^ 2 * frobSq (rmatMul (Rmat3 p y) S)) ^ (-c')) := by
  unfold gFlat3 Rmat3
  refine lintegral_congr (fun S => ?_)
  congr 1
  have hbl : matToFlat3.symm (pivotBlowupOn (Finset.univ : Finset (Fin (3 * 3))) p y)
      = fun r c => (y p) * (matToFlat3.symm (fun i => if i = p then 1 else y i)) r c := by
    funext r c
    show matToFlat3.symm (pivotBlowupOn (Finset.univ : Finset (Fin (3 * 3))) p y) r c = _
    rw [show pivotBlowupOn (Finset.univ : Finset (Fin (3 * 3))) p y
        = (fun i => (y p) * (if i = p then 1 else y i)) from by
      funext i; unfold pivotBlowupOn
      by_cases hi : i = p
      · subst hi; simp
      · simp [hi]]
    show matToFlat3.symm (fun i => (y p) * (if i = p then 1 else y i)) r c
        = (y p) * matToFlat3.symm (fun i => if i = p then 1 else y i) r c
    rfl
  rw [hbl, radialDelta_loss_factor (y p) (matToFlat3.symm (fun i => if i = p then 1 else y i)) S]

/-! ## Per-chart support (threshold-agnostic; mirror of corank-2) -/

/-- On the chart, the blown-up point lands in `flatBox3 T` IFF `|y p| ≤ T`. -/
theorem flatBox3_blowup_mem_iff (T : ℝ) (p : Fin (3 * 3)) (y : Fin (3 * 3) → ℝ)
    (hy : y ∈ chartDomOn (Finset.univ : Finset (Fin (3 * 3))) p) :
    pivotBlowupOn (Finset.univ : Finset (Fin (3 * 3))) p y ∈ flatBox3 T ↔ |y p| ≤ T := by
  unfold flatBox3 chartDomOn at *
  simp only [Set.mem_setOf_eq] at *
  constructor
  · intro h
    have hpp := h p
    rw [pivotBlowupOn] at hpp
    simp only [if_pos rfl, Set.mem_Icc] at hpp
    rw [abs_le]; exact hpp
  · intro hp i
    rw [pivotBlowupOn]
    by_cases hi : i = p
    · subst hi; simp only [if_pos rfl, Set.mem_Icc]; rw [abs_le] at hp; exact hp
    · simp only [if_neg hi, Finset.mem_univ, if_true, Set.mem_Icc]
      have hyi : |y i| ≤ 1 := hy i (Finset.mem_univ i) hi
      have hb : |y p * y i| ≤ |y p| := by
        rw [abs_mul]; nlinarith [abs_nonneg (y p), abs_nonneg (y i), abs_nonneg (y p * y i)]
      have hbb : |y p * y i| ≤ T := le_trans hb hp
      rw [abs_le] at hbb; exact hbb

/-! ## The JOINT residual-domination (the genuinely-new corank-3 piece)

After the N2b j=1 split + the shifted-exponent peel, the corank-2 residual `∫_Δ∫_S frobSq(Sc·S)^{−c''}`
with `Sc = Δ_{M22} − Sh` (`Δ_{M22}` the free `2×2` block, `Sh` the fixed Schur shift). The `Δ_{M22} ↦ Sc`
translation (Jac ≡ 1, the matrix-space addition is measure-preserving) box-enlarges `Δ_{M22}` to radius
`T + B` (`B` = the shift bound), and `core_schur2_lt_top` at radius `T + B` closes it. The controller's
decomposition: the matrix-translate is the `Fin 2 → Fin 2 → ℝ` analog of `lintegral_translate_le_local`. -/

/-- **Matrix-box translate-enlarge** (the `Fin 2 → Fin 2 → ℝ` analog of `lintegral_translate_le_local`):
`∫_{Δ∈matBox 2 2 T} f(Δ + Sh) ≤ ∫_{Δ'∈matBox 2 2 Tg} f Δ'` when `(·+Sh)''(matBox 2 2 T) ⊆ matBox 2 2 Tg`.
Measure-preserving matrix-space translation (`measurePreserving_add_right`) + `lintegral_mono_set`. -/
theorem matBox2_translate_le (Sh : Fin 2 → Fin 2 → ℝ) (T Tg : ℝ)
    (f : (Fin 2 → Fin 2 → ℝ) → ℝ≥0∞)
    (hsub : (fun Δ => Δ + Sh) '' (matBox 2 2 T) ⊆ matBox 2 2 Tg) :
    (∫⁻ Δ in matBox 2 2 T, f (Δ + Sh)) ≤ ∫⁻ Δ' in matBox 2 2 Tg, f Δ' := by
  set τ : (Fin 2 → Fin 2 → ℝ) → (Fin 2 → Fin 2 → ℝ) := fun Δ => Δ + Sh with hτ
  have hmp : MeasurePreserving τ volume volume := measurePreserving_add_right volume Sh
  have hemb : MeasurableEmbedding τ := (Homeomorph.addRight Sh).measurableEmbedding
  have h1 : (∫⁻ Δ in matBox 2 2 T, f (τ Δ)) = ∫⁻ Δ' in τ '' (matBox 2 2 T), f Δ' := by
    rw [← hmp.setLIntegral_comp_preimage_emb hemb f (τ '' (matBox 2 2 T)),
      Set.preimage_image_eq (matBox 2 2 T) hemb.injective]
  calc (∫⁻ Δ in matBox 2 2 T, f (Δ + Sh)) = ∫⁻ Δ' in τ '' (matBox 2 2 T), f Δ' := h1
    _ ≤ ∫⁻ Δ' in matBox 2 2 Tg, f Δ' := lintegral_mono_set hsub

/-- **The JOINT residual-domination.** For a fixed shift `Sh` with `|Sh i j| ≤ B`, the shifted corank-2
core integral `∫_{Δ∈matBox 2 2 T}∫_{S∈matBox 2 4 T} frobSq((Δ − Sh)·S)^{−c''}` is finite for `0 < c'' < 2`:
the `Δ ↦ Δ − Sh` translation box-enlarges `Δ` to radius `T + B` (Jac ≡ 1), then `core_schur2_lt_top` at
radius `T + B`. The R-integrated residual the corank-3 recursion produces (Sc varies, not fixed). -/
theorem schurResid2_translate_lt_top (Sh : Fin 2 → Fin 2 → ℝ) (B : ℝ) (hB : ∀ i j, |Sh i j| ≤ B)
    (c'' : ℝ) (hc0 : 0 < c'') (hc2 : c'' < 2) (T : ℝ) (hT : 0 < T) :
    (∫⁻ Δ in matBox 2 2 T, ∫⁻ S in matBox 2 4 T,
        ENNReal.ofReal ((frobSq (rmatMul (fun i j => Δ i j - Sh i j) S)) ^ (-c''))) < ⊤ := by
  -- bound S over the ENLARGED box T+B (S-monotone, T ≤ T+B), then translate Δ ↦ Δ − Sh into radius T+B,
  -- then core_schur2 at T+B (both Δ and S over T+B).
  have hB0 : 0 ≤ B := le_trans (abs_nonneg _) (hB 0 0)
  set g : (Fin 2 → Fin 2 → ℝ) → ℝ≥0∞ := fun Δ =>
    ∫⁻ S in matBox 2 4 (T + B), ENNReal.ofReal ((frobSq (rmatMul Δ S)) ^ (-c'')) with hg
  -- Step 1: S-monotone enlarge + translate-recognition: residual integrand ≤ g (Δ + (−Sh))
  have hSsub : matBox 2 4 T ⊆ matBox 2 4 (T + B) := by
    intro X hX i k; have := Set.mem_Icc.1 (hX i k); rw [Set.mem_Icc]
    constructor <;> [linarith [this.1]; linarith [this.2]]
  have hle1 : ∀ Δ : Fin 2 → Fin 2 → ℝ,
      (∫⁻ S in matBox 2 4 T, ENNReal.ofReal ((frobSq (rmatMul (fun i j => Δ i j - Sh i j) S)) ^ (-c'')))
        ≤ g (Δ + (fun i j => -Sh i j)) := by
    intro Δ
    have hmono := lintegral_mono_set (μ := volume) hSsub
      (f := fun S => ENNReal.ofReal ((frobSq (rmatMul (fun i j => Δ i j - Sh i j) S)) ^ (-c'')))
    refine le_trans hmono (le_of_eq ?_)
    show (∫⁻ S in matBox 2 4 (T + B),
        ENNReal.ofReal ((frobSq (rmatMul (fun i j => Δ i j - Sh i j) S)) ^ (-c'')))
      = ∫⁻ S in matBox 2 4 (T + B),
          ENNReal.ofReal ((frobSq (rmatMul (fun i j => Δ i j + -Sh i j) S)) ^ (-c''))
    refine lintegral_congr (fun S => ?_)
    have : (fun i j => Δ i j - Sh i j) = (fun i j => Δ i j + -Sh i j) := by funext i j; ring
    rw [this]
  refine lt_of_le_of_lt (lintegral_mono hle1) ?_
  -- box-enlarge Δ: |Δ i j + (−Sh i j)| ≤ T + B
  have hsub : (fun Δ => Δ + (fun i j => -Sh i j)) '' (matBox 2 2 T) ⊆ matBox 2 2 (T + B) := by
    rintro Δ' ⟨Δ, hΔ, rfl⟩
    intro i j
    show -(T + B) ≤ Δ i j + (-Sh i j) ∧ Δ i j + (-Sh i j) ≤ T + B
    have hΔij := Set.mem_Icc.1 (hΔ i j)
    have hShij := abs_le.1 (hB i j)
    constructor <;> [linarith [hΔij.1, hShij.2]; linarith [hΔij.2, hShij.1]]
  refine lt_of_le_of_lt (matBox2_translate_le (fun i j => -Sh i j) T (T + B) g hsub) ?_
  show (∫⁻ Δ' in matBox 2 2 (T + B), ∫⁻ S in matBox 2 4 (T + B),
      ENNReal.ofReal ((frobSq (rmatMul Δ' S)) ^ (-c''))) < ⊤
  exact core_schur2_lt_top c'' hc0 hc2 (T + B) (by linarith)

/-- The inner angular S-integral on chart `p`: `innerS3 c' T p y = ∫_{S∈box 3 4} frobSq(Rmat3 p y·S)^{−c'}`. -/
noncomputable def innerS3 (c' : ℝ) (T : ℝ) (p : Fin (3 * 3)) (y : Fin (3 * 3) → ℝ) : ℝ≥0∞ :=
  ∫⁻ S in matBox 3 4 T, ENNReal.ofReal ((frobSq (rmatMul (Rmat3 p y) S)) ^ (-c'))

/-- The chart integrand factors as `radInd(y p) · innerS3` (`|y p|³ → |y p|^{8−2c'}` via the radial peel,
`y p ≠ 0` from `\ pivotZeroOn`). Mirror of `chart_integrand_factor2` (Jacobian `|y p|⁸`, card 9). -/
theorem chart_integrand_factor3 (c' : ℝ) (hc0 : 0 < c') (T : ℝ) (hT : 0 < T)
    (p : Fin (3 * 3)) (y : Fin (3 * 3) → ℝ) (hyp0 : y p ≠ 0)
    (hy : y ∈ chartDomOn (Finset.univ : Finset (Fin (3 * 3))) p) :
    ENNReal.ofReal (|y p| ^ 8)
        * (flatBox3 T).indicator (gFlat3 c' T) (pivotBlowupOn
            (Finset.univ : Finset (Fin (3 * 3))) p y)
      = (Set.Icc (-T) T).indicator
          (fun a => ENNReal.ofReal (|a| ^ ((8 : ℝ) - 2 * c'))) (y p) * innerS3 c' T p y := by
  by_cases hmem : pivotBlowupOn (Finset.univ : Finset (Fin (3 * 3))) p y ∈ flatBox3 T
  · have hyp : |y p| ≤ T := (flatBox3_blowup_mem_iff T p y hy).1 hmem
    rw [Set.indicator_of_mem hmem,
      Set.indicator_of_mem (s := Set.Icc (-T) T) (by rw [Set.mem_Icc, ← abs_le]; exact hyp)]
    rw [gFlat3_blowup_radial c' T p y, innerS3]
    have hpull : ∀ S : Fin 3 → Fin 4 → ℝ,
        ENNReal.ofReal (((y p) ^ 2 * frobSq (rmatMul (Rmat3 p y) S)) ^ (-c'))
          = ENNReal.ofReal ((((y p) ^ 2) ^ (-c')))
            * ENNReal.ofReal ((frobSq (rmatMul (Rmat3 p y) S)) ^ (-c')) := by
      intro S
      rw [← ENNReal.ofReal_mul (Real.rpow_nonneg (by positivity) _),
        ← Real.mul_rpow (by positivity) (frobSq_nonneg _)]
    rw [lintegral_congr hpull, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← mul_assoc]
    congr 1
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    have hb : ((y p) ^ 2 : ℝ) = |y p| ^ (2 : ℝ) := by
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, sq_abs]
    have hpos : (0 : ℝ) < |y p| := abs_pos.2 hyp0
    rw [hb, ← Real.rpow_natCast (|y p|) 8, ← Real.rpow_mul (le_of_lt hpos), ← Real.rpow_add hpos]
    congr 1; push_cast; ring
  · have hyp : ¬ |y p| ≤ T := fun h => hmem ((flatBox3_blowup_mem_iff T p y hy).2 h)
    rw [Set.indicator_of_notMem hmem,
      Set.indicator_of_notMem (s := Set.Icc (-T) T)
        (by rw [Set.mem_Icc, ← abs_le]; exact hyp), zero_mul, mul_zero]

end DLNFibre.DLN.RLCT
