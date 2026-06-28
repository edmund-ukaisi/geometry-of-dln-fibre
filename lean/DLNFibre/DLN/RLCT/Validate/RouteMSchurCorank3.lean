import DLNFibre.DLN.RLCT.Validate.RouteMSchurDepth2
import DLNFibre.DLN.RLCT.Validate.RadialResidualPower
import DLNFibre.DLN.RLCT.Validate.RouteM334Ratiofin
import DLNFibre.Core.MeasureTheory.PolynomialZeroSet

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

/-! ## The UNIFORM `_le` form of the JOINT residual (the boundary-integrable bound)

`schurResid2_translate_lt_top` is only `< ⊤` — pointwise finiteness in the shift `Sh` does not integrate
over the boundary-ratio box (Codex risk #1). The corank-3 chart assembly integrates the residual over the
boundary ratios `Sh(z)` (a finite box), so it needs a bound INDEPENDENT of `Sh`: bound the shifted residual
by the named value `coreSchur2Val c'' (T+B)` (the unshifted corank-2 core integral at the enlarged radius
`T+B`, finite by the depth-2 `core_schur2_lt_top`). Mirror of the corank-2 `schurInner_S_bound` vs `_le`. -/

/-- **The unshifted corank-2 core value** `coreSchur2Val c'' Kr := ∫_{Δ∈matBox 2 2 Kr}∫_{S∈matBox 2 4 Kr}
frobSq(Δ·S)^{−c''}` — the `Sh`-independent finite constant the shifted residual is bounded by. -/
noncomputable def coreSchur2Val (c'' Kr : ℝ) : ℝ≥0∞ :=
  ∫⁻ Δ in matBox 2 2 Kr, ∫⁻ S in matBox 2 4 Kr,
    ENNReal.ofReal ((frobSq (rmatMul Δ S)) ^ (-c''))

/-- `coreSchur2Val c'' Kr < ⊤` for `0 < c'' < 2`, `0 < Kr` (the depth-2 `core_schur2_lt_top`). -/
theorem coreSchur2Val_lt_top (c'' : ℝ) (hc0 : 0 < c'') (hc2 : c'' < 2) (Kr : ℝ) (hKr : 0 < Kr) :
    coreSchur2Val c'' Kr < ⊤ :=
  core_schur2_lt_top c'' hc0 hc2 Kr hKr

/-- **The JOINT residual UNIFORM `_le` bound.** For a fixed shift `Sh` with `|Sh i j| ≤ B`, the shifted
corank-2 core integral is `≤ coreSchur2Val c'' (T+B)` — a bound INDEPENDENT of `Sh` (only the radius
`T+B` records the shift's size). Same chain as `schurResid2_translate_lt_top` (S-monotone enlarge T→T+B,
then translate `Δ ↦ Δ − Sh` into radius `T+B`), ending at the named value rather than `< ⊤`. The
boundary-integrable form the corank-3 chart assembly consumes. -/
theorem schurResid2_translate_le (Sh : Fin 2 → Fin 2 → ℝ) (B : ℝ) (hB : ∀ i j, |Sh i j| ≤ B)
    (c'' : ℝ) (T : ℝ) :
    (∫⁻ Δ in matBox 2 2 T, ∫⁻ S in matBox 2 4 T,
        ENNReal.ofReal ((frobSq (rmatMul (fun i j => Δ i j - Sh i j) S)) ^ (-c'')))
      ≤ coreSchur2Val c'' (T + B) := by
  have hB0 : 0 ≤ B := le_trans (abs_nonneg _) (hB 0 0)
  set g : (Fin 2 → Fin 2 → ℝ) → ℝ≥0∞ := fun Δ =>
    ∫⁻ S in matBox 2 4 (T + B), ENNReal.ofReal ((frobSq (rmatMul Δ S)) ^ (-c'')) with hg
  -- Step 1: S-monotone enlarge T → T+B + translate-recognition: residual integrand ≤ g (Δ + (−Sh))
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
  refine le_trans (lintegral_mono hle1) ?_
  -- box-enlarge Δ: |Δ i j + (−Sh i j)| ≤ T + B
  have hsub : (fun Δ => Δ + (fun i j => -Sh i j)) '' (matBox 2 2 T) ⊆ matBox 2 2 (T + B) := by
    rintro Δ' ⟨Δ, hΔ, rfl⟩
    intro i j
    show -(T + B) ≤ Δ i j + (-Sh i j) ∧ Δ i j + (-Sh i j) ≤ T + B
    have hΔij := Set.mem_Icc.1 (hΔ i j)
    have hShij := abs_le.1 (hB i j)
    constructor <;> [linarith [hΔij.1, hShij.2]; linarith [hΔij.2, hShij.1]]
  refine le_trans (matBox2_translate_le (fun i j => -Sh i j) T (T + B) g hsub) (le_of_eq ?_)
  rw [coreSchur2Val]

/-! ## The local a.e.-positivity of the corank-2 residual core (`frobSq (Δ·S) > 0` a.e.)

The shifted Morse peel (`radial_morse_residual_power_le`) needs `w = frobSq (Sc·S_bot) > 0`. For a FIXED
shift `Sh`, the shifted core `frobSq ((Δ − Sh)·S)` is `> 0` a.e. by translation `Δ ↦ Δ + Sh` (MP) from the
UNSHIFTED `frobSq (Δ·S) > 0` a.e. The unshifted positivity is the polynomial-nonvanishing argument: the
core is a nonzero `MvPolynomial (Fin 12) ℝ` in the flattened `(Δ,S)` coords, so its zero set is null
(`MvPolynomial.ae_eval_ne_zero`). Local copy of `RouteM334Hfin`'s machinery (renamed `…R2c3` to avoid the
full-aggregator name clash), avoiding that file's heavy import (it carries an unrelated `sorry`). -/

open MvPolynomial in
/-- The corank-2 residual core as an `MvPolynomial (Fin 12) ℝ` (Δ at coords `0..3`, S at `4..11`). -/
noncomputable def corePolyR2c3 : MvPolynomial (Fin 12) ℝ :=
  ∑ i : Fin 2, ∑ j : Fin 4,
    (∑ k : Fin 2,
      (!![X 0, X 1; X 2, X 3] : Matrix (Fin 2) (Fin 2) (MvPolynomial (Fin 12) ℝ)) i k
        * (!![X 4, X 5, X 6, X 7; X 8, X 9, X 10, X 11]
          : Matrix (Fin 2) (Fin 4) (MvPolynomial (Fin 12) ℝ)) k j) ^ 2

open MvPolynomial in
/-- `corePolyR2c3 ≠ 0` (witness `Δ = I₂`, `S = !![1,0,0,0;0,0,0,0]` gives core `= 1`). -/
theorem corePolyR2c3_ne_zero : corePolyR2c3 ≠ 0 := by
  intro h0
  set w : Fin 12 → ℝ := Pi.single 0 1 + Pi.single 3 1 + Pi.single 4 1 with hw
  have hval : MvPolynomial.eval w corePolyR2c3 = 1 := by
    rw [corePolyR2c3]
    simp only [map_sum, map_pow, map_mul, Fin.sum_univ_two, Fin.sum_univ_four,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.of_apply,
      Matrix.cons_val, Matrix.head_fin_const, Matrix.cons_val', MvPolynomial.eval_X]
    simp only [hw, Pi.add_apply, Pi.single_apply]
    norm_num [Fin.ext_iff]
  rw [h0] at hval; simp at hval

/-- The flatten `(Fin 2 → Fin 2 → ℝ) × (Fin 2 → Fin 4 → ℝ) → (Fin 12 → ℝ)` (Δ → `0..3`, S → `4..11`). -/
noncomputable def flatR2c3 (p : (Fin 2 → Fin 2 → ℝ) × (Fin 2 → Fin 4 → ℝ)) : Fin 12 → ℝ :=
  fun k => if h : (k : ℕ) < 4 then p.1 ⟨(k : ℕ) / 2, by omega⟩ ⟨(k : ℕ) % 2, by omega⟩
    else p.2 ⟨((k : ℕ) - 4) / 4, by omega⟩ ⟨((k : ℕ) - 4) % 4, by omega⟩

/-- A matrix-space flatten `(Fin r → Fin n → ℝ) ≃ᵐ (Fin (r * n) → ℝ)` (local copy). -/
noncomputable def matToFlatEquivc3 (r n : ℕ) : (Fin r → Fin n → ℝ) ≃ᵐ (Fin (r * n) → ℝ) :=
  (MeasurableEquiv.piCurry (fun (_ : Fin r) (_ : Fin n) => ℝ)).symm.trans
    (MeasurableEquiv.arrowCongr'
      ((Equiv.sigmaEquivProd (Fin r) (Fin n)).trans finProdFinEquiv) (MeasurableEquiv.refl ℝ))

theorem measurePreserving_matToFlatEquivc3 (r n : ℕ) :
    MeasurePreserving (matToFlatEquivc3 r n)
      (volume : Measure (Fin r → Fin n → ℝ)) (volume : Measure (Fin (r * n) → ℝ)) := by
  unfold matToFlatEquivc3
  refine MeasurePreserving.trans ?_ (volume_preserving_arrowCongr'
    ((Equiv.sigmaEquivProd (Fin r) (Fin n)).trans finProdFinEquiv)
    (MeasurableEquiv.refl ℝ) (MeasurePreserving.id _))
  exact (measurePreserving_piCurry (fun (_ : Fin r) (_ : Fin n) => ℝ)
    (fun _ _ => (volume : Measure ℝ))).symm
    (MeasurableEquiv.piCurry (fun (_ : Fin r) (_ : Fin n) => ℝ))

/-- The combine `(Fin 4 → ℝ) × (Fin 8 → ℝ) ≃ᵐ (Fin 12 → ℝ)` (local copy). -/
noncomputable def combine48c3 : ((Fin 4 → ℝ) × (Fin 8 → ℝ)) ≃ᵐ (Fin 12 → ℝ) :=
  (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin 4 ⊕ Fin 8 => ℝ)).symm.trans
    ((MeasurableEquiv.piCongrLeft (fun _ : Fin 12 => ℝ)
      (finSumFinEquiv : Fin 4 ⊕ Fin 8 ≃ Fin 12)))

theorem measurePreserving_combine48c3 :
    MeasurePreserving combine48c3
      (volume : Measure ((Fin 4 → ℝ) × (Fin 8 → ℝ))) (volume : Measure (Fin 12 → ℝ)) := by
  unfold combine48c3
  have hsum : MeasurePreserving
      (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin 4 ⊕ Fin 8 => ℝ)).symm
      (volume : Measure ((Fin 4 → ℝ) × (Fin 8 → ℝ)))
      (volume : Measure (Fin 4 ⊕ Fin 8 → ℝ)) :=
    volume_measurePreserving_sumPiEquivProdPi_symm (fun _ : Fin 4 ⊕ Fin 8 => ℝ)
  have hcongr : MeasurePreserving
      (MeasurableEquiv.piCongrLeft (fun _ : Fin 12 => ℝ)
        (finSumFinEquiv : Fin 4 ⊕ Fin 8 ≃ Fin 12))
      (volume : Measure (Fin 4 ⊕ Fin 8 → ℝ)) (volume : Measure (Fin 12 → ℝ)) :=
    volume_measurePreserving_piCongrLeft (fun _ : Fin 12 => ℝ)
      (finSumFinEquiv : Fin 4 ⊕ Fin 8 ≃ Fin 12)
  exact hsum.trans hcongr

theorem measurePreserving_flatR2c3 :
    MeasurePreserving flatR2c3
      (volume : Measure ((Fin 2 → Fin 2 → ℝ) × (Fin 2 → Fin 4 → ℝ)))
      (volume : Measure (Fin 12 → ℝ)) := by
  have hcomp : MeasurePreserving
      (combine48c3 ∘ (Prod.map (matToFlatEquivc3 2 2) (matToFlatEquivc3 2 4)))
      (volume : Measure ((Fin 2 → Fin 2 → ℝ) × (Fin 2 → Fin 4 → ℝ)))
      (volume : Measure (Fin 12 → ℝ)) := by
    refine MeasurePreserving.comp measurePreserving_combine48c3 ?_
    have hpp := (measurePreserving_matToFlatEquivc3 2 2).prod (measurePreserving_matToFlatEquivc3 2 4)
    rw [show (volume : Measure ((Fin 4 → ℝ) × (Fin 8 → ℝ))) = volume.prod volume from rfl]
    rw [show (volume : Measure ((Fin 2 → Fin 2 → ℝ) × (Fin 2 → Fin 4 → ℝ))) = volume.prod volume
      from rfl]
    exact hpp
  have heq : flatR2c3 = combine48c3 ∘ (Prod.map (matToFlatEquivc3 2 2) (matToFlatEquivc3 2 4)) := by
    funext p k
    fin_cases k <;> rfl
  rw [heq]; exact hcomp

theorem eval_corePolyR2c3_flatR2c3 (p : (Fin 2 → Fin 2 → ℝ) × (Fin 2 → Fin 4 → ℝ)) :
    MvPolynomial.eval (flatR2c3 p) corePolyR2c3 = frobSq (rmatMul p.1 p.2) := by
  have h0 : flatR2c3 p 0 = p.1 0 0 := rfl
  have h1 : flatR2c3 p 1 = p.1 0 1 := rfl
  have h2 : flatR2c3 p 2 = p.1 1 0 := rfl
  have h3 : flatR2c3 p 3 = p.1 1 1 := rfl
  have h4 : flatR2c3 p 4 = p.2 0 0 := rfl
  have h5 : flatR2c3 p 5 = p.2 0 1 := rfl
  have h6 : flatR2c3 p 6 = p.2 0 2 := rfl
  have h7 : flatR2c3 p 7 = p.2 0 3 := rfl
  have h8 : flatR2c3 p 8 = p.2 1 0 := rfl
  have h9 : flatR2c3 p 9 = p.2 1 1 := rfl
  have h10 : flatR2c3 p 10 = p.2 1 2 := rfl
  have h11 : flatR2c3 p 11 = p.2 1 3 := rfl
  rw [corePolyR2c3]
  unfold frobSq rmatMul
  simp only [Fin.sum_univ_two, Fin.sum_univ_four,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.of_apply,
    Matrix.cons_val, Matrix.head_fin_const, Matrix.cons_val',
    map_sum, map_add, map_mul, map_pow, map_ofNat, MvPolynomial.eval_X,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]

/-- **The corank-2 residual core is positive a.e.** `∀ᵐ (Δ,S), 0 < frobSq (Δ·S)` (local copy of
`RouteM334Hfin.frobSq_core334_ne_zero_ae`, renamed). -/
theorem frobSqR2c3_ne_zero_ae :
    ∀ᵐ p : (Fin 2 → Fin 2 → ℝ) × (Fin 2 → Fin 4 → ℝ) ∂(volume),
      0 < frobSq (rmatMul p.1 p.2) := by
  have hae : ∀ᵐ x : Fin 12 → ℝ, MvPolynomial.eval x corePolyR2c3 ≠ 0 :=
    MvPolynomial.ae_eval_ne_zero corePolyR2c3 corePolyR2c3_ne_zero
  have hmeasSet : MeasurableSet {x : Fin 12 → ℝ | MvPolynomial.eval x corePolyR2c3 ≠ 0} :=
    (MvPolynomial.measurableSet_zeroSet corePolyR2c3).compl.congr (by ext x; simp)
  have hpull : ∀ᵐ p : (Fin 2 → Fin 2 → ℝ) × (Fin 2 → Fin 4 → ℝ) ∂(volume),
      MvPolynomial.eval (flatR2c3 p) corePolyR2c3 ≠ 0 := by
    rw [← measurePreserving_flatR2c3.map_eq] at hae
    exact (ae_map_iff measurePreserving_flatR2c3.measurable.aemeasurable hmeasSet).1 hae
  refine hpull.mono (fun p hp => ?_)
  rw [eval_corePolyR2c3_flatR2c3] at hp
  exact lt_of_le_of_ne (frobSq_nonneg _) (Ne.symm hp)

/-! ## The local Tonelli `T`-peel bound (a.e. variant; local copy of `core_T_peel_le_ae`) -/

/-- **The a.e. Tonelli `T`-peel bound** (local copy of `RouteM334Hfin.core_T_peel_le_ae`, built on the
imported `radial_morse_residual_power_le`). With `w > 0` only a.e. on `Z`, the joint Morse-block peel
`∫_z ∫_T (∑Tᵢ² + w z)^{−c'} ≤ Cresid·∫_z (w z)^{−(c'−(m+1)/2)}`. -/
theorem core_T_peel_le_ae_c3 {m : ℕ} {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (c' : ℝ) (hc' : (m + 1 : ℝ) / 2 < c')
    (Tw : ℝ) (hTw : 0 < Tw) (w : Ω → ℝ) (Z : Set Ω)
    (hwpos : ∀ᵐ z ∂(μ.restrict Z), 0 < w z) :
    (∫⁻ z in Z, (∫⁻ T in morseBox (m + 1) Tw,
        ENNReal.ofReal ((∑ i, (T i) ^ 2 + w z) ^ (-c'))) ∂μ)
      ≤ ENNReal.ofReal (Cresid (m + 1) c')
        * ∫⁻ z in Z, ENNReal.ofReal ((w z) ^ (-(c' - (m + 1 : ℝ) / 2))) ∂μ := by
  calc (∫⁻ z in Z, (∫⁻ T in morseBox (m + 1) Tw,
          ENNReal.ofReal ((∑ i, (T i) ^ 2 + w z) ^ (-c'))) ∂μ)
      ≤ ∫⁻ z in Z, ENNReal.ofReal (Cresid (m + 1) c')
          * ENNReal.ofReal ((w z) ^ (-(c' - (m + 1 : ℝ) / 2))) ∂μ := by
        refine lintegral_mono_ae (hwpos.mono (fun z hz => ?_))
        rw [← ENNReal.ofReal_mul (Cresid_nonneg _ _)]
        exact radial_morse_residual_power_le m c' hc' Tw hTw (w z) hz
    _ = ENNReal.ofReal (Cresid (m + 1) c')
          * ∫⁻ z in Z, ENNReal.ofReal ((w z) ^ (-(c' - (m + 1 : ℝ) / 2))) ∂μ := by
        rw [lintegral_const_mul']
        exact ENNReal.ofReal_ne_top

/-! ## The SHIFTED resolved-form (the JOINT brick: peel + shifted residual, uniform `_le`)

The corank-3 inner-S, after the N2b `j=1` split and the row-0 shear, is the SHIFTED analog of
`RouteM334Hfin.resolved334_box_lt_top`: a `4`-dim Morse spectator `T` (the shear of `S_row0`) disjoint-
summed onto the SHIFTED corank-2 core `frobSq ((Δ − Sh)·S)` (`Δ = M22` the free angular sub-block,
`Sh = M21·M12` the boundary-ratio shift, `S = S_bot`). The peel (`core_T_peel_le_ae_c3`, threshold
`4/2 = 2 < c'`) leaves the shifted residual at exponent `c'' = c'−2 < 2`, bounded UNIFORMLY in `Sh` by
`coreSchur2Val (c'−2) (K+B)` (`schurResid2_translate_le`). The `Sh`-uniform bound the chart's boundary
integration consumes. -/

/-! ## The per-chart angular helpers (mirror of the corank-2 `Rmat2_*` / `innerS2_*`) -/

/-- The matrix↔flat index equiv `e3c3 : Fin 3 × Fin 3 ≃ Fin 9`, matching `matToFlat3`'s index reindex. -/
noncomputable def e3c3 : Fin 3 × Fin 3 ≃ Fin (3 * 3) :=
  ((Equiv.sigmaEquivProd (Fin 3) (Fin 3)).symm).trans
    ((Equiv.sigmaEquivProd (Fin 3) (Fin 3)).trans finProdFinEquiv)

/-- `Rmat3 p y i j = if e3c3 (i,j) = p then 1 else y (e3c3 (i,j))` (the unflattened angular matrix). -/
theorem Rmat3_entry (p : Fin (3 * 3)) (y : Fin (3 * 3) → ℝ) (i j : Fin 3) :
    Rmat3 p y i j = if e3c3 (i, j) = p then 1 else y (e3c3 (i, j)) := rfl

/-- The pivot entry of `Rmat3 p y` is `1` (at the matrix index `e3c3.symm p`). -/
theorem Rmat3_pivot (p : Fin (3 * 3)) (y : Fin (3 * 3) → ℝ) :
    Rmat3 p y (e3c3.symm p).1 (e3c3.symm p).2 = 1 := by
  rw [Rmat3_entry, if_pos]
  rw [show ((e3c3.symm p).1, (e3c3.symm p).2) = e3c3.symm p from rfl, Equiv.apply_symm_apply]

/-- `|Rmat3 p y i j| ≤ 1` on the ratio chart `|y_k| ≤ 1` (`k ≠ p`); pivot entry `= 1`. -/
theorem Rmat3_entry_le (p : Fin (3 * 3)) (y : Fin (3 * 3) → ℝ)
    (hy : ∀ k, k ≠ p → |y k| ≤ 1) (i j : Fin 3) : |Rmat3 p y i j| ≤ 1 := by
  rw [Rmat3_entry]
  by_cases h : e3c3 (i, j) = p
  · rw [if_pos h]; norm_num
  · rw [if_neg h]; exact hy _ h

/-- `innerS3` is `y p`-invariant: `Rmat3 p y` reads `y i` only for `i ≠ p`. -/
theorem innerS3_offpivot (c' : ℝ) (T : ℝ) (p : Fin (3 * 3)) (y y' : Fin (3 * 3) → ℝ)
    (h : ∀ i, i ≠ p → y i = y' i) : innerS3 c' T p y = innerS3 c' T p y' := by
  have hR : Rmat3 p y = Rmat3 p y' := by
    funext i j; rw [Rmat3_entry, Rmat3_entry]
    by_cases hij : e3c3 (i, j) = p
    · rw [if_pos hij, if_pos hij]
    · rw [if_neg hij, if_neg hij]; exact h _ hij
  rw [innerS3, innerS3, hR]

/-- `innerS3 c' T p` is measurable in `y`. -/
theorem measurable_innerS3 (c' : ℝ) (T : ℝ) (p : Fin (3 * 3)) : Measurable (innerS3 c' T p) := by
  unfold innerS3
  apply Measurable.lintegral_prod_right (f := fun y S =>
    ENNReal.ofReal ((frobSq (rmatMul (Rmat3 p y) S)) ^ (-c')))
  apply ENNReal.measurable_ofReal.comp
  apply Measurable.comp (g := fun t : ℝ => t ^ (-c')) (by fun_prop)
  unfold frobSq rmatMul
  apply Finset.measurable_sum; intro i _
  apply Finset.measurable_sum; intro j _
  apply Measurable.pow_const
  apply Finset.measurable_sum; intro k _
  apply Measurable.mul
  · have hy : Measurable (fun y : Fin (3 * 3) → ℝ => Rmat3 p y i k) := by
      simp only [Rmat3_entry]
      by_cases h : e3c3 (i, k) = p
      · simp only [if_pos h]; exact measurable_const
      · simp only [if_neg h]; exact measurable_pi_apply _
    exact hy.comp measurable_fst
  · exact (measurable_pi_apply j).comp ((measurable_pi_apply k).comp measurable_snd)

/-- **The shifted core is positive a.e.** `∀ᵐ (Δ,S), 0 < frobSq ((Δ − Sh)·S)` for any fixed `Sh`: the
translation `Δ ↦ Δ + Sh` (MP) reduces it to the unshifted `frobSqR2c3_ne_zero_ae`. -/
theorem frobSqShiftR2c3_ne_zero_ae (Sh : Fin 2 → Fin 2 → ℝ) :
    ∀ᵐ p : (Fin 2 → Fin 2 → ℝ) × (Fin 2 → Fin 4 → ℝ) ∂(volume),
      0 < frobSq (rmatMul (fun i j => p.1 i j - Sh i j) p.2) := by
  -- translation τ (Δ,S) = (Δ − Sh, S) is MP; pull back the unshifted a.e.-positivity along τ
  set τ : (Fin 2 → Fin 2 → ℝ) × (Fin 2 → Fin 4 → ℝ) → (Fin 2 → Fin 2 → ℝ) × (Fin 2 → Fin 4 → ℝ) :=
    fun p => (p.1 + (fun i j => -Sh i j), p.2) with hτ
  have hmpΔ : MeasurePreserving (fun Δ : Fin 2 → Fin 2 → ℝ => Δ + (fun i j => -Sh i j))
      volume volume :=
    measurePreserving_add_right volume (fun i j => -Sh i j)
  have hmp : MeasurePreserving τ volume volume := by
    rw [show (volume : Measure ((Fin 2 → Fin 2 → ℝ) × (Fin 2 → Fin 4 → ℝ))) = volume.prod volume
      from rfl]
    exact hmpΔ.prod (MeasurePreserving.id volume)
  have hmsSet : MeasurableSet {q : (Fin 2 → Fin 2 → ℝ) × (Fin 2 → Fin 4 → ℝ) |
      0 < frobSq (rmatMul q.1 q.2)} :=
    measurableSet_lt measurable_const (by unfold frobSq rmatMul; fun_prop)
  have hae : ∀ᵐ x ∂(volume.map τ), 0 < frobSq (rmatMul x.1 x.2) := by
    rw [hmp.map_eq]; exact frobSqR2c3_ne_zero_ae
  have hpull : ∀ᵐ p ∂(volume : Measure ((Fin 2 → Fin 2 → ℝ) × (Fin 2 → Fin 4 → ℝ))),
      0 < frobSq (rmatMul (τ p).1 (τ p).2) :=
    (ae_map_iff hmp.measurable.aemeasurable hmsSet).1 hae
  refine hpull.mono (fun p hp => ?_)
  -- `hp : 0 < frobSq (rmatMul (τ p).1 (τ p).2)`; `(τ p).1 = p.1 + (−Sh)`, `(τ p).2 = p.2`
  have hΔeq : (τ p).1 = (fun i j => p.1 i j - Sh i j) := by
    funext i j; show (p.1 + (fun i j => -Sh i j)) i j = p.1 i j - Sh i j
    simp [Pi.add_apply, sub_eq_add_neg]
  have hSeq : (τ p).2 = p.2 := rfl
  rw [hΔeq, hSeq] at hp
  exact hp

/-- **The SHIFTED resolved-form UNIFORM `_le` bound (the JOINT brick).** For a fixed shift `Sh` with
`|Sh i j| ≤ B`, `2 < c' < 4`, every `K > 0`,
`∫_{Δ∈matBox 2 2 K}∫_{S∈matBox 2 4 K}∫_{T∈morseBox 4 K}(∑T² + frobSq((Δ−Sh)·S))^{−c'}` is bounded by
`ofReal(Cresid 4 c') · coreSchur2Val (c'−2) (K+B)` — INDEPENDENT of `Sh` (only the radius `K+B` records the
shift). The T-peel (`core_T_peel_le_ae_c3`, m=3, threshold 2) on the shifted core (`> 0` a.e. by
`frobSqShiftR2c3_ne_zero_ae`) leaves the residual at `c'−2 < 2`, closed by `schurResid2_translate_le`.
Mirror of `RouteM334Hfin.resolved334_box_lt_top`, shifted + uniform. -/
theorem resolvedShiftR2c3_le (Sh : Fin 2 → Fin 2 → ℝ) (B : ℝ) (hB : ∀ i j, |Sh i j| ≤ B)
    (K : ℝ) (hK : 0 < K) (c' : ℝ) (hc2 : 2 < c') (hc4 : c' < 4) :
    (∫⁻ Δ in matBox 2 2 K, ∫⁻ S in matBox 2 4 K, ∫⁻ T in morseBox 4 K,
        ENNReal.ofReal ((∑ i, (T i) ^ 2 + frobSq (rmatMul (fun a b => Δ a b - Sh a b) S)) ^ (-c')))
      ≤ ENNReal.ofReal (Cresid 4 c') * coreSchur2Val (c' - 2) (K + B) := by
  set w : (Fin 2 → Fin 2 → ℝ) × (Fin 2 → Fin 4 → ℝ) → ℝ :=
    fun p => frobSq (rmatMul (fun a b => p.1 a b - Sh a b) p.2) with hwdef
  have hmeasT : Measurable (fun q : ((Fin 2 → Fin 2 → ℝ) × (Fin 2 → Fin 4 → ℝ)) × (Fin 4 → ℝ) =>
      ENNReal.ofReal ((∑ i, (q.2 i) ^ 2 + w q.1) ^ (-c'))) := by
    apply ENNReal.measurable_ofReal.comp
    apply Measurable.comp (g := fun t : ℝ => t ^ (-c')) (by fun_prop)
    show Measurable (fun q : ((Fin 2 → Fin 2 → ℝ) × (Fin 2 → Fin 4 → ℝ)) × (Fin 4 → ℝ) =>
        (∑ i, (q.2 i) ^ 2 + frobSq (rmatMul (fun a b => q.1.1 a b - Sh a b) q.1.2)))
    unfold frobSq rmatMul; fun_prop
  -- Step 1: Tonelli ∫_Δ∫_S∫_T = ∫_{(Δ,S)}∫_T over the product box
  have hstep1 : ∫⁻ Δ in matBox 2 2 K, ∫⁻ S in matBox 2 4 K, ∫⁻ T in morseBox 4 K,
        ENNReal.ofReal ((∑ i, (T i) ^ 2 + frobSq (rmatMul (fun a b => Δ a b - Sh a b) S)) ^ (-c'))
      = ∫⁻ p in (matBox 2 2 K ×ˢ matBox 2 4 K), (∫⁻ T in morseBox 4 K,
          ENNReal.ofReal ((∑ i, (T i) ^ 2 + w p) ^ (-c'))) ∂volume := by
    rw [Measure.volume_eq_prod (Fin 2 → Fin 2 → ℝ) (Fin 2 → Fin 4 → ℝ),
      setLIntegral_prod _ (Measurable.lintegral_prod_right hmeasT).aemeasurable]
  rw [hstep1]
  -- Step 2: the a.e. T-peel (m = 3): bound by Cresid · ∫_{(Δ,S)} w^{−(c'−2)}
  have hwpos : ∀ᵐ z ∂(volume.restrict (matBox 2 2 K ×ˢ matBox 2 4 K)), 0 < w z :=
    ae_restrict_of_ae (frobSqShiftR2c3_ne_zero_ae Sh)
  have hpeel := core_T_peel_le_ae_c3 (m := 3) (volume) c' (by norm_num; linarith) K hK w
    (matBox 2 2 K ×ˢ matBox 2 4 K) hwpos
  refine le_trans hpeel ?_
  -- Step 3: the residual ∫_{(Δ,S)} w^{−(c'−2)} = ∫_Δ∫_S frobSq((Δ−Sh)·S)^{−(c'−2)} ≤ schurResid2_translate_le
  refine mul_le_mul_left' ?_ _
  have hmeasResid : Measurable
      (fun p : (Fin 2 → Fin 2 → ℝ) × (Fin 2 → Fin 4 → ℝ) =>
        ENNReal.ofReal ((w p) ^ (-(c' - ((3 : ℕ) + 1 : ℝ) / 2)))) := by
    apply ENNReal.measurable_ofReal.comp
    apply Measurable.comp (g := fun t : ℝ => t ^ (-(c' - ((3 : ℕ) + 1 : ℝ) / 2))) (by fun_prop)
    show Measurable (fun p : (Fin 2 → Fin 2 → ℝ) × (Fin 2 → Fin 4 → ℝ) =>
        frobSq (rmatMul (fun a b => p.1 a b - Sh a b) p.2))
    unfold frobSq rmatMul; fun_prop
  have hresid : (∫⁻ p in (matBox 2 2 K ×ˢ matBox 2 4 K),
        ENNReal.ofReal ((w p) ^ (-(c' - ((3 : ℕ) + 1 : ℝ) / 2))))
      = ∫⁻ Δ in matBox 2 2 K, ∫⁻ S in matBox 2 4 K,
          ENNReal.ofReal ((frobSq (rmatMul (fun a b => Δ a b - Sh a b) S)) ^ (-(c' - 2))) := by
    rw [Measure.volume_eq_prod (Fin 2 → Fin 2 → ℝ) (Fin 2 → Fin 4 → ℝ),
      setLIntegral_prod _ hmeasResid.aemeasurable]
    refine setLIntegral_congr_fun (matBox_measurableSet 2 2 K) (fun Δ _ => ?_)
    refine setLIntegral_congr_fun (matBox_measurableSet 2 4 K) (fun S _ => ?_)
    rw [hwdef]; norm_num
  rw [hresid]
  exact schurResid2_translate_le Sh B hB (c' - 2) K

/-! ## The per-chart finiteness + the 9-chart assembly -/

/-- **The corank-3 per-chart ratio-residual finiteness — the JOINT inner heart (at the unit `S`-box).**
For each `Δ`-entry pivot `p : Fin 9`, `2 < c' < 4`, `∫_{z∈[−1,1]^8} innerS3 c' 1 p (e.symm(0,z)) < ⊤`,
`e = piFinSuccAbove p`. This is EXACTLY the `(3,3,4)` anchor's ratio residual `ratioResidual_lt_top`:
`innerS3 c' 1 p y` and `angA1Int c' p y` are the same object (`Rmat3 = Rmat334`, both `matToFlatEquiv 3 3`,
the `matBox 3 4 1` `S`-box). The `(3,3,4)` JOINT recognition (`ginnerZ_lt_top`: the `zE`/`bgShift`
`M22 ↦ Δ−Sh` slot identification feeding the BANKED `resolved334_box_lt_top`) IS the corank-3 inner heart —
the genuinely-new content is reused verbatim, not re-derived. -/
theorem schurInner3_ratiofin_mid (c' : ℝ) (hc2 : 2 < c') (hc4 : c' < 4)
    (p : Fin (3 * 3)) :
    (∫⁻ z in (Set.univ.pi (fun _ : Fin 8 => Set.Icc (-1 : ℝ) 1)),
        innerS3 c' 1 p ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (3 * 3) => ℝ) p).symm (0, z)))
      < ⊤ :=
  ratioResidual_lt_top c' hc2 hc4 p

/-- **Pointwise rpow domination** `ofReal(x^{−c'}) ≤ 1 + ofReal(x^{−c''})` for `x ≥ 0`, `0 < c' ≤ c''`:
on `x ≥ 1` the LHS `≤ 1`, on `0 < x < 1` the LHS `≤ x^{−c''}` (smaller-magnitude negative exponent), at
`x = 0` both `0^{neg} = 0`. The reduction of the `c' ≤ 2` ratio-residual to the `c'' = 3 ∈ (2,4)` mid case. -/
theorem ofReal_rpow_neg_le_one_add (x : ℝ) (hx : 0 ≤ x) (c' c'' : ℝ) (hc0 : 0 < c') (hcc : c' ≤ c'') :
    ENNReal.ofReal (x ^ (-c')) ≤ 1 + ENNReal.ofReal (x ^ (-c'')) := by
  rcases eq_or_lt_of_le hx with hx0 | hx0
  · -- x = 0: 0^{−c'} = 0 (c' > 0)
    rw [← hx0, Real.zero_rpow (by linarith), ENNReal.ofReal_zero]
    exact zero_le _
  · -- x > 0
    rcases le_or_gt 1 x with h1 | h1
    · -- x ≥ 1: x^{−c'} ≤ 1
      refine le_trans (ENNReal.ofReal_le_ofReal ?_) (le_add_right (le_of_eq ENNReal.ofReal_one))
      calc x ^ (-c') ≤ x ^ (0 : ℝ) := Real.rpow_le_rpow_of_exponent_le h1 (by linarith)
        _ = 1 := Real.rpow_zero x
    · -- 0 < x < 1: x^{−c'} ≤ x^{−c''}
      refine le_trans (ENNReal.ofReal_le_ofReal ?_) (le_add_left (le_refl _))
      exact Real.rpow_le_rpow_of_exponent_ge hx0 (le_of_lt h1) (by linarith)

theorem schurInner3_ratiofin (c' : ℝ) (hc0 : 0 < c') (hc' : c' < 4)
    (p : Fin (3 * 3)) :
    (∫⁻ z in (Set.univ.pi (fun _ : Fin 8 => Set.Icc (-1 : ℝ) 1)),
        innerS3 c' 1 p ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (3 * 3) => ℝ) p).symm (0, z)))
      < ⊤ := by
  rcases lt_or_ge 2 c' with hc2 | hc2
  · exact schurInner3_ratiofin_mid c' hc2 hc' p
  · -- c' ≤ 2: dominate the integrand by `1 + (·)^{−3}`, reducing to the c'' = 3 ∈ (2,4) mid case
    set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (3 * 3) => ℝ) p with he
    -- per z: innerS3 c' (e.symm(0,z)) ≤ vol(matBox 3 4 1) + innerS3 3 (e.symm(0,z))
    have hdom : ∀ z : Fin 8 → ℝ,
        innerS3 c' 1 p (e.symm (0, z))
          ≤ volume (matBox 3 4 1) + innerS3 3 1 p (e.symm (0, z)) := by
      intro z
      rw [innerS3, innerS3]
      calc (∫⁻ S in matBox 3 4 1,
              ENNReal.ofReal ((frobSq (rmatMul (Rmat3 p (e.symm (0, z))) S)) ^ (-c')))
          ≤ ∫⁻ S in matBox 3 4 1,
              (1 + ENNReal.ofReal ((frobSq (rmatMul (Rmat3 p (e.symm (0, z))) S)) ^ (-(3 : ℝ)))) :=
            lintegral_mono (fun S =>
              ofReal_rpow_neg_le_one_add _ (frobSq_nonneg _) c' 3 hc0 (by linarith))
        _ = volume (matBox 3 4 1) + ∫⁻ S in matBox 3 4 1,
              ENNReal.ofReal ((frobSq (rmatMul (Rmat3 p (e.symm (0, z))) S)) ^ (-(3 : ℝ))) := by
            rw [lintegral_add_left measurable_const, setLIntegral_const, one_mul]
    refine lt_of_le_of_lt (lintegral_mono hdom) ?_
    rw [lintegral_add_left measurable_const, setLIntegral_const]
    refine ENNReal.add_lt_top.2 ⟨?_, ?_⟩
    · exact ENNReal.mul_lt_top (matBox_volume_lt_top 3 4 1)
        (by rw [show (Set.univ.pi (fun _ : Fin 8 => Set.Icc (-1 : ℝ) 1)) = morseBox 8 1 from by
          rw [morseBox]]; exact morseBox_volume_lt_top 8 1)
    · exact schurInner3_ratiofin_mid 3 (by norm_num) (by norm_num) p

/-- **The corank-3 per-chart finiteness.** Mirror of `matBox2_chart_lt_top` one corank up: the radial-blow-up
chart integral (Jacobian `|y p|⁸`) is finite for `0 < c' < 4`. `chart_integrand_factor3` →
`radInd(y p)·innerS3`; the `piFinSuccAbove p` MP + Tonelli factor the pivot axis (`innerS3` is
`a`-invariant) from the 8 ratios; the radial axis is `radial_aAxis_divisor_lt_top 3`-finite (`c' < 9/2`,
holds since `c' < 4`); the ratio residual is finite via the JOINT `schurInner3_ratiofin`. -/
theorem matBox3_chart_lt_top (c' : ℝ) (hc0 : 0 < c') (hc' : c' < 4)
    (p : Fin (3 * 3)) :
    ∫⁻ y in chartDomOn (Finset.univ : Finset (Fin (3 * 3))) p \ pivotZeroOn p,
        ENNReal.ofReal |(pivotBlowupOnDeriv (Finset.univ : Finset (Fin (3 * 3))) p y).det|
          * (flatBox3 1).indicator (gFlat3 c' 1) (pivotBlowupOn
              (Finset.univ : Finset (Fin (3 * 3))) p y)
      < ⊤ := by
  set T : ℝ := 1 with hTdef
  have hT : (0:ℝ) < T := by rw [hTdef]; exact one_pos
  have hdet : ∀ y : Fin (3 * 3) → ℝ,
      |(pivotBlowupOnDeriv (Finset.univ : Finset (Fin (3 * 3))) p y).det| = |y p| ^ 8 := by
    intro y
    rw [pivotBlowupOnDeriv_det (Finset.univ : Finset (Fin (3 * 3))) p (Finset.mem_univ p) y]
    simp [abs_pow]
  simp only [hdet]
  have hmsD : MeasurableSet (chartDomOn (Finset.univ : Finset (Fin (3 * 3))) p \ pivotZeroOn p) := by
    refine MeasurableSet.diff ?_ ?_
    · have heq : chartDomOn (Finset.univ : Finset (Fin (3 * 3))) p
          = ⋂ k ∈ (Finset.univ.erase p), {y : Fin (3 * 3) → ℝ | |y k| ≤ 1} := by
        ext y
        simp only [chartDomOn, Set.mem_setOf_eq, Set.mem_iInter, Finset.mem_erase,
          Finset.mem_univ, true_and, and_true, true_implies]
      rw [heq]
      refine Finset.measurableSet_biInter (Finset.univ.erase p) (fun k _ => ?_)
      exact measurableSet_le ((measurable_pi_apply k).abs) measurable_const
    · exact (measurable_pi_apply p (measurableSet_singleton 0))
  rw [setLIntegral_congr_fun hmsD (fun y hy => chart_integrand_factor3 c' hc0 T hT p y hy.2 hy.1)]
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (3 * 3) => ℝ) p with he
  have hmp : MeasurePreserving e (volume) (volume) := volume_preserving_piFinSuccAbove _ p
  have hpre : (chartDomOn (Finset.univ : Finset (Fin (3 * 3))) p \ pivotZeroOn p)
      = e ⁻¹' (({a : ℝ | a ≠ 0}) ×ˢ (Set.univ.pi (fun _ : Fin 8 => Set.Icc (-1 : ℝ) 1))) := by
    ext y
    simp only [chartDomOn, pivotZeroOn, Set.mem_diff, Set.mem_setOf_eq, Set.mem_preimage,
      Set.mem_prod, Set.mem_pi, Set.mem_univ, true_implies, he]
    show (_ ∧ _) ↔ ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (3 * 3) => ℝ) p) y).1 ≠ 0 ∧ _
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨h2, fun j => ?_⟩
      rw [Set.mem_Icc, ← abs_le]
      exact h1 (p.succAbove j) (Finset.mem_univ _) (Fin.succAbove_ne p j)
    · rintro ⟨h1, h2⟩
      refine ⟨fun k _ hk => ?_, h1⟩
      obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hk
      have := h2 j; rw [Set.mem_Icc, ← abs_le] at this; exact this
  have hSms : MeasurableSet
      (({a : ℝ | a ≠ 0}) ×ˢ (Set.univ.pi (fun _ : Fin 8 => Set.Icc (-1 : ℝ) 1))) :=
    MeasurableSet.prod (by measurability) (MeasurableSet.univ_pi (fun _ => measurableSet_Icc))
  set g : (Fin (3 * 3) → ℝ) → ℝ≥0∞ := fun y =>
    (Set.Icc (-T) T).indicator (fun a => ENNReal.ofReal (|a| ^ ((8 : ℝ) - 2 * c'))) (y p)
      * innerS3 c' T p y with hgdef
  have hgmeas : Measurable g := by
    rw [hgdef]
    refine Measurable.mul ?_ (measurable_innerS3 c' T p)
    have hind : Measurable (fun a : ℝ =>
        (Set.Icc (-T) T).indicator (fun a => ENNReal.ofReal (|a| ^ ((8 : ℝ) - 2 * c'))) a) := by
      refine Measurable.indicator ?_ measurableSet_Icc
      exact ENNReal.measurable_ofReal.comp ((measurable_id.abs).pow_const _)
    exact hind.comp (measurable_pi_apply p)
  rw [hpre]
  have key := hmp.setLIntegral_comp_preimage_emb e.measurableEmbedding (fun q => g (e.symm q))
    (({a : ℝ | a ≠ 0}) ×ˢ (Set.univ.pi (fun _ : Fin 8 => Set.Icc (-1 : ℝ) 1)))
  have htrans : (∫⁻ y in e ⁻¹' (({a : ℝ | a ≠ 0}) ×ˢ
        (Set.univ.pi (fun _ : Fin 8 => Set.Icc (-1 : ℝ) 1))), g y)
      = ∫⁻ q in (({a : ℝ | a ≠ 0}) ×ˢ (Set.univ.pi (fun _ : Fin 8 => Set.Icc (-1 : ℝ) 1))),
          g (e.symm q) := by
    rw [← key]
    refine setLIntegral_congr_fun (e.measurable hSms) (fun y _ => ?_)
    rw [MeasurableEquiv.symm_apply_apply]
  rw [htrans]
  have hgsymm_meas : Measurable (fun q : ℝ × (Fin 8 → ℝ) => g (e.symm q)) :=
    hgmeas.comp e.symm.measurable
  rw [Measure.volume_eq_prod ℝ (Fin 8 → ℝ), setLIntegral_prod _ hgsymm_meas.aemeasurable]
  have hfactor : ∀ a : ℝ, ∀ z : Fin 8 → ℝ,
      g (e.symm (a, z))
        = (Set.Icc (-T) T).indicator (fun a => ENNReal.ofReal (|a| ^ ((8 : ℝ) - 2 * c'))) a
          * innerS3 c' T p (e.symm (0, z)) := by
    intro a z
    show (Set.Icc (-T) T).indicator (fun a => ENNReal.ofReal (|a| ^ ((8 : ℝ) - 2 * c')))
        ((e.symm (a, z)) p) * innerS3 c' T p (e.symm (a, z))
      = (Set.Icc (-T) T).indicator (fun a => ENNReal.ofReal (|a| ^ ((8 : ℝ) - 2 * c'))) a
          * innerS3 c' T p (e.symm (0, z))
    have hp_eq : (e.symm (a, z)) p = a := by rw [he]; simp [MeasurableEquiv.piFinSuccAbove]
    have hoff : innerS3 c' T p (e.symm (a, z)) = innerS3 c' T p (e.symm (0, z)) := by
      refine innerS3_offpivot c' T p _ _ (fun i hi => ?_)
      obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hi
      rw [he]; simp [MeasurableEquiv.piFinSuccAbove]
    rw [hp_eq, hoff]
  -- radial-axis factor finite (c' < 9/2 = 3²/2; holds since c' < 4)
  have hN3a : (∫⁻ a in Set.Icc (-T) T, ENNReal.ofReal (|a| ^ (((3:ℕ) ^ 2 : ℝ) - 1 - 2 * c'))) < ⊤ :=
    radial_aAxis_divisor_lt_top 3 (by norm_num) T hT c' (by norm_num; linarith)
  have hexp : (((3:ℕ) ^ 2 : ℝ) - 1 - 2 * c') = (8 : ℝ) - 2 * c' := by norm_num
  rw [hexp] at hN3a
  have hradfin : (∫⁻ a in {a : ℝ | a ≠ 0},
        (Set.Icc (-T) T).indicator (fun a => ENNReal.ofReal (|a| ^ ((8 : ℝ) - 2 * c'))) a) < ⊤ := by
    have hle1 : (∫⁻ a in {a : ℝ | a ≠ 0},
          (Set.Icc (-T) T).indicator (fun a => ENNReal.ofReal (|a| ^ ((8 : ℝ) - 2 * c'))) a)
        ≤ ∫⁻ a, (Set.Icc (-T) T).indicator
            (fun a => ENNReal.ofReal (|a| ^ ((8 : ℝ) - 2 * c'))) a := by
      have := lintegral_mono_set (μ := volume) (s := {a : ℝ | a ≠ 0}) (t := Set.univ)
        (Set.subset_univ _)
        (f := (Set.Icc (-T) T).indicator (fun a => ENNReal.ofReal (|a| ^ ((8 : ℝ) - 2 * c'))))
      rwa [setLIntegral_univ] at this
    have heq2 : (∫⁻ a, (Set.Icc (-T) T).indicator
          (fun a => ENNReal.ofReal (|a| ^ ((8 : ℝ) - 2 * c'))) a)
        = ∫⁻ a in Set.Icc (-T) T, ENNReal.ofReal (|a| ^ ((8 : ℝ) - 2 * c')) :=
      lintegral_indicator measurableSet_Icc _
    rw [heq2] at hle1
    exact lt_of_le_of_lt hle1 hN3a
  -- ratio residual finite via the JOINT inner heart (at the unit S-box, T = 1)
  have hratiofin : (∫⁻ z in (Set.univ.pi (fun _ : Fin 8 => Set.Icc (-1 : ℝ) 1)),
        innerS3 c' T p (e.symm (0, z))) < ⊤ := by
    rw [hTdef]; exact schurInner3_ratiofin c' hc0 hc' p
  have hinner : ∀ a : ℝ,
      (∫⁻ z in (Set.univ.pi (fun _ : Fin 8 => Set.Icc (-1 : ℝ) 1)), g (e.symm (a, z)))
        = (Set.Icc (-T) T).indicator (fun a => ENNReal.ofReal (|a| ^ ((8 : ℝ) - 2 * c'))) a
          * ∫⁻ z in (Set.univ.pi (fun _ : Fin 8 => Set.Icc (-1 : ℝ) 1)),
              innerS3 c' T p (e.symm (0, z)) := by
    intro a
    have hradne : (Set.Icc (-T) T).indicator
        (fun a => ENNReal.ofReal (|a| ^ ((8 : ℝ) - 2 * c'))) a ≠ ⊤ := by
      rw [Set.indicator_apply]; split <;> simp [ENNReal.ofReal_ne_top]
    rw [lintegral_congr (fun z => hfactor a z), lintegral_const_mul' _ _ hradne]
  rw [lintegral_congr hinner, lintegral_mul_const' _ _ hratiofin.ne]
  exact ENNReal.mul_lt_top hradfin hratiofin

/-- **The corank-3 core finiteness, CLOSED (the unit box).** `∫_{Δ∈matBox 3 3 1}∫_{S∈matBox 3 4 1}
frobSq(Δ·S)^{−c'} < ⊤` for `0 < c' < 4 = λ_{3,4}` (the JOINT-core SUM threshold `jp/2 + λ_{2,4} = 2 + 2`,
NOT the corank-2 `2`) — at the unit box (the `(3,3,4)` `routeMBaseNbhd` radius). The recursion's FIRST real
firing: the `Δ`-outer integral reindexes to the `Fin 9` flat carrier (`matBox3_outer_flat`), `recStep`
covers it by the 9 max-modulus-entry charts (`gFlat3_cover_sum`), each chart finite
(`matBox3_chart_lt_top`), summed by `ENNReal.sum_lt_top`. The inner JOINT heart reuses the `(3,3,4)` anchor's
`zE`/`bgShift` `M22 ↦ Δ−Sh` recognition (`ratioResidual_lt_top`, S2-free). The general-`T` box-scaling
(`= T^{21−4c'}·` this) is a roadmapped extension (needs the matrix-space `lintegral_comp_smul`). -/
theorem core_schur3_lt_top (c' : ℝ) (hc0 : 0 < c') (hc' : c' < 4) :
    (∫⁻ Δ in matBox 3 3 1, ∫⁻ S in matBox 3 4 1,
        ENNReal.ofReal ((frobSq (rmatMul Δ S)) ^ (-c'))) < ⊤ := by
  rw [matBox3_outer_flat c' 1, gFlat3_cover_sum c' 1]
  exact ENNReal.sum_lt_top.2 (fun p _ => matBox3_chart_lt_top c' hc0 hc' p)

end DLNFibre.DLN.RLCT
