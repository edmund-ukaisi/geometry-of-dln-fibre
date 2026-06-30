import DLNFibre.DLN.RLCT.Validate.RouteMSchurRectAngular
import DLNFibre.DLN.RLCT.Validate.RouteMSchurCapACarveP

/-!
# `DLNFibre.DLN.RLCT.Validate.RouteMSchurRectCarve` — the RECTANGULAR cap-A carve analytic core (item 3)

The measure-theoretic analytic half of the rectangular per-step: the asymmetric (`Δ : Fin m → Fin n`)
generalisation of `RouteMSchurCapACarveP`'s cap-A ratio-residual carve, built on the pinned interface
`RouteMSchurRectAngular` (eRect/RmatRect/piRatioRect/RmatRectNorm/slotMatRect/cellR_rect/zσRect/zERect +
the carve readbacks + innerSRect_eq_norm). Closes the interior-stratum / corank-leaf branch of the
rectangular per-step.

The residual is `(m−1)×(n−1)` (NOT square `(r−1)×(r−1)`); the recursion measure is `min(m,n)` (the
`j = 1` peel drops `(m,n) → (m−1,n−1)`). The lower IH is `RectSchurLowerIH p (rectSchurLambda p) m n`.

## Build order (this file, bottom-up, each sorry-free)
* 3b-pos: `frobSqRect_ne_zero_ae` / `frobSqShiftRect_ne_zero_ae` — a.e.-positivity of the free / shifted
  `(a×b)·(b×p)` core (the `Fin p`/rectangular `frobSqGP_ne_zero_ae` analog).
* 3b-peel / 3b-carve / 3b-assemble — the Morse-peel-translate, the per-`(M,v)` carve, and the fold
  (downstream; built after 3b-pos lands).
-/

open MeasureTheory Set
open scoped ENNReal BigOperators
namespace DLNFibre.DLN.RLCT

/-! ## 3b-pos: a.e.-positivity of the free / shifted rectangular core -/

/-- The joint coords `(Fin a → Fin b → ℝ) × (Fin b → Fin p → ℝ) ≃ᵐ ((Fin a × Fin b) ⊕ (Fin b × Fin p) → ℝ)`
(rectangular analog of `coreJoinGP`; the `Δ` block is `a×b`, the `S` block `b×p`). -/
noncomputable def coreJoinRect (a b p : ℕ) :
    ((Fin a → Fin b → ℝ) × (Fin b → Fin p → ℝ))
      ≃ᵐ (((Fin a × Fin b) ⊕ (Fin b × Fin p)) → ℝ) :=
  ((matToProdG a b).prodCongr (matToProdG b p)).trans
    (MeasurableEquiv.sumPiEquivProdPi (fun _ : (Fin a × Fin b) ⊕ (Fin b × Fin p) => ℝ)).symm

theorem coreJoinRect_inl (a b p : ℕ) (q : (Fin a → Fin b → ℝ) × (Fin b → Fin p → ℝ)) (i : Fin a) (j : Fin b) :
    coreJoinRect a b p q (Sum.inl (i, j)) = q.1 i j := by
  show (MeasurableEquiv.sumPiEquivProdPi (fun _ : (Fin a × Fin b) ⊕ (Fin b × Fin p) => ℝ)).symm
      (matToProdG a b q.1, matToProdG b p q.2) (Sum.inl (i, j)) = q.1 i j
  rw [MeasurableEquiv.coe_sumPiEquivProdPi_symm]
  show matToProdG a b q.1 (i, j) = q.1 i j
  rw [matToProdG_apply]

theorem coreJoinRect_inr (a b p : ℕ) (q : (Fin a → Fin b → ℝ) × (Fin b → Fin p → ℝ)) (k : Fin b) (j : Fin p) :
    coreJoinRect a b p q (Sum.inr (k, j)) = q.2 k j := by
  show (MeasurableEquiv.sumPiEquivProdPi (fun _ : (Fin a × Fin b) ⊕ (Fin b × Fin p) => ℝ)).symm
      (matToProdG a b q.1, matToProdG b p q.2) (Sum.inr (k, j)) = q.2 k j
  rw [MeasurableEquiv.coe_sumPiEquivProdPi_symm]
  show matToProdG b p q.2 (k, j) = q.2 k j
  rw [matToProdG_apply]

theorem measurePreserving_coreJoinRect (a b p : ℕ) :
    MeasurePreserving (coreJoinRect a b p)
      (volume : Measure ((Fin a → Fin b → ℝ) × (Fin b → Fin p → ℝ)))
      (volume : Measure (((Fin a × Fin b) ⊕ (Fin b × Fin p)) → ℝ)) := by
  unfold coreJoinRect
  refine MeasurePreserving.trans ?_
    (volume_measurePreserving_sumPiEquivProdPi_symm (fun _ : (Fin a × Fin b) ⊕ (Fin b × Fin p) => ℝ))
  rw [show (volume : Measure ((Fin a → Fin b → ℝ) × (Fin b → Fin p → ℝ))) = volume.prod volume
    from rfl,
    show (volume : Measure (((Fin a × Fin b) → ℝ) × ((Fin b × Fin p) → ℝ))) = volume.prod volume
    from rfl]
  exact (measurePreserving_matToProdG a b).prod (measurePreserving_matToProdG b p)

open MvPolynomial in
/-- The `(0,0)`-entry polynomial of `Δ·S` over the joint index `(Fin a × Fin b) ⊕ (Fin b × Fin p)`
(rectangular `coreEntryPolyGP`; needs `0 < a, 0 < b, 0 < p`). -/
noncomputable def coreEntryPolyRect (a b p : ℕ) (ha : 0 < a) (_hb : 0 < b) (hp : 0 < p) :
    MvPolynomial ((Fin a × Fin b) ⊕ (Fin b × Fin p)) ℝ :=
  ∑ k : Fin b,
    X (Sum.inl (⟨0, ha⟩, k)) * X (Sum.inr (k, ⟨0, hp⟩))

open MvPolynomial in
theorem eval_coreEntryPolyRect (a b p : ℕ) (ha : 0 < a) (hb : 0 < b) (hp : 0 < p)
    (q : (Fin a → Fin b → ℝ) × (Fin b → Fin p → ℝ)) :
    MvPolynomial.eval (coreJoinRect a b p q) (coreEntryPolyRect a b p ha hb hp)
      = ∑ k : Fin b, q.1 ⟨0, ha⟩ k * q.2 k ⟨0, hp⟩ := by
  rw [coreEntryPolyRect, map_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [map_mul, MvPolynomial.eval_X, MvPolynomial.eval_X, coreJoinRect_inl, coreJoinRect_inr]

open MvPolynomial in
theorem coreEntryPolyRect_ne_zero (a b p : ℕ) (ha : 0 < a) (hb : 0 < b) (hp : 0 < p) :
    coreEntryPolyRect a b p ha hb hp ≠ 0 := by
  intro h0
  set Δ0 : Fin a → Fin b → ℝ := fun i k => if i = ⟨0, ha⟩ ∧ k = ⟨0, hb⟩ then 1 else 0 with hΔ0
  set S0 : Fin b → Fin p → ℝ := fun k j => if k = ⟨0, hb⟩ ∧ j = ⟨0, hp⟩ then 1 else 0 with hS0
  have hval : MvPolynomial.eval (coreJoinRect a b p (Δ0, S0)) (coreEntryPolyRect a b p ha hb hp) = 1 := by
    rw [eval_coreEntryPolyRect]
    rw [Finset.sum_eq_single (⟨0, hb⟩ : Fin b)]
    · rw [hΔ0, hS0]; simp
    · intro k _ hk; rw [hS0]; simp [hk]
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [h0] at hval; simp at hval

/-- **The free rectangular core is positive a.e.** (rectangular `frobSqGP_ne_zero_ae`): for the free box
`Δ : a×b`, `S : b×p`, `0 < frobSq (Δ·S)` a.e. -/
theorem frobSqRect_ne_zero_ae (a b p : ℕ) (ha : 0 < a) (hb : 0 < b) (hp : 0 < p) :
    ∀ᵐ q : (Fin a → Fin b → ℝ) × (Fin b → Fin p → ℝ) ∂(volume),
      0 < frobSq (rmatMul q.1 q.2) := by
  have hae : ∀ᵐ x : ((Fin a × Fin b) ⊕ (Fin b × Fin p)) → ℝ,
      MvPolynomial.eval x (coreEntryPolyRect a b p ha hb hp) ≠ 0 :=
    ae_eval_ne_zero_fintype (coreEntryPolyRect a b p ha hb hp) (coreEntryPolyRect_ne_zero a b p ha hb hp)
  have hms : MeasurableSet
      {x : ((Fin a × Fin b) ⊕ (Fin b × Fin p)) → ℝ |
        MvPolynomial.eval x (coreEntryPolyRect a b p ha hb hp) ≠ 0} := by
    have : MeasurableSet {x : ((Fin a × Fin b) ⊕ (Fin b × Fin p)) → ℝ |
        MvPolynomial.eval x (coreEntryPolyRect a b p ha hb hp) = 0} :=
      (MvPolynomial.continuous_eval (coreEntryPolyRect a b p ha hb hp)).measurable
        (measurableSet_singleton 0)
    exact this.compl.congr (by ext x; simp)
  have hpull : ∀ᵐ q : (Fin a → Fin b → ℝ) × (Fin b → Fin p → ℝ) ∂(volume),
      MvPolynomial.eval (coreJoinRect a b p q) (coreEntryPolyRect a b p ha hb hp) ≠ 0 := by
    rw [← (measurePreserving_coreJoinRect a b p).map_eq] at hae
    exact (ae_map_iff (measurePreserving_coreJoinRect a b p).measurable.aemeasurable hms).1 hae
  refine hpull.mono (fun q hq => ?_)
  rw [eval_coreEntryPolyRect] at hq
  have hentry : (rmatMul q.1 q.2) ⟨0, ha⟩ ⟨0, hp⟩ = ∑ k, q.1 ⟨0, ha⟩ k * q.2 k ⟨0, hp⟩ := rfl
  have hne : (rmatMul q.1 q.2) ⟨0, ha⟩ ⟨0, hp⟩ ≠ 0 := by rw [hentry]; exact hq
  have hpos : 0 < ((rmatMul q.1 q.2) ⟨0, ha⟩ ⟨0, hp⟩) ^ 2 :=
    lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hne))
  refine lt_of_lt_of_le hpos ?_
  unfold frobSq
  calc ((rmatMul q.1 q.2) ⟨0, ha⟩ ⟨0, hp⟩) ^ 2
      = ∑ j ∈ {(⟨0, hp⟩ : Fin p)}, ((rmatMul q.1 q.2) ⟨0, ha⟩ j) ^ 2 := by simp
    _ ≤ ∑ j, ((rmatMul q.1 q.2) ⟨0, ha⟩ j) ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => sq_nonneg _)
    _ ≤ ∑ i, ∑ j, ((rmatMul q.1 q.2) i j) ^ 2 :=
        Finset.single_le_sum (f := fun i => ∑ j, ((rmatMul q.1 q.2) i j) ^ 2)
          (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _)) (Finset.mem_univ _)

/-- **The shifted rectangular core is positive a.e.** (rectangular `frobSqShiftGP_ne_zero_ae`): for a
fixed shift `Sh : a×b`, `0 < frobSq ((Δ − Sh)·S)` a.e. -/
theorem frobSqShiftRect_ne_zero_ae (a b p : ℕ) (ha : 0 < a) (hb : 0 < b) (hp : 0 < p)
    (Sh : Fin a → Fin b → ℝ) :
    ∀ᵐ q : (Fin a → Fin b → ℝ) × (Fin b → Fin p → ℝ) ∂(volume),
      0 < frobSq (rmatMul (fun i j => q.1 i j - Sh i j) q.2) := by
  set τ : (Fin a → Fin b → ℝ) × (Fin b → Fin p → ℝ) → (Fin a → Fin b → ℝ) × (Fin b → Fin p → ℝ) :=
    fun q => (q.1 + (fun i j => -Sh i j), q.2) with hτ
  have hmpΔ : MeasurePreserving (fun Δ : Fin a → Fin b → ℝ => Δ + (fun i j => -Sh i j))
      volume volume :=
    measurePreserving_add_right volume (fun i j => -Sh i j)
  have hmp : MeasurePreserving τ volume volume := by
    rw [show (volume : Measure ((Fin a → Fin b → ℝ) × (Fin b → Fin p → ℝ))) = volume.prod volume
      from rfl]
    exact hmpΔ.prod (MeasurePreserving.id volume)
  have hmsSet : MeasurableSet {q : (Fin a → Fin b → ℝ) × (Fin b → Fin p → ℝ) |
      0 < frobSq (rmatMul q.1 q.2)} :=
    measurableSet_lt measurable_const (by unfold frobSq rmatMul; fun_prop)
  have hae : ∀ᵐ x ∂(volume.map τ), 0 < frobSq (rmatMul x.1 x.2) := by
    rw [hmp.map_eq]; exact frobSqRect_ne_zero_ae a b p ha hb hp
  have hpull : ∀ᵐ q ∂(volume : Measure ((Fin a → Fin b → ℝ) × (Fin b → Fin p → ℝ))),
      0 < frobSq (rmatMul (τ q).1 (τ q).2) :=
    (ae_map_iff hmp.measurable.aemeasurable hmsSet).1 hae
  refine hpull.mono (fun q hq => ?_)
  have hΔeq : (τ q).1 = (fun i j => q.1 i j - Sh i j) := by
    funext i j; show (q.1 + (fun i j => -Sh i j)) i j = q.1 i j - Sh i j
    simp [Pi.add_apply, sub_eq_add_neg]
  have hSeq : (τ q).2 = q.2 := rfl
  rw [hΔeq, hSeq] at hq
  exact hq

/-! ## 3b-peel: the rectangular core value, the translate-domination, and the Morse-peel `_le` -/

/-- **The rectangular lower core value** (rectangular `coreSchurGenValP`): the free `(a×b)·(b×p)` two-box
core integral at exponent `c''`, radius `Kr`. The value the carve's shifted residual is dominated into. -/
noncomputable def coreSchurValRect (a b p : ℕ) (c'' Kr : ℝ) : ℝ≥0∞ :=
  ∫⁻ Δ in matBox a b Kr, ∫⁻ S in matBox b p Kr,
    ENNReal.ofReal ((frobSq (rmatMul Δ S)) ^ (-c''))

/-- The rectangular `Δ`-box translation domination (rectangular `matBoxSq_translate_le`): translating
`Δ : a×b` by `Sh` into the enlarged box `matBox a b Kg`. -/
theorem matBoxRect_translate_le {a b : ℕ} (Sh : Fin a → Fin b → ℝ) (K Kg : ℝ)
    (f : (Fin a → Fin b → ℝ) → ℝ≥0∞)
    (hsub : (fun Δ => Δ + Sh) '' (matBox a b K) ⊆ matBox a b Kg) :
    (∫⁻ Δ in matBox a b K, f (Δ + Sh)) ≤ ∫⁻ Δ' in matBox a b Kg, f Δ' := by
  set τ : (Fin a → Fin b → ℝ) → (Fin a → Fin b → ℝ) := fun Δ => Δ + Sh with hτ
  have hmp : MeasurePreserving τ volume volume := measurePreserving_add_right volume Sh
  have hemb : MeasurableEmbedding τ := (Homeomorph.addRight Sh).measurableEmbedding
  have h1 : (∫⁻ Δ in matBox a b K, f (τ Δ)) = ∫⁻ Δ' in τ '' (matBox a b K), f Δ' := by
    rw [← hmp.setLIntegral_comp_preimage_emb hemb f (τ '' (matBox a b K)),
      Set.preimage_image_eq (matBox a b K) hemb.injective]
  calc (∫⁻ Δ in matBox a b K, f (Δ + Sh)) = ∫⁻ Δ' in τ '' (matBox a b K), f Δ' := h1
    _ ≤ ∫⁻ Δ' in matBox a b Kg, f Δ' := lintegral_mono_set hsub

/-- **The rectangular shift-uniform residual `_le` bound** (rectangular `schurResidGP_translate_le`):
for `|Sh| ≤ B` (`0 < a, 0 < b`), the shifted `(a×b)·(b×p)` core is `≤ coreSchurValRect a b p c'' (K+B)`,
INDEPENDENT of `Sh` (only the radius `K+B` records the shift size). Chain: `S`-monotone enlarge `K → K+B`,
then translate `Δ ↦ Δ − Sh` into radius `K+B` (`matBoxRect_translate_le`). -/
theorem schurResidRect_translate_le (a b p : ℕ) (ha : 0 < a) (hb : 0 < b)
    (Sh : Fin a → Fin b → ℝ) (B : ℝ) (hB : ∀ i j, |Sh i j| ≤ B) (c'' : ℝ) (K : ℝ) :
    (∫⁻ Δ in matBox a b K, ∫⁻ S in matBox b p K,
        ENNReal.ofReal ((frobSq (rmatMul (fun i j => Δ i j - Sh i j) S)) ^ (-c'')))
      ≤ coreSchurValRect a b p c'' (K + B) := by
  have hB0 : 0 ≤ B := le_trans (abs_nonneg _) (hB ⟨0, ha⟩ ⟨0, hb⟩)
  set g : (Fin a → Fin b → ℝ) → ℝ≥0∞ := fun Δ =>
    ∫⁻ S in matBox b p (K + B), ENNReal.ofReal ((frobSq (rmatMul Δ S)) ^ (-c'')) with hg
  have hSsub : matBox b p K ⊆ matBox b p (K + B) := by
    intro X hX i k; have := Set.mem_Icc.1 (hX i k); rw [Set.mem_Icc]
    constructor <;> [linarith [this.1]; linarith [this.2]]
  have hle1 : ∀ Δ : Fin a → Fin b → ℝ,
      (∫⁻ S in matBox b p K,
          ENNReal.ofReal ((frobSq (rmatMul (fun i j => Δ i j - Sh i j) S)) ^ (-c'')))
        ≤ g (Δ + (fun i j => -Sh i j)) := by
    intro Δ
    have hmono := lintegral_mono_set (μ := volume) hSsub
      (f := fun S => ENNReal.ofReal ((frobSq (rmatMul (fun i j => Δ i j - Sh i j) S)) ^ (-c'')))
    refine le_trans hmono (le_of_eq ?_)
    have heqfun : (fun i j => Δ i j - Sh i j) = (Δ + (fun i j => -Sh i j)) := by
      funext i j; simp [Pi.add_apply, sub_eq_add_neg]
    rw [hg]; refine lintegral_congr (fun S => ?_); rw [heqfun]
  refine le_trans (lintegral_mono hle1) ?_
  have hsub : (fun Δ => Δ + (fun i j => -Sh i j)) '' (matBox a b K)
      ⊆ matBox a b (K + B) := by
    rintro Δ' ⟨Δ, hΔ, rfl⟩
    intro i j
    show -(K + B) ≤ Δ i j + (-Sh i j) ∧ Δ i j + (-Sh i j) ≤ K + B
    have hΔij := Set.mem_Icc.1 (hΔ i j)
    have hShij := abs_le.1 (hB i j)
    constructor <;> [linarith [hΔij.1, hShij.2]; linarith [hΔij.2, hShij.1]]
  refine le_trans (matBoxRect_translate_le (fun i j => -Sh i j) K (K + B) g hsub) (le_of_eq ?_)
  rw [coreSchurValRect]

/-- **The rectangular SHIFTED resolved-form UNIFORM `_le` bound** (the JOINT Morse-peel brick;
rectangular `resolvedShiftRGP_le`). For a fixed shift `Sh : a×b` with `|Sh| ≤ B`, `p/2 < c'`, `K > 0`,
the resolved integral `∫_Δ∫_S∫_{T∈morseBox p K} (∑ T_i² + frobSq((Δ−Sh)·S))^{−c'}` is
`≤ ofReal(Cresid p c') · coreSchurValRect a b p (c'−p/2) (K+B)` — INDEPENDENT of `Sh`. The `Fin p` Morse
`T`-peel (`core_T_peel_le_aeG`, threshold `p/2`) on the shifted core (`> 0` a.e. by
`frobSqShiftRect_ne_zero_ae`) leaves the residual at `c'−p/2`, closed by `schurResidRect_translate_le`. -/
theorem resolvedShiftRRect_le (a b p : ℕ) (ha : 0 < a) (hb : 0 < b) (hp : 0 < p)
    (Sh : Fin a → Fin b → ℝ) (B : ℝ) (hB : ∀ i j, |Sh i j| ≤ B)
    (K : ℝ) (hK : 0 < K) (c' : ℝ) (hcp : (p : ℝ) / 2 < c') :
    (∫⁻ Δ in matBox a b K, ∫⁻ S in matBox b p K, ∫⁻ T in morseBox p K,
        ENNReal.ofReal ((∑ i, (T i) ^ 2
          + frobSq (rmatMul (fun x y => Δ x y - Sh x y) S)) ^ (-c')))
      ≤ ENNReal.ofReal (Cresid p c') * coreSchurValRect a b p (c' - (p : ℝ) / 2) (K + B) := by
  obtain ⟨pm, rfl⟩ : ∃ pm, p = pm + 1 := ⟨p - 1, by omega⟩
  set w : (Fin a → Fin b → ℝ) × (Fin b → Fin (pm + 1) → ℝ) → ℝ :=
    fun q => frobSq (rmatMul (fun x y => q.1 x y - Sh x y) q.2) with hwdef
  have hmeasT : Measurable (fun q : ((Fin a → Fin b → ℝ) × (Fin b → Fin (pm + 1) → ℝ))
      × (Fin (pm + 1) → ℝ) => ENNReal.ofReal ((∑ i, (q.2 i) ^ 2 + w q.1) ^ (-c'))) := by
    apply ENNReal.measurable_ofReal.comp
    apply Measurable.comp (g := fun t : ℝ => t ^ (-c')) (by fun_prop)
    show Measurable (fun q : ((Fin a → Fin b → ℝ) × (Fin b → Fin (pm + 1) → ℝ))
        × (Fin (pm + 1) → ℝ) =>
        (∑ i, (q.2 i) ^ 2 + frobSq (rmatMul (fun x y => q.1.1 x y - Sh x y) q.1.2)))
    unfold frobSq rmatMul; fun_prop
  -- Tonelli ∫_Δ∫_S∫_T = ∫_{(Δ,S)}∫_T
  have hstep1 : ∫⁻ Δ in matBox a b K, ∫⁻ S in matBox b (pm + 1) K, ∫⁻ T in morseBox (pm + 1) K,
        ENNReal.ofReal ((∑ i, (T i) ^ 2 + frobSq (rmatMul (fun x y => Δ x y - Sh x y) S)) ^ (-c'))
      = ∫⁻ q in (matBox a b K ×ˢ matBox b (pm + 1) K),
          (∫⁻ T in morseBox (pm + 1) K,
          ENNReal.ofReal ((∑ i, (T i) ^ 2 + w q) ^ (-c'))) ∂volume := by
    rw [Measure.volume_eq_prod (Fin a → Fin b → ℝ) (Fin b → Fin (pm + 1) → ℝ),
      setLIntegral_prod _ (Measurable.lintegral_prod_right hmeasT).aemeasurable]
  rw [hstep1]
  have hwpos : ∀ᵐ z ∂(volume.restrict
        (matBox a b K ×ˢ matBox b (pm + 1) K)), 0 < w z :=
    ae_restrict_of_ae (frobSqShiftRect_ne_zero_ae a b (pm + 1) ha hb hp Sh)
  have hpeel := core_T_peel_le_aeG (m := pm) (volume) c' (by exact_mod_cast hcp) K hK w
    (matBox a b K ×ˢ matBox b (pm + 1) K) hwpos
  refine le_trans hpeel ?_
  refine mul_le_mul' (le_refl _) ?_
  have hmeasResid : Measurable
      (fun q : (Fin a → Fin b → ℝ) × (Fin b → Fin (pm + 1) → ℝ) =>
        ENNReal.ofReal ((w q) ^ (-(c' - (pm + 1 : ℝ) / 2)))) := by
    apply ENNReal.measurable_ofReal.comp
    apply Measurable.comp (g := fun t : ℝ => t ^ (-(c' - (pm + 1 : ℝ) / 2))) (by fun_prop)
    show Measurable (fun q : (Fin a → Fin b → ℝ) × (Fin b → Fin (pm + 1) → ℝ) =>
        frobSq (rmatMul (fun x y => q.1 x y - Sh x y) q.2))
    unfold frobSq rmatMul; fun_prop
  have hresid : (∫⁻ q in (matBox a b K ×ˢ matBox b (pm + 1) K),
        ENNReal.ofReal ((w q) ^ (-(c' - (pm + 1 : ℝ) / 2))))
      = ∫⁻ Δ in matBox a b K, ∫⁻ S in matBox b (pm + 1) K,
          ENNReal.ofReal ((frobSq (rmatMul (fun x y => Δ x y - Sh x y) S))
            ^ (-(c' - ((pm : ℝ) + 1) / 2))) := by
    rw [Measure.volume_eq_prod (Fin a → Fin b → ℝ) (Fin b → Fin (pm + 1) → ℝ),
      setLIntegral_prod _ hmeasResid.aemeasurable]
  rw [hresid]
  have hcast : (c' - ((pm : ℝ) + 1) / 2) = (c' - ((pm + 1 : ℕ) : ℝ) / 2) := by push_cast; ring
  rw [hcast]
  exact schurResidRect_translate_le a b (pm + 1) ha hb Sh B hB (c' - ((pm + 1 : ℕ) : ℝ) / 2) K

end DLNFibre.DLN.RLCT
