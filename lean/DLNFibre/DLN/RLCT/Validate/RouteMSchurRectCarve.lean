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

/-! ## 3b-carve: the top-row N2b bridge + the rectangular row-shear -/

/-- **The N2b top-row bridge (rectangular, `t = 1`).** With pivot `R ⟨0⟩ ⟨0⟩ = 1` for `R : Fin m → Fin n`,
the N2b top block `frobSq` of row `0` of `R·S` expands to the shear sum
`∑_q (S ⟨0⟩ q + ∑_a R ⟨0⟩ ⟨1+a⟩ · S ⟨1+a⟩ q)²` — the contraction over `Fin n` block-splits at `1`
(`fin_sum_block_split 1`, needs `1 ≤ n`). The asymmetric `frobSqTopRowP_eq_shearP1` (`1 ≤ m, 1 ≤ n`). -/
theorem frobSqTopRowRect_eq_shear (m n p : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n) (R : Fin m → Fin n → ℝ)
    (hpiv : R ⟨0, by omega⟩ ⟨0, by omega⟩ = 1) (S : Fin n → Fin p → ℝ) :
    frobSq (fun a : Fin 1 => rmatMul R S ⟨(a : ℕ), by omega⟩)
      = ∑ q, (S ⟨0, by omega⟩ q
          + ∑ a : Fin (n - 1), R ⟨0, by omega⟩ ⟨1 + (a : ℕ), by omega⟩
              * S ⟨1 + (a : ℕ), by omega⟩ q) ^ 2 := by
  unfold frobSq
  rw [Fin.sum_univ_one]
  refine Finset.sum_congr rfl (fun q _ => ?_)
  congr 1
  show rmatMul R S ⟨0, by omega⟩ q = _
  unfold rmatMul
  rw [fin_sum_block_split 1 (show (1 : ℕ) ≤ n by omega) (fun k : Fin n => R ⟨0, by omega⟩ k * S k q)]
  congr 1
  · rw [Fin.sum_univ_one]
    have h0 : (⟨(0 : Fin 1), lt_of_lt_of_le (0 : Fin 1).2 (show (1:ℕ) ≤ n by omega)⟩ : Fin n)
        = ⟨0, by omega⟩ := rfl
    rw [h0, hpiv, one_mul]

/-- **The rectangular generic row-shear** (`Sc : sr × m` residual; the `Sc`-row-count `sr` generalises
`stepShearGP`'s square `Sc : m × m`). The top row `S 0` of the `(m+1)×p` box shears by `b : Fin m`
couplings into the `Fin p` Morse spectator; the residual `frobSq (Sc · S_bot)` is carried unchanged. The
`Sc`-row-count never enters the measure-theory — verbatim `stepShearGP` with `Sc : sr × m`. -/
theorem stepShearGP_rect (sr m p : ℕ) (b : Fin m → ℝ) (hb : ∀ a, |b a| ≤ 1)
    (Sc : Fin sr → Fin m → ℝ) (T : ℝ) (hT : 0 < T) (c' : ℝ) :
    (∫⁻ S in matBox (m + 1) p T,
        ENNReal.ofReal (((∑ q, (S 0 q + ∑ a, b a * S a.succ q) ^ 2)
          + frobSq (rmatMul Sc (fun a q => S a.succ q))) ^ (-c')))
      ≤ ∫⁻ S_bot in matBox m p T, ∫⁻ T' in morseBox p ((m + 1 : ℕ) * T),
          ENNReal.ofReal (((∑ q, (T' q) ^ 2) + frobSq (rmatMul Sc S_bot)) ^ (-c')) := by
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => Fin p → ℝ) 0 with he
  have hmp : MeasurePreserving e volume volume :=
    volume_preserving_piFinSuccAbove (fun _ : Fin (m + 1) => Fin p → ℝ) 0
  set H : (Fin p → ℝ) × (Fin m → Fin p → ℝ) → ℝ≥0∞ := fun q =>
    ENNReal.ofReal (((∑ qq, (q.1 qq + ∑ a, b a * q.2 a qq) ^ 2)
      + frobSq (rmatMul Sc q.2)) ^ (-c')) with hHdef
  have hHmeas : Measurable H := by
    rw [hHdef]
    apply ENNReal.measurable_ofReal.comp
    apply Measurable.comp (g := fun t : ℝ => t ^ (-c')) (by fun_prop)
    refine Measurable.add ?_ ?_
    · refine Finset.measurable_sum _ (fun qq _ => ?_)
      refine Measurable.pow_const ?_ 2
      have h0 : Measurable (fun q : (Fin p → ℝ) × (Fin m → Fin p → ℝ) => q.1 qq) :=
        (measurable_pi_apply qq).comp measurable_fst
      refine h0.add (Finset.measurable_sum _ (fun a _ => ?_))
      exact measurable_const.mul ((measurable_pi_apply qq).comp
        ((measurable_pi_apply a).comp measurable_snd))
    · unfold frobSq rmatMul
      refine Finset.measurable_sum _ (fun i _ => ?_)
      refine Finset.measurable_sum _ (fun j _ => ?_)
      refine Measurable.pow_const ?_ 2
      refine Finset.measurable_sum _ (fun k _ => ?_)
      exact measurable_const.mul ((measurable_pi_apply j).comp
        ((measurable_pi_apply k).comp measurable_snd))
  have hsplit : matBox (m + 1) p T
      = e ⁻¹' ((Set.univ.pi (fun _ : Fin p => Set.Icc (-T) T)) ×ˢ matBox m p T) := by
    ext S
    simp only [he, Set.mem_preimage, Set.mem_prod, matBox, Set.mem_setOf_eq, Set.mem_pi,
      Set.mem_univ, true_implies]
    constructor
    · intro h
      refine ⟨fun q => h 0 q, fun a q => h a.succ q⟩
    · rintro ⟨h1, h2⟩ i k
      rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i', rfl⟩
      · exact h1 k
      · exact h2 i' k
  have hLHS : (∫⁻ S in matBox (m + 1) p T,
      ENNReal.ofReal (((∑ q, (S 0 q + ∑ a, b a * S a.succ q) ^ 2)
        + frobSq (rmatMul Sc (fun a q => S a.succ q))) ^ (-c')))
      = ∫⁻ pq in ((Set.univ.pi (fun _ : Fin p => Set.Icc (-T) T)) ×ˢ matBox m p T), H pq := by
    rw [hsplit, ← hmp.setLIntegral_comp_preimage_emb e.measurableEmbedding H
        ((Set.univ.pi (fun _ : Fin p => Set.Icc (-T) T)) ×ˢ matBox m p T)]
    refine setLIntegral_congr_fun ?_ (fun S _ => rfl)
    exact e.measurable (MeasurableSet.prod
      (MeasurableSet.univ_pi (fun _ => measurableSet_Icc)) (matBox_measurableSet m p T))
  rw [hLHS, Measure.volume_eq_prod, setLIntegral_prod _ hHmeas.aemeasurable,
    lintegral_lintegral_swap hHmeas.aemeasurable]
  refine setLIntegral_mono_ae' (matBox_measurableSet m p T) (ae_of_all _ (fun S_bot hSbot => ?_))
  set shift : Fin p → ℝ := fun q => ∑ a, b a * S_bot a q with hshift
  set f : (Fin p → ℝ) → ℝ≥0∞ := fun T' =>
    ENNReal.ofReal (((∑ q, (T' q) ^ 2) + frobSq (rmatMul Sc S_bot)) ^ (-c')) with hf
  have hrw : ∀ S_top : Fin p → ℝ, H (S_top, S_bot) = f (S_top + shift) := by
    intro S_top; rw [hHdef, hf]; rfl
  rw [lintegral_congr hrw]
  refine lintegral_translate_leG p shift (Set.univ.pi (fun _ : Fin p => Set.Icc (-T) T))
    (morseBox p ((m + 1 : ℕ) * T)) f ?_
  rintro T' ⟨v, hv, rfl⟩
  simp only [morseBox, Set.mem_pi, Set.mem_univ, true_implies] at hv ⊢
  intro q
  have hvq := Set.mem_Icc.1 (hv q)
  have htermbd : ∀ a : Fin m, |b a * S_bot a q| ≤ T := by
    intro a
    rw [abs_mul]
    have hSa := Set.mem_Icc.1 (hSbot a q)
    calc |b a| * |S_bot a q| ≤ 1 * T :=
          mul_le_mul (hb a) (abs_le.2 hSa) (abs_nonneg _) (by norm_num)
      _ = T := by ring
  have hshiftbd : |shift q| ≤ (m : ℝ) * T := by
    rw [hshift]
    calc |∑ a, b a * S_bot a q| ≤ ∑ a, |b a * S_bot a q| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _a : Fin m, T := Finset.sum_le_sum (fun a _ => htermbd a)
      _ = (m : ℝ) * T := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [Set.mem_Icc, Pi.add_apply, hshift]
  have habs := abs_le.1 hshiftbd
  push_cast
  constructor <;> [nlinarith [hvq.1, habs.1, hT]; nlinarith [hvq.2, habs.2, hT]]

/-- **The rectangular row-indexed shear** (the carve's `S : Fin n → Fin p` native index form, residual
`Sc : (m−1)×(n−1)`). Transports `stepShearGP_rect` (at `sr = m−1`, `m = n−1`) through the row-reindex
`er : Fin ((n−1)+1) ≃ Fin n`. The asymmetric `stepShearP_r1`. -/
theorem stepShearRect (m n p : ℕ) (hn : 1 ≤ n) (b : Fin (n - 1) → ℝ) (hb : ∀ a, |b a| ≤ 1)
    (Sc : Matrix (Fin (m - 1)) (Fin (n - 1)) ℝ) (T : ℝ) (hT : 0 < T) (c' : ℝ) :
    (∫⁻ S in matBox n p T,
        ENNReal.ofReal (((∑ q, (S ⟨0, by omega⟩ q + ∑ a, b a * S ⟨1 + (a : ℕ), by omega⟩ q) ^ 2)
          + frobSq (rmatMul Sc (fun a q => S ⟨1 + (a : ℕ), by omega⟩ q))) ^ (-c')))
      ≤ ∫⁻ S_bot in matBox (n - 1) p T, ∫⁻ T' in morseBox p ((n : ℕ) * T),
          ENNReal.ofReal (((∑ q, (T' q) ^ 2) + frobSq (rmatMul Sc S_bot)) ^ (-c')) := by
  have hrm : (n - 1) + 1 = n := Nat.sub_add_cancel hn
  set er : Fin ((n - 1) + 1) ≃ Fin n := finCongr hrm with her
  set E := MeasurableEquiv.piCongrLeft (fun _ : Fin n => Fin p → ℝ) er with hE
  have hmp : MeasurePreserving E.symm volume volume :=
    (volume_measurePreserving_piCongrLeft (fun _ : Fin n => Fin p → ℝ) er).symm E
  have hpre : matBox n p T = E.symm ⁻¹' (matBox ((n - 1) + 1) p T) := by
    ext S
    simp only [Set.mem_preimage, matBox, Set.mem_setOf_eq]
    constructor
    · intro h i k; exact h (er i) k
    · intro h i k
      have := h (er.symm i) k
      rw [show E.symm S (er.symm i) k = S i k from by
        show S (er (er.symm i)) k = S i k; rw [Equiv.apply_symm_apply]] at this
      exact this
  set f : (Fin ((n - 1) + 1) → Fin p → ℝ) → ℝ≥0∞ := fun S =>
    ENNReal.ofReal (((∑ q, (S 0 q + ∑ a, b a * S a.succ q) ^ 2)
      + frobSq (rmatMul Sc (fun a q => S a.succ q))) ^ (-c')) with hf
  have hkey := hmp.setLIntegral_comp_preimage_emb E.symm.measurableEmbedding f
    (matBox ((n - 1) + 1) p T)
  rw [← hpre] at hkey
  have hLHSeq : (∫⁻ S in matBox n p T,
      ENNReal.ofReal (((∑ q, (S ⟨0, by omega⟩ q + ∑ a, b a * S ⟨1 + (a : ℕ), by omega⟩ q) ^ 2)
        + frobSq (rmatMul Sc (fun a q => S ⟨1 + (a : ℕ), by omega⟩ q))) ^ (-c')))
      = ∫⁻ S in matBox n p T, f (E.symm S) := by
    refine lintegral_congr (fun S => ?_)
    rw [hf]
    have hrow0 : E.symm S (0 : Fin ((n - 1) + 1)) = S ⟨0, by omega⟩ := by
      show S (er 0) = S ⟨0, by omega⟩; rfl
    have hrowsucc : ∀ a : Fin (n - 1), E.symm S a.succ = S ⟨1 + (a : ℕ), by omega⟩ := by
      intro a
      show S (er a.succ) = S ⟨1 + (a : ℕ), by omega⟩
      congr 1; apply Fin.ext; simp [her, Fin.succ]; omega
    simp only [hrow0, hrowsucc]
  rw [hLHSeq, hkey]
  have hshear := stepShearGP_rect (m - 1) (n - 1) p b hb Sc T hT c'
  have hcast : (((n - 1) + 1 : ℕ) : ℝ) * T = ((n : ℕ) : ℝ) * T := by rw [hrm]
  rw [hcast] at hshear
  exact hshear

/-! ## 3b-carve: the per-`(M,v)` carve bound (the heart) -/

/-- **The per-`(M,v)` carve bound (the rectangular firing heart, `M` FREE).** For the carved angular
matrix `R = RmatRectNorm (zERect.symm (M,v))` (pivot `1`, `|entries| ≤ 1` when `M,v ∈ [−1,1]`),
`p/2 < c'`, the inner-`S` integral over `matBox n p T` is bounded by `ofReal(c₀^{−c'})` times the per-`M`
resolved slice (radius `K = max 1 (n·T)`, shift `Sh = bgShiftRect v`): N2b (`t = 1`) lower-bounds
`frobSq(R·S)` by `c₀·(frobSq row0 + frobSq(Sc·S_bot))`; the top-row bridge (`frobSqTopRowRect_eq_shear`)
+ `stepShearRect` peel the `Fin p` Morse spectator; the carve readback (`ScCarve_rect_eq`) turns `Sc`
into `M − bgShiftRect v`. The asymmetric `innerSGenCarveP_le`. -/
theorem innerSGenCarveRect_le (m n N p : ℕ) (hN : m * n = N + 1) (hm : 1 ≤ m) (hn : 1 ≤ n)
    (hmn : 2 ≤ m * n) (hp : 0 < p) (c' : ℝ) (hcp : (p : ℝ) / 2 < c')
    (pivot : Fin (m * n)) (T : ℝ) (hT : 0 < T)
    (M : (Fin (m - 1) × Fin (n - 1)) → ℝ) (v : (Fin (m - 1) ⊕ Fin (n - 1)) → ℝ)
    (hM : M ∈ Set.univ.pi (fun _ : (Fin (m - 1) × Fin (n - 1)) => Set.Icc (-1 : ℝ) 1))
    (hv : v ∈ Set.univ.pi (fun _ : (Fin (m - 1) ⊕ Fin (n - 1)) => Set.Icc (-1 : ℝ) 1)) :
    (∫⁻ S in matBox n p T,
        ENNReal.ofReal ((frobSq (rmatMul (RmatRectNorm m n N hN hm hn pivot
          ((zERect m n N hN hm hn hmn pivot).symm (M, v))) S)) ^ (-c')))
      ≤ ENNReal.ofReal
          (((schur_minorPivot_split_rect (m := m) (n := n) (p := p) 1 hm hn).choose) ^ (-c'))
        * (∫⁻ S_bot in matBox (n - 1) p (max 1 ((n : ℝ) * T)),
            ∫⁻ T' in morseBox p (max 1 ((n : ℝ) * T)),
              ENNReal.ofReal (((∑ q, (T' q) ^ 2)
                + frobSq (rmatMul (fun a b => M (a, b) - bgShiftRect m n v a b) S_bot)) ^ (-c'))) := by
  classical
  have hc0 : 0 < c' := lt_trans (by positivity) hcp
  set z := (zERect m n N hN hm hn hmn pivot).symm (M, v) with hzdef
  set R : Fin m → Fin n → ℝ := RmatRectNorm m n N hN hm hn pivot z with hRdef
  have hpiv : R ⟨0, by omega⟩ ⟨0, by omega⟩ = 1 := RmatRectNorm_pivot m n N hN hm hn pivot z
  have hbd : ∀ a b, |R a b| ≤ 1 := by
    intro a b
    by_cases hab : a = ⟨0, by omega⟩ ∧ b = ⟨0, by omega⟩
    · rw [hab.1, hab.2, hpiv]; norm_num
    · refine RmatRectNorm_offpivot_le m n N hN hm hn pivot z ?_ a b hab
      intro k _
      rw [hzdef, zERect_symm_apply]
      rcases (zσRect m n N hN hm hn hmn pivot k) with s | s
      · exact hM s (Set.mem_univ s)
      · exact hv s (Set.mem_univ s)
  set RM : Matrix (Fin m) (Fin n) ℝ := Matrix.of R with hRM
  set c₀ := (schur_minorPivot_split_rect (m := m) (n := n) (p := p) 1 hm hn).choose with hc₀def
  obtain ⟨c₁, hc₀, hc₁, hN2b⟩ := (schur_minorPivot_split_rect (m := m) (n := n) (p := p) 1 hm hn).choose_spec
  set M11 : Matrix (Fin 1) (Fin 1) ℝ :=
    Matrix.of (fun a b : Fin 1 => RM ⟨a, lt_of_lt_of_le a.2 hm⟩ ⟨b, lt_of_lt_of_le b.2 hn⟩) with hM11
  have hM11_one : M11 = 1 := by
    ext a b; fin_cases a; fin_cases b
    simp only [hM11, hRM, Matrix.of_apply, Matrix.one_apply_eq]
    exact hpiv
  have hpivdet : M11.det = 1 := by rw [hM11_one]; simp
  have hpivot' : ∀ (I : Fin 1 → Fin m) (J : Fin 1 → Fin n),
      |(RM.submatrix I J).det| ≤ |M11.det| := by
    intro I J
    rw [Matrix.det_fin_one, hpivdet, abs_one, Matrix.submatrix_apply]
    exact hbd (I 0) (J 0)
  have hne : M11.det ≠ 0 := by rw [hpivdet]; norm_num
  obtain ⟨Sc, hSceq, _hlo0, _hup0⟩ := hN2b RM (fun _ _ => 0) hbd hpivot' hne
  set X : (Fin n → Fin p → ℝ) → ℝ := fun S =>
    frobSq (fun a : Fin 1 => rmatMul (fun x y => R x y) S ⟨a, lt_of_lt_of_le a.2 hm⟩)
      + frobSq (rmatMul (fun a b => Sc a b) (fun a : Fin (n - 1) => S ⟨1 + a, by omega⟩)) with hXdef
  have hlow : ∀ S, c₀ * X S ≤ frobSq (rmatMul (fun a b => R a b) S) := by
    intro S
    obtain ⟨Sc', hSceq', hlo, _⟩ := hN2b RM S hbd hpivot' hne
    have hSceq2 : Sc' = Sc := by rw [hSceq', ← hSceq]
    subst hSceq2
    simpa only [hXdef] using hlo
  have hupp : ∀ S, frobSq (rmatMul (fun a b => R a b) S) ≤ c₁ * X S := by
    intro S
    obtain ⟨Sc', hSceq', _, hup⟩ := hN2b RM S hbd hpivot' hne
    have hSceq2 : Sc' = Sc := by rw [hSceq', ← hSceq]
    subst hSceq2
    simpa only [hXdef] using hup
  have hXnn : ∀ S, 0 ≤ X S := fun S => by
    rw [hXdef]; exact add_nonneg (frobSq_nonneg _) (frobSq_nonneg _)
  have hpt : ∀ S, ENNReal.ofReal ((frobSq (rmatMul (fun a b => R a b) S)) ^ (-c'))
      ≤ ENNReal.ofReal (c₀ ^ (-c')) * ENNReal.ofReal ((X S) ^ (-c')) := by
    intro S
    refine ofReal_rpow_le_const_mul (X S) (frobSq (rmatMul (fun a b => R a b) S)) c₀ c'
      hc0 hc₀ (hXnn S) (frobSq_nonneg _) (hlow S) ?_
    intro hX0
    have := hupp S
    rw [hX0, mul_zero] at this
    exact le_antisymm this (frobSq_nonneg _)
  -- M11⁻¹ = id (the 1×1 pivot inverse is the identity)
  have hM11inv : ∀ s t : Fin 1, (M11⁻¹) s t = if s = t then 1 else 0 := by
    intro s t; rw [hM11_one]; simp [Matrix.one_apply]
  -- the carve readback: Sc a b = M (a,b) − bgShiftRect v a b
  have hSc_carve : (fun a b => Sc a b)
      = fun (a : Fin (m - 1)) (b : Fin (n - 1)) => M (a, b) - bgShiftRect m n v a b := by
    funext a b
    rw [hSceq]
    -- M11⁻¹ = id collapses the 1×1 Cramer factor; the simp set's exact firing varies, so the
    -- unused-simp-args linter is locally disabled (the convert below pins the result).
    set_option linter.unusedSimpArgs false in
    simp only [Matrix.sub_apply, Matrix.of_apply, Matrix.mul_apply, hM11inv,
      Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton, if_true, mul_one, mul_ite,
      mul_zero, hRM]
    have hcarve := ScCarve_rect_eq m n N hN hm hn hmn pivot M v a b
    rw [← hzdef, ← hRdef] at hcarve
    -- the (1×1) pivot-inverse factor is 1 (it is M11⁻¹ 0 0)
    have hinv00 : (Matrix.of (fun a b : Fin 1 =>
        R ⟨(a : ℕ), by omega⟩ ⟨(b : ℕ), by omega⟩))⁻¹ 0 0 = 1 := by
      have : (Matrix.of (fun a b : Fin 1 =>
          R ⟨(a : ℕ), by omega⟩ ⟨(b : ℕ), by omega⟩)) = M11 := by
        ext s t; fin_cases s; fin_cases t; rfl
      rw [this, hM11inv]; simp
    rw [hinv00, mul_one]
    exact hcarve
  set K := max 1 ((n : ℝ) * T) with hKdef
  have hKpos : 0 < K := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  set bcoup : Fin (n - 1) → ℝ := fun a => R ⟨0, by omega⟩ ⟨1 + (a : ℕ), by omega⟩ with hbcoup
  have hbcoup_le : ∀ a, |bcoup a| ≤ 1 := fun a => hbd _ _
  calc (∫⁻ S in matBox n p T,
          ENNReal.ofReal ((frobSq (rmatMul (fun a b => R a b) S)) ^ (-c')))
      ≤ ∫⁻ S in matBox n p T, ENNReal.ofReal (c₀ ^ (-c')) * ENNReal.ofReal ((X S) ^ (-c')) :=
        lintegral_mono hpt
    _ = ENNReal.ofReal (c₀ ^ (-c'))
          * ∫⁻ S in matBox n p T, ENNReal.ofReal ((X S) ^ (-c')) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ ≤ ENNReal.ofReal (c₀ ^ (-c'))
          * (∫⁻ S_bot in matBox (n - 1) p K, ∫⁻ T' in morseBox p K,
              ENNReal.ofReal (((∑ q, (T' q) ^ 2)
                + frobSq (rmatMul (fun a b => M (a, b) - bgShiftRect m n v a b) S_bot)) ^ (-c'))) := by
        refine mul_le_mul' (le_refl _) ?_
        have hpiv' : (fun x y => R x y) ⟨0, by omega⟩ ⟨0, by omega⟩ = 1 := hpiv
        have hXrw : ∀ S, X S
            = (∑ q, (S ⟨0, by omega⟩ q
                + ∑ a, bcoup a * S ⟨1 + (a : ℕ), by omega⟩ q) ^ 2)
              + frobSq (rmatMul (fun a b => Sc a b) (fun a q => S ⟨1 + (a : ℕ), by omega⟩ q)) := by
          intro S
          simp only [hXdef]
          rw [frobSqTopRowRect_eq_shear m n p hm hn (fun x y => R x y) hpiv' S]
        calc (∫⁻ S in matBox n p T, ENNReal.ofReal ((X S) ^ (-c')))
            = ∫⁻ S in matBox n p T,
                ENNReal.ofReal (((∑ q, (S ⟨0, by omega⟩ q
                    + ∑ a, bcoup a * S ⟨1 + (a : ℕ), by omega⟩ q) ^ 2)
                  + frobSq (rmatMul (fun a b => Sc a b)
                      (fun a q => S ⟨1 + (a : ℕ), by omega⟩ q))) ^ (-c')) := by
              refine lintegral_congr (fun S => ?_); rw [hXrw S]
          _ ≤ ∫⁻ S_bot in matBox (n - 1) p T, ∫⁻ T' in morseBox p ((n : ℕ) * T),
                ENNReal.ofReal (((∑ q, (T' q) ^ 2)
                  + frobSq (rmatMul (fun a b => Sc a b) S_bot)) ^ (-c')) :=
              stepShearRect m n p hn bcoup hbcoup_le (Matrix.of (fun a b => Sc a b)) T hT c'
          _ ≤ ∫⁻ S_bot in matBox (n - 1) p K, ∫⁻ T' in morseBox p K,
                ENNReal.ofReal (((∑ q, (T' q) ^ 2)
                  + frobSq (rmatMul (fun a b => M (a, b) - bgShiftRect m n v a b) S_bot)) ^ (-c')) := by
              have hSsub : matBox (n - 1) p T ⊆ matBox (n - 1) p K := by
                intro Y hY i k; have := Set.mem_Icc.1 (hY i k); rw [Set.mem_Icc]
                have hTK : T ≤ K := le_trans (le_mul_of_one_le_left hT.le
                  (by exact_mod_cast (show (1:ℕ) ≤ n by omega))) (le_max_right _ _)
                constructor <;> [linarith [this.1]; linarith [this.2]]
              have hTsub : morseBox p ((n : ℕ) * T) ⊆ morseBox p K := by
                intro Y hY
                simp only [morseBox, Set.mem_pi, Set.mem_univ, true_implies] at hY ⊢
                intro i
                have hrTK : ((n : ℕ) : ℝ) * T ≤ K := le_max_right _ _
                have := Set.mem_Icc.1 (hY i); rw [Set.mem_Icc]
                constructor <;> [linarith [this.1]; linarith [this.2]]
              refine le_trans (lintegral_mono_set hSsub) ?_
              refine lintegral_mono (fun S_bot => ?_)
              refine le_trans (lintegral_mono_set hTsub) ?_
              refine lintegral_mono (fun T' => ?_)
              refine le_of_eq ?_
              rw [hSc_carve]

end DLNFibre.DLN.RLCT
