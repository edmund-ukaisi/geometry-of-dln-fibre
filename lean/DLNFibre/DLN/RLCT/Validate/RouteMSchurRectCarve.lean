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

end DLNFibre.DLN.RLCT
