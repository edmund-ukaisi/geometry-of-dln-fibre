import DLNFibre.DLN.RLCT.Validate.MatMulFibre
import DLNFibre.DLN.RLCT.Validate.RouteM4422
import DLNFibre.DLN.RLCT.Foundations.S1SmoothBlock

/-!
# `RouteM4422Hfin` — the `(4,4,2,2)` upper-bound finiteness (the hfin atom, S2-FREE)

The `(4,4,2,2)` instance of the hfin upper bound: for `c' < ½·minAdm M4422 = 2`,

    ∫⁻_{routeMBaseNbhd M4422} |routeMCore M4422 x|^{−c'} < ⊤.

This is the `cover_le` premise of `routeMLayerCover_of_atoms` for `M = (4,4,2,2)`, the companion of the
banked box-divergence atom `routeM4422_box_diverges` (the lower bound, `RouteM4422.lean`).

## The route (Codex-steered iterated fibre, thread 29; NOT the rank-stratified recursion)

`routeMCore M4422 x = frobSq (A0·A1·A2)` (`A0 : 4×4`, `A1 : 4×2`, `A2 : 2×2`), the 28 free flat
coords over the box `(−1,1)^28`. Tonelli-integrate the fibres outside-in:

  ∫_{A2}∫_{A1}∫_{A0} frobSq(A0·A1·A2)^{−c'}
    ≤ C0 · ∫_{A2}∫_{A1} frobSq(A1·A2)^{−c'}      [`fibre_lintegral_mul_le`, X = A0, Y = A1·A2, p=4]
    ≤ C0·C1 · ∫_{A2} frobSq(A2)^{−c'}            [`fibre_lintegral_mul_le`, X = A1, Y = A2,   p=4]
    < ⊤                                          [`sumSqND_box_lt_top`, A2 a 4-dim Morse block, c'<2]

Each fibre bound's constant `C0, C1` is `Y`-independent and finite (`fibreConst`); the threshold is
`p/2 = 2` at every step (`p = 4` rows in each layer's left factor). S2-FREE: only the matrix-product
fibre engine + the radial Morse terminal (`radial_ball_iff`), no `monomial_rlct`.

## STATUS — CLOSED (sorry-free, S2-free)

`routeMCore_M4422_threshold_lt_top` is now PROVED sorry-free, axiom-clean
(`#print axioms = [propext, Classical.choice, Quot.sound]`, NO `monomial_rlct` — S2-FREE). The whole
analytic engine is banked **sorry-free and S2-free**: the fibre lemma `fibre_lintegral_mul_le`, the
radial-Morse terminal `radial_morse_dominates_lt_top`/`sumSqND_box_lt_top`, the A2 leaf
`frobSq22_box_lt_top`, and the assembled 3-fold iterated fibre `triple_fibre_lt_top` (`MatMulFibre`,
`S1RadialMorse`). The connecting plumbing — the measure-preserving identification of `routeMCore M4422`
over `(−1,1)^28` with `triple_fibre_lt_top` — is the `eParams4422`/`paramsEquivFlat` reshape below
(`piFinSuccAbove`/`piUnique` layer split + the open-⊆-closed box monotone bound + the `c' = 0` trivial
split), riding the banked `prod_M4422_eq_rmatMul` + `dlnLoss_M4422_eq_frobSq` product identities.
-/

namespace DLNFibre.DLN.RLCT

open MeasureTheory
open scoped ENNReal BigOperators

/-! ## The `Params M4422` ↔ triple-matrix bridge (the loss as a matrix-product Frobenius square) -/

/-- `dlnLoss M4422 0 A = frobSq (prod M4422 A)` (the loss at target `0` is the squared Frobenius norm
of the layer product). -/
theorem dlnLoss_M4422_eq_frobSq (A : Params M4422) :
    dlnLoss M4422 0 A = frobSq (prod M4422 A) := by
  unfold dlnLoss frobSq
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  simp only [Matrix.sub_apply, Matrix.zero_apply, sub_zero]

/-- The layer product `prod M4422 A` as the iterated raw matrix product `rmatMul (rmatMul A₀ A₁) A₂`
(entrywise; associativity of the three-factor product, via `prod_three_layer4422`). -/
theorem prod_M4422_eq_rmatMul (A : Params M4422) :
    (fun i j => prod M4422 A i j)
      = rmatMul (rmatMul (fun i k => A 0 i k) (fun k k2 => A 1 k k2)) (fun k2 j => A 2 k2 j) := by
  funext i j
  rw [prod_three_layer4422 M4422 A i j]
  unfold rmatMul
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun k2 _ => ?_)
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl (fun k1 _ => ?_)
  ring

/-- **The triple-matrix iterated-fibre finiteness** `∫⁻_{A2}∫_{A1}∫_{A0} frobSq(A0·A1·A2)^{−c'} < ⊤`
for `0 < c' < 2`, each layer box `[−1,1]`. The iterated-fibre core: apply `fibre_lintegral_mul_le`
to the A0-fibre (`Y = A1·A2`, p=4), then the A1-fibre (`Y = A2`, p=4), terminating at the A2 4-dim
Morse leaf (`sumSqND_box_lt_top`). All S2-free; the constants are `Y`-independent. -/
theorem triple_fibre_lt_top (c' : ℝ) (hc0 : 0 < c') (hc' : c' < 2) :
    ∫⁻ A2 in matBox 2 2 1, ∫⁻ A1 in matBox 4 2 1, ∫⁻ A0 in matBox 4 4 1,
      ENNReal.ofReal ((frobSq (rmatMul (rmatMul A0 A1) A2)) ^ (-c')) < ⊤ := by
  -- A0-fibre: ∫_{A0} frobSq((A0·A1)·A2)^{−c'} ≤ C0·frobSq(A1·A2)^{−c'} (X=A0, Y=A1·A2, p=4,n=4,q=2)
  have hc2 : c' < (4 : ℕ) / 2 := by norm_num; linarith
  have hstep0 : ∀ (A1 : Fin 4 → Fin 2 → ℝ) (A2 : Fin 2 → Fin 2 → ℝ),
      ∫⁻ A0 in matBox 4 4 1, ENNReal.ofReal ((frobSq (rmatMul (rmatMul A0 A1) A2)) ^ (-c'))
        ≤ fibreConst 4 4 2 1 c' * ENNReal.ofReal ((frobSq (rmatMul A1 A2)) ^ (-c')) := by
    intro A1 A2
    -- rmatMul (rmatMul A0 A1) A2 = rmatMul A0 (rmatMul A1 A2) (associativity)
    have hassoc : ∀ A0 : Fin 4 → Fin 4 → ℝ,
        rmatMul (rmatMul A0 A1) A2 = rmatMul A0 (rmatMul A1 A2) := by
      intro A0; funext i j
      unfold rmatMul
      simp only [Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun k2 _ => Finset.sum_congr rfl (fun k1 _ => by ring))
    calc ∫⁻ A0 in matBox 4 4 1, ENNReal.ofReal ((frobSq (rmatMul (rmatMul A0 A1) A2)) ^ (-c'))
        = ∫⁻ A0 in matBox 4 4 1, ENNReal.ofReal ((frobSq (rmatMul A0 (rmatMul A1 A2))) ^ (-c')) := by
          refine setLIntegral_congr_fun (matBox_measurableSet _ _ _) (fun A0 _ => ?_)
          rw [hassoc A0]
      _ ≤ fibreConst 4 4 2 1 c' * ENNReal.ofReal ((frobSq (rmatMul A1 A2)) ^ (-c')) :=
          fibre_lintegral_mul_le (by norm_num) (by norm_num) (by norm_num) 1 one_pos c' hc0 hc2
            (rmatMul A1 A2)
  -- A1-fibre: ∫_{A1} frobSq(A1·A2)^{−c'} ≤ C1·frobSq(A2)^{−c'} (X=A1, Y=A2, p=4,n=2,q=2)
  have hstep1 : ∀ (A2 : Fin 2 → Fin 2 → ℝ),
      ∫⁻ A1 in matBox 4 2 1, ENNReal.ofReal ((frobSq (rmatMul A1 A2)) ^ (-c'))
        ≤ fibreConst 4 2 2 1 c' * ENNReal.ofReal ((frobSq A2) ^ (-c')) := by
    intro A2
    exact fibre_lintegral_mul_le (by norm_num) (by norm_num) (by norm_num) 1 one_pos c' hc0 hc2 A2
  -- A2 leaf: ∫_{A2} frobSq(A2)^{−c'} < ⊤ (4-dim Morse, c' < 2 = 4/2)
  have hmeasA0 : ∀ (A1 : Fin 4 → Fin 2 → ℝ) (A2 : Fin 2 → Fin 2 → ℝ),
      Measurable (fun A0 : Fin 4 → Fin 4 → ℝ =>
        ENNReal.ofReal ((frobSq (rmatMul (rmatMul A0 A1) A2)) ^ (-c'))) := by
    intro A1 A2
    apply ENNReal.measurable_ofReal.comp
    apply Measurable.comp (g := fun t : ℝ => t ^ (-c')) (by fun_prop)
    unfold frobSq rmatMul; fun_prop
  have hmeasA1 : ∀ (A2 : Fin 2 → Fin 2 → ℝ),
      Measurable (fun A1 : Fin 4 → Fin 2 → ℝ =>
        ENNReal.ofReal ((frobSq (rmatMul A1 A2)) ^ (-c'))) := by
    intro A2
    apply ENNReal.measurable_ofReal.comp
    apply Measurable.comp (g := fun t : ℝ => t ^ (-c')) (by fun_prop)
    unfold frobSq rmatMul; fun_prop
  -- chain the three bounds via monotonicity of the inner integrals
  calc ∫⁻ A2 in matBox 2 2 1, ∫⁻ A1 in matBox 4 2 1, ∫⁻ A0 in matBox 4 4 1,
          ENNReal.ofReal ((frobSq (rmatMul (rmatMul A0 A1) A2)) ^ (-c'))
      ≤ ∫⁻ A2 in matBox 2 2 1, ∫⁻ A1 in matBox 4 2 1,
          fibreConst 4 4 2 1 c' * ENNReal.ofReal ((frobSq (rmatMul A1 A2)) ^ (-c')) := by
        refine lintegral_mono (fun A2 => lintegral_mono (fun A1 => hstep0 A1 A2))
    _ = fibreConst 4 4 2 1 c' * ∫⁻ A2 in matBox 2 2 1, ∫⁻ A1 in matBox 4 2 1,
          ENNReal.ofReal ((frobSq (rmatMul A1 A2)) ^ (-c')) := by
        rw [← lintegral_const_mul' _ _ (fibreConst_ne_top 4 4 2 1 c' one_pos hc2 (by norm_num) (by norm_num))]
        refine setLIntegral_congr_fun (matBox_measurableSet _ _ _) (fun A2 _ => ?_)
        rw [lintegral_const_mul' _ _ (fibreConst_ne_top 4 4 2 1 c' one_pos hc2 (by norm_num) (by norm_num))]
    _ ≤ fibreConst 4 4 2 1 c' * ∫⁻ A2 in matBox 2 2 1,
          fibreConst 4 2 2 1 c' * ENNReal.ofReal ((frobSq A2) ^ (-c')) := by
        refine mul_le_mul_left' (lintegral_mono (fun A2 => hstep1 A2)) _
    _ = fibreConst 4 4 2 1 c' * fibreConst 4 2 2 1 c'
          * ∫⁻ A2 in matBox 2 2 1, ENNReal.ofReal ((frobSq A2) ^ (-c')) := by
        rw [lintegral_const_mul' _ _
          (fibreConst_ne_top 4 2 2 1 c' one_pos hc2 (by norm_num) (by norm_num)), mul_assoc]
    _ < ⊤ := by
        apply ENNReal.mul_lt_top (ENNReal.mul_lt_top
          (fibreConst_lt_top 4 4 2 1 c' one_pos hc2 (by norm_num) (by norm_num))
          (fibreConst_lt_top 4 2 2 1 c' one_pos hc2 (by norm_num) (by norm_num)))
        -- the A2 leaf: frobSq A2 = ∑_{k2 j} (A2 k2 j)² is a 4-dim sum of squares; finite for c' < 2
        exact frobSq22_box_lt_top 1 one_pos c' hc'

/-! ## The `Params M4422` ↔ triple-matrix-box reshape (the bridge to `triple_fibre_lt_top`)

The connecting plumbing identifying the flat-box integral of `routeMCore M4422` with the iterated
matrix-box integral `triple_fibre_lt_top`. The flat box `(−1,1)^28` is dominated by the closed cube box
`[−1,1]^28`, transported through `paramsEquivFlat` (MP) to the `Params M4422` box, then split into the
three per-layer matrix boxes via `eParams4422` (an MP `piFinSuccAbove`/`piUnique` reshape) — peeling the
layers in the order `(A2, A1, A0)` to match `triple_fibre_lt_top`'s `∫_{A2}∫_{A1}∫_{A0}`. -/

/-- The flat decode `paramsEquivFlat H A (equivFin idx) = A idx.1.1 idx.1.2 idx.2` — a flat coordinate
reads back the layer matrix entry. (Re-derived locally; the `arrowCongr'`/`piCurry`/`Sigma.uncurry`
unfold.) -/
theorem paramsEquivFlat_decode {L : ℕ} (H : Fin (L + 1) → ℕ) (A : Params H) (idx : FlatIdx H) :
    paramsEquivFlat H A (Fintype.equivFin (FlatIdx H) idx) = A idx.1.1 idx.1.2 idx.2 := by
  unfold paramsEquivFlat
  erw [MeasurableEquiv.trans_apply, MeasurableEquiv.trans_apply]
  simp only [MeasurableEquiv.coe_piCurry_symm]
  erw [Equiv.arrowCongr_apply]
  simp only [Function.comp_apply]
  erw [Equiv.symm_apply_apply]
  rfl

/-- The `Fin 2` tail family after peeling layer `2` (the layers `0,1` fibers, in index order). -/
abbrev TailFam4422 : Fin 2 → Type :=
  fun s : Fin 2 => Fin (M4422 ((2 : Fin 3).succAbove s).castSucc) →
    Fin (M4422 ((2 : Fin 3).succAbove s).succ) → ℝ

/-- The `Fin 1` tail-tail family after peeling index `1` of the `Fin 2` tail (the layer-`0` fiber). -/
abbrev TailTailFam4422 : Fin 1 → Type := fun s : Fin 1 => TailFam4422 ((1 : Fin 2).succAbove s)

/-- The tail reshape `(∀ s : Fin 2, layer fibers 0,1) ≃ᵐ (A1 × A0)` — peel index `1` (A1) then collapse
the singleton `Fin 1` tail (A0) via `piUnique`. -/
noncomputable def eTail4422 :
    (∀ s : Fin 2, TailFam4422 s) ≃ᵐ (Fin 4 → Fin 2 → ℝ) × (Fin 4 → Fin 4 → ℝ) :=
  (MeasurableEquiv.piFinSuccAbove TailFam4422 1).trans
    (MeasurableEquiv.prodCongr (MeasurableEquiv.refl _) (MeasurableEquiv.piUnique TailTailFam4422))

theorem measurePreserving_eTail4422 :
    MeasurePreserving eTail4422 (volume : Measure (∀ s : Fin 2, TailFam4422 s)) volume := by
  unfold eTail4422
  refine (volume_preserving_piFinSuccAbove TailFam4422 1).trans ?_
  have hp := (MeasurePreserving.id (volume : Measure (Fin 4 → Fin 2 → ℝ))).prod
    (volume_preserving_piUnique TailTailFam4422)
  rw [show (volume : Measure ((Fin 4 → Fin 2 → ℝ) × (Fin 4 → Fin 4 → ℝ)))
    = volume.prod volume from rfl]
  exact hp

/-- **The `Params M4422` split into the three layer matrix boxes, in `(A2, A1, A0)` order.** Peel layer
`2` (A2) then the tail into (A1, A0) — the order matching `triple_fibre_lt_top`. An MP reshape, with
components `(eParams4422 A).1 = A 2`, `.2.1 = A 1`, `.2.2 = A 0` (all definitional). -/
noncomputable def eParams4422 :
    Params M4422 ≃ᵐ (Fin 2 → Fin 2 → ℝ) × ((Fin 4 → Fin 2 → ℝ) × (Fin 4 → Fin 4 → ℝ)) :=
  (MeasurableEquiv.piFinSuccAbove
      (fun s : Fin 3 => Fin (M4422 s.castSucc) → Fin (M4422 s.succ) → ℝ) 2).trans
    (MeasurableEquiv.prodCongr (MeasurableEquiv.refl _) eTail4422)

theorem measurePreserving_eParams4422 :
    MeasurePreserving eParams4422 (volume : Measure (Params M4422)) volume := by
  unfold eParams4422
  refine (volume_preserving_piFinSuccAbove _ 2).trans ?_
  have hp := (MeasurePreserving.id (volume : Measure (Fin 2 → Fin 2 → ℝ))).prod
    measurePreserving_eTail4422
  rw [show (volume : Measure ((Fin 2 → Fin 2 → ℝ) × ((Fin 4 → Fin 2 → ℝ) × (Fin 4 → Fin 4 → ℝ))))
    = volume.prod volume from rfl]
  exact hp

/-- The `Params M4422` box: all matrix entries in `[−1,1]` (the image of the closed flat cube box). -/
def paramsBox4422 : Set (Params M4422) := {A | ∀ s i j, A s i j ∈ Set.Icc (-1 : ℝ) 1}

/-- `eParams4422 ⁻¹' (matBox A2 ×ˢ matBox A1 ×ˢ matBox A0) = paramsBox4422` (the three layer boxes pull
back to the all-entries-bounded `Params` box; `fin_cases` on the layer index). -/
theorem eParams4422_preimage_box :
    eParams4422 ⁻¹' (matBox 2 2 1 ×ˢ (matBox 4 2 1 ×ˢ matBox 4 4 1)) = paramsBox4422 := by
  ext A
  simp only [Set.mem_preimage, Set.mem_prod, matBox, paramsBox4422, Set.mem_setOf_eq]
  constructor
  · rintro ⟨h2, h1, h0⟩ s i j
    fin_cases s
    · exact h0 i j
    · exact h1 i j
    · exact h2 i j
  · intro h
    exact ⟨fun i j => h 2 i j, fun i j => h 1 i j, fun i j => h 0 i j⟩

/-- `paramsEquivFlat M4422 ⁻¹' (cubeBox 28 1) = paramsBox4422` (the closed flat cube box pulls back to
the all-entries-bounded `Params` box; the flat decode `paramsEquivFlat_decode` ranges over all entries). -/
theorem paramsEquivFlat_preimage_box4422 :
    paramsEquivFlat M4422 ⁻¹' (cubeBox (flatDim M4422) 1) = paramsBox4422 := by
  ext A
  simp only [Set.mem_preimage, cubeBox, paramsBox4422, Set.mem_pi, Set.mem_univ, true_implies,
    Set.mem_setOf_eq]
  constructor
  · intro h s i j
    have := h (Fintype.equivFin (FlatIdx M4422) ⟨⟨s, i⟩, j⟩)
    rwa [paramsEquivFlat_decode M4422 A ⟨⟨s, i⟩, j⟩] at this
  · intro h k
    obtain ⟨idx, rfl⟩ := (Fintype.equivFin (FlatIdx M4422)).surjective k
    rw [paramsEquivFlat_decode M4422 A idx]
    exact h idx.1.1 idx.1.2 idx.2

theorem measurableSet_paramsBox4422 : MeasurableSet paramsBox4422 := by
  rw [← paramsEquivFlat_preimage_box4422]
  exact ((by rw [cubeBox]; exact MeasurableSet.univ_pi (fun _ => measurableSet_Icc)) :
    MeasurableSet (cubeBox (flatDim M4422) 1)).preimage (paramsEquivFlat M4422).measurable

/-- The integrand identity: `frobSq (prod M4422 A) = frobSq (rmatMul (rmatMul A0 A1) A2)` read off the
`eParams4422` components (`A0,A1,A2` are `(eParams4422 A).2.2, .2.1, .1`). Via `prod_M4422_eq_rmatMul`. -/
theorem frobSq_prod_eq_eParams4422 (A : Params M4422) :
    frobSq (prod M4422 A)
      = frobSq (rmatMul (rmatMul (eParams4422 A).2.2 (eParams4422 A).2.1) (eParams4422 A).1) := by
  change frobSq (prod M4422 A) = frobSq (rmatMul (rmatMul (A 0) (A 1)) (A 2))
  have h : (prod M4422 A : Fin 4 → Fin 2 → ℝ) = rmatMul (rmatMul (A 0) (A 1)) (A 2) :=
    prod_M4422_eq_rmatMul A
  unfold frobSq
  rw [h]
  rfl

/-- `routeMCore M4422` is nonnegative (the loss is a squared Frobenius norm). -/
theorem routeMCore_M4422_nonneg (x : Fin (routeMAmbient M4422) → ℝ) : 0 ≤ routeMCore M4422 x := by
  rw [routeMCore, dlnLoss_M4422_eq_frobSq]; exact frobSq_nonneg _

/-- The product integrand `(frobSq (rmatMul (rmatMul A0 A1) A2))^{−c'}` is measurable. -/
theorem measurable_triple_integrand4422 (c' : ℝ) :
    Measurable (fun p : (Fin 2 → Fin 2 → ℝ) × ((Fin 4 → Fin 2 → ℝ) × (Fin 4 → Fin 4 → ℝ)) =>
      ENNReal.ofReal ((frobSq (rmatMul (rmatMul p.2.2 p.2.1) p.1)) ^ (-c'))) := by
  apply ENNReal.measurable_ofReal.comp
  apply Measurable.comp (g := fun t : ℝ => t ^ (-c')) (by fun_prop)
  unfold frobSq rmatMul; fun_prop

/-- **The `(4,4,2,2)` hfin upper bound (S2-FREE).** For `c' < ½·minAdm M4422 = 2`,
`∫⁻_{routeMBaseNbhd M4422} |routeMCore M4422 x|^{−c'} < ⊤`. The companion of the banked box-divergence
atom `routeM4422_box_diverges`; together they discharge the two analytic atoms of
`routeMLayerCover_of_atoms` for `M = (4,4,2,2)` (this side via the iterated matrix-product fibre engine
`fibre_lintegral_mul_le`, S2-free).

The reshape (`eParams4422`/`paramsEquivFlat`, all measure-preserving): dominate the open flat box by the
closed cube `[−1,1]^28`, transport through `paramsEquivFlat` (MP) to the `Params M4422` box, split into
the three per-layer matrix boxes (in `(A2,A1,A0)` order), Tonelli to the iterated integral, and apply
`triple_fibre_lt_top`. The `c' = 0` case is the trivial constant-`1` integral over the finite-volume box.
S2-FREE: only the matrix-product fibre engine + the radial Morse terminal (`radial_ball_iff`); no
`monomial_rlct`. -/
theorem routeMCore_M4422_threshold_lt_top (c' : NNReal)
    (hc' : (c' : ℝ) < (minAdm M4422 : ℝ) / 2) :
    ∫⁻ x in routeMBaseNbhd M4422, ENNReal.ofReal (|routeMCore M4422 x| ^ (-(c' : ℝ))) < ⊤ := by
  rw [minAdm_M4422] at hc'
  have hc2 : (c' : ℝ) < 2 := by linarith
  have hopen_sub : flatOpenBox (routeMAmbient M4422) ⊆ cubeBox (routeMAmbient M4422) 1 := by
    intro x hx i _
    have := hx i (Set.mem_univ i); rw [Set.mem_Ioo] at this
    rw [Set.mem_Icc]; exact ⟨le_of_lt this.1, le_of_lt this.2⟩
  rcases eq_or_lt_of_le (c'.2 : (0 : ℝ) ≤ (c' : ℝ)) with hc0 | hc0
  · -- c' = 0: integrand is (·)^0 = 1, integral = volume(box) < ⊤.
    have hzero : (c' : ℝ) = 0 := hc0.symm
    have hone : ∀ x, ENNReal.ofReal (|routeMCore M4422 x| ^ (-(c' : ℝ))) = 1 := by
      intro x; rw [hzero]; simp [Real.rpow_zero]
    simp only [hone]
    rw [setLIntegral_const]
    refine ENNReal.mul_lt_top ENNReal.one_lt_top ?_
    rw [routeMBaseNbhd]
    refine lt_of_le_of_lt (measure_mono hopen_sub) ?_
    exact (isCompact_univ_pi (fun _ => isCompact_Icc)).measure_lt_top
  · -- 0 < c' < 2: the full reshape chain.
    -- Step 1: |routeMCore| = routeMCore, dominate the open box by the closed cube box.
    have hbound : ∫⁻ x in routeMBaseNbhd M4422, ENNReal.ofReal (|routeMCore M4422 x| ^ (-(c' : ℝ)))
        ≤ ∫⁻ x in cubeBox (routeMAmbient M4422) 1,
            ENNReal.ofReal (routeMCore M4422 x ^ (-(c' : ℝ))) := by
      rw [routeMBaseNbhd]
      refine le_trans (lintegral_mono_set hopen_sub) (le_of_eq ?_)
      refine setLIntegral_congr_fun (by
        rw [cubeBox]; exact MeasurableSet.univ_pi (fun _ => measurableSet_Icc)) (fun x _ => ?_)
      rw [abs_of_nonneg (routeMCore_M4422_nonneg x)]
    refine lt_of_le_of_lt hbound ?_
    -- Step 2: transport the closed cube box via paramsEquivFlat (MP) to paramsBox4422.
    have hcore : ∀ A : Params M4422,
        routeMCore M4422 (paramsEquivFlat M4422 A) = frobSq (prod M4422 A) := by
      intro A; rw [congrFun (routeMCore_comp_paramsEquivFlat M4422) A, dlnLoss_M4422_eq_frobSq]
    have hmpF := measurePreserving_paramsEquivFlat M4422
    have hstep2 : ∫⁻ x in cubeBox (routeMAmbient M4422) 1,
          ENNReal.ofReal (routeMCore M4422 x ^ (-(c' : ℝ)))
        = ∫⁻ A in paramsBox4422, ENNReal.ofReal (frobSq (prod M4422 A) ^ (-(c' : ℝ))) := by
      have hpre := hmpF.setLIntegral_comp_preimage_emb
        (MeasurableEquiv.measurableEmbedding (paramsEquivFlat M4422))
        (fun x => ENNReal.ofReal (routeMCore M4422 x ^ (-(c' : ℝ))))
        (cubeBox (routeMAmbient M4422) 1)
      calc ∫⁻ x in cubeBox (routeMAmbient M4422) 1,
              ENNReal.ofReal (routeMCore M4422 x ^ (-(c' : ℝ)))
          = ∫⁻ A in (paramsEquivFlat M4422) ⁻¹' cubeBox (routeMAmbient M4422) 1,
              ENNReal.ofReal (routeMCore M4422 (paramsEquivFlat M4422 A) ^ (-(c' : ℝ))) := hpre.symm
        _ = ∫⁻ A in paramsBox4422,
              ENNReal.ofReal (frobSq (prod M4422 A) ^ (-(c' : ℝ))) := by
            rw [show (paramsEquivFlat M4422) ⁻¹' cubeBox (routeMAmbient M4422) 1 = paramsBox4422
              from paramsEquivFlat_preimage_box4422]
            refine setLIntegral_congr_fun measurableSet_paramsBox4422 (fun A _ => ?_)
            rw [hcore A]
    rw [hstep2]
    -- Step 3: transport paramsBox4422 via eParams4422 (MP) to the three layer matrix boxes.
    have hmpP := measurePreserving_eParams4422
    have hstep3 : ∫⁻ A in paramsBox4422, ENNReal.ofReal (frobSq (prod M4422 A) ^ (-(c' : ℝ)))
        = ∫⁻ p in (matBox 2 2 1 ×ˢ (matBox 4 2 1 ×ˢ matBox 4 4 1)),
            ENNReal.ofReal ((frobSq (rmatMul (rmatMul p.2.2 p.2.1) p.1)) ^ (-(c' : ℝ))) := by
      have hpre := hmpP.setLIntegral_comp_preimage_emb
        (MeasurableEquiv.measurableEmbedding eParams4422)
        (fun p : (Fin 2 → Fin 2 → ℝ) × ((Fin 4 → Fin 2 → ℝ) × (Fin 4 → Fin 4 → ℝ)) =>
          ENNReal.ofReal ((frobSq (rmatMul (rmatMul p.2.2 p.2.1) p.1)) ^ (-(c' : ℝ))))
        (matBox 2 2 1 ×ˢ (matBox 4 2 1 ×ˢ matBox 4 4 1))
      calc ∫⁻ A in paramsBox4422, ENNReal.ofReal (frobSq (prod M4422 A) ^ (-(c' : ℝ)))
          = ∫⁻ A in eParams4422 ⁻¹' (matBox 2 2 1 ×ˢ (matBox 4 2 1 ×ˢ matBox 4 4 1)),
              ENNReal.ofReal ((frobSq (rmatMul (rmatMul (eParams4422 A).2.2 (eParams4422 A).2.1)
                (eParams4422 A).1)) ^ (-(c' : ℝ))) := by
            rw [eParams4422_preimage_box]
            refine setLIntegral_congr_fun measurableSet_paramsBox4422 (fun A _ => ?_)
            rw [frobSq_prod_eq_eParams4422 A]
        _ = ∫⁻ p in (matBox 2 2 1 ×ˢ (matBox 4 2 1 ×ˢ matBox 4 4 1)),
              ENNReal.ofReal ((frobSq (rmatMul (rmatMul p.2.2 p.2.1) p.1)) ^ (-(c' : ℝ))) := hpre
    rw [hstep3]
    -- Step 4: Tonelli twice into the iterated integral matching triple_fibre_lt_top.
    rw [Measure.volume_eq_prod (Fin 2 → Fin 2 → ℝ) ((Fin 4 → Fin 2 → ℝ) × (Fin 4 → Fin 4 → ℝ)),
      setLIntegral_prod _ (measurable_triple_integrand4422 (c' : ℝ)).aemeasurable]
    have hinner : ∀ A2 : Fin 2 → Fin 2 → ℝ,
        ∫⁻ p in (matBox 4 2 1 ×ˢ matBox 4 4 1),
          ENNReal.ofReal ((frobSq (rmatMul (rmatMul p.2 p.1) A2)) ^ (-(c' : ℝ)))
        = ∫⁻ A1 in matBox 4 2 1, ∫⁻ A0 in matBox 4 4 1,
            ENNReal.ofReal ((frobSq (rmatMul (rmatMul A0 A1) A2)) ^ (-(c' : ℝ))) := by
      intro A2
      have hmeas2 : Measurable (fun p : (Fin 4 → Fin 2 → ℝ) × (Fin 4 → Fin 4 → ℝ) =>
          ENNReal.ofReal ((frobSq (rmatMul (rmatMul p.2 p.1) A2)) ^ (-(c' : ℝ)))) := by
        apply ENNReal.measurable_ofReal.comp
        apply Measurable.comp (g := fun t : ℝ => t ^ (-(c' : ℝ))) (by fun_prop)
        unfold frobSq rmatMul; fun_prop
      rw [Measure.volume_eq_prod (Fin 4 → Fin 2 → ℝ) (Fin 4 → Fin 4 → ℝ),
        setLIntegral_prod _ hmeas2.aemeasurable]
    simp only [hinner]
    exact triple_fibre_lt_top (c' : ℝ) hc0 hc2

end DLNFibre.DLN.RLCT
