import DLNFibre.DLN.Aoyagi.Corank2FoldedFamily334

/-!
# `DLN.Aoyagi.Corank2FoldedInj334` — the ainj leaf (`folded_hg_inj`) for the (3,3,4) V-lower

The `hg_inj` obligation of the folded-family headline (`Corank2OverVanishHeadline334`): the folded
chart `gFold c` is INJECTIVE off its critical set `excepFold c`, on the whole neighbourhood
`nbhdFold c = univ`. Cite-free, monument-free; built ON the `Corank2FoldedFamily334` foundation.

**Route.** `gFold c = pathMap [bb S1 p1, nativeChart1 p1, bb σC1 p2, bb σC2 p3, psiOf c]` (the
`abs_jacDet_gFlat` composite, folded with `psiOf c`), so `LeafChartWire.injOn_pathMap_off_critical`
reduces the composite injectivity to per-atom injectivity off each atom's own critical set:

* the three block blow-ups are injective off their pivot hyperplane `{w_p = 0}`
  (`injOn_blockBlowupMap`), which — since every centre has `card ≥ 2` — IS their critical set
  `{jacDet = 0} = {(w_p)^(card−1) = 0}` (`jacDet_blockBlowupMap` + `pow_eq_zero_iff`);
* the two shears `nativeChart1 p1` and `psiOf c` are GLOBALLY injective (shear ∘ coord-perm resp. a
  `conjChart` of an injective `blockShear`), so injective off ANY set a fortiori.

The composite's non-injective locus lands in `{jacDet (gFold c) = 0}`, which the foundation's
`folded_jac_collapse` identifies with `excepFold c` (`|jacDet (gFold c)| = jacWeight (jacExpFold c)`
gives `{jacDet = 0} ⊆ excepFold`), so a `.mono` down closes the headline hole.
-/

open MeasureTheory Set Filter Topology Metric RLCT
open DLNFibre.Core.Aoyagi
open DLNFibre.DLN.Aoyagi.NativeFan334
open DLNFibre.DLN.Aoyagi.NativeShear334
open DLNFibre.DLN.Aoyagi.NativePerm334
open DLNFibre.DLN.Aoyagi.GeneralGeoAtlas

namespace DLNFibre.DLN.Aoyagi.OverVanishHeadline334

/-! ## §1 — global injectivity of the two shear atoms -/

/-- **Coordinate precomposition by a permutation is injective** (`w ↦ w ∘ σ`; the inverse reindex by
`σ⁻¹` recovers `w`). -/
private theorem injective_reindex (σ : Equiv.Perm (Fin 21)) :
    Function.Injective (fun w : Fin 21 → ℝ ↦ fun k ↦ w (σ k)) := by
  intro w w' h
  funext j
  have hj := congrFun h (σ.symm j)
  simpa [Equiv.apply_symm_apply] using hj

/-- **`conjChart σ` preserves injectivity.** `conjChart σ H = R_{σ⁻¹} ∘ H ∘ R_σ` with the two
coordinate reindexings bijective (`injective_reindex`). -/
private theorem injective_conjChart (σ : Equiv.Perm (Fin 21))
    {H : (Fin 21 → ℝ) → (Fin 21 → ℝ)} (hH : Function.Injective H) :
    Function.Injective (OverVanishTransport334.conjChart σ H) :=
  (injective_reindex σ.symm).comp (hH.comp (injective_reindex σ))

/-- Every base-type straightening `psi` is injective (each per-type `psiCanon = blockShear phiCanon`
with the kept-coordinate data `phiCanon_keep`/`phiCanon_read`, so `injective_blockShear`). -/
private theorem bundleOf_psi_injective (q r : Fin 21) : Function.Injective (bundleOf q r).psi := by
  simp only [bundleOf]
  split_ifs <;>
    first
      | exact injective_blockShear _ _ OverVanishCanon334.phiCanon_keep
          OverVanishCanon334.phiCanon_read
      | exact injective_blockShear _ _ OverVanishA_20_1_5.phiCanon_keep
          OverVanishA_20_1_5.phiCanon_read
      | exact injective_blockShear _ _ OverVanishA_20_1_6.phiCanon_keep
          OverVanishA_20_1_6.phiCanon_read
      | exact injective_blockShear _ _ OverVanishA_20_1_7.phiCanon_keep
          OverVanishA_20_1_7.phiCanon_read
      | exact injective_blockShear _ _ OverVanishA_20_5_1.phiCanon_keep
          OverVanishA_20_5_1.phiCanon_read
      | exact injective_blockShear _ _ OverVanishA_20_5_5.phiCanon_keep
          OverVanishA_20_5_5.phiCanon_read
      | exact injective_blockShear _ _ OverVanishA_20_5_6.phiCanon_keep
          OverVanishA_20_5_6.phiCanon_read
      | exact injective_blockShear _ _ OverVanishA_20_5_7.phiCanon_keep
          OverVanishA_20_5_7.phiCanon_read
      | exact injective_blockShear _ _ OverVanishB_20_6_1.phiCanon_keep
          OverVanishB_20_6_1.phiCanon_read
      | exact injective_blockShear _ _ OverVanishB_20_6_5.phiCanon_keep
          OverVanishB_20_6_5.phiCanon_read
      | exact injective_blockShear _ _ OverVanishB_20_6_6.phiCanon_keep
          OverVanishB_20_6_6.phiCanon_read
      | exact injective_blockShear _ _ OverVanishB_20_6_7.phiCanon_keep
          OverVanishB_20_6_7.phiCanon_read
      | exact injective_blockShear _ _ OverVanishB_20_7_1.phiCanon_keep
          OverVanishB_20_7_1.phiCanon_read
      | exact injective_blockShear _ _ OverVanishB_20_7_5.phiCanon_keep
          OverVanishB_20_7_5.phiCanon_read
      | exact injective_blockShear _ _ OverVanishB_20_7_6.phiCanon_keep
          OverVanishB_20_7_6.phiCanon_read
      | exact injective_blockShear _ _ OverVanishB_20_7_7.phiCanon_keep
          OverVanishB_20_7_7.phiCanon_read

/-- **The folding shear `psiOf c` is injective** (identity on clean; `conjChart` of an injective
per-type straightening on over-vanishing). -/
private theorem injective_psiOf (c : Fin numCharts) : Function.Injective (psiOf c) := by
  unfold psiOf
  split_ifs with h
  · exact Function.injective_id
  · exact injective_conjChart _ (bundleOf_psi_injective (canonQ c) (canonR c))

/-- **The node-1 native shear is injective** at every dominant pivot (dispatch to the nine
`injective_P·`). -/
private theorem injective_nativeSel (p : Fin 21) (hp : p ∈ S1) :
    Function.Injective (nativeSel p) := by
  fin_cases hp <;> simp only [nativeSel, Fin.reduceEq, if_true, if_false] <;>
    first
      | exact injective_P0 | exact injective_P1 | exact injective_P2 | exact injective_P3
      | exact injective_P4 | exact injective_P5 | exact injective_P6 | exact injective_P7
      | exact injective_P20

/-- **The node-1 native permutation is injective** at every dominant pivot (coordinate
precomposition by the bijective `cpermS·`). -/
private theorem injective_nativePerm (p : Fin 21) (hp : p ∈ S1) :
    Function.Injective (nativePerm p) := by
  fin_cases hp <;> simp only [nativePerm, Fin.reduceEq, if_true, if_false] <;>
    first
      | exact injective_reindex cpermS0 | exact injective_reindex cpermS1
      | exact injective_reindex cpermS2 | exact injective_reindex cpermS3
      | exact injective_reindex cpermS4 | exact injective_reindex cpermS5
      | exact injective_reindex cpermS6 | exact injective_reindex cpermS7
      | exact injective_reindex cpermS20

/-- **The composite node-1 shear `nativeChart1 p` is injective** at every dominant pivot. -/
private theorem injective_nativeChart1 (p : Fin 21) (hp : p ∈ S1) :
    Function.Injective (nativeChart1 p) :=
  (injective_nativeSel p hp).comp (injective_nativePerm p hp)

/-! ## §2 — the block blow-up atom off its OWN critical set -/

/-- **The block blow-up is injective off its critical set** `{jacDet = 0}`. For a centre with
`2 ≤ |S|` this set equals the pivot hyperplane `{w_p = 0}` (`jacDet = (w_p)^(|S|−1)`,
`pow_eq_zero_iff`), where `injOn_blockBlowupMap` gives injectivity. -/
private theorem injOn_blockBlowupMap_off_critical {S : Finset (Fin 21)} {p : Fin 21}
    (hp : p ∈ S) (hcard : 2 ≤ S.card) :
    Set.InjOn (blockBlowupMap S p)
      (Set.univ \ {w : Fin 21 → ℝ | jacDet (blockBlowupMap S p) w = 0}) := by
  have hset : {w : Fin 21 → ℝ | jacDet (blockBlowupMap S p) w = 0} = {w | w p = 0} := by
    ext w
    simp only [Set.mem_setOf_eq]
    rw [jacDet_blockBlowupMap hp, pow_eq_zero_iff (by omega : S.card - 1 ≠ 0)]
  rw [hset]
  exact injOn_blockBlowupMap hp

/-! ## §3 — the ainj headline hole -/

/-- **`folded_hg_inj` — the folded chart is a.e.-injective off its critical set.** For every
leaf `c`, `gFold c` is injective on `nbhdFold c \ excepFold c`. Decomposes `gFold c` as a
`pathMap` of five atoms, folds their per-atom injectivity with `injOn_pathMap_off_critical`, and
`.mono`s the critical-set exclusion down onto `excepFold c` via `folded_jac_collapse`. -/
theorem folded_hg_inj : ∀ c, Set.InjOn (gFold c) (nbhdFold c \ excepFold c) := by
  intro c
  have hp1 : p1Of c ∈ S1 := (idxEquiv c).1.2
  have hp2 : p2Of c ∈ sigmaC1Fs (p1Of c) := (idxEquiv c).2.1.2
  have hp3 : p3Of c ∈ sigmaC2Fs (p1Of c) := (idxEquiv c).2.2.2
  -- the five-atom path presentation of `gFold c`.
  have hpath : gFold c = pathMap
      [blockBlowupMap S1 (p1Of c), nativeChart1 (p1Of c),
        blockBlowupMap (sigmaC1Fs (p1Of c)) (p2Of c),
        blockBlowupMap (sigmaC2Fs (p1Of c)) (p3Of c), psiOf c] := rfl
  -- injective off its own critical set, via the pathMap fold.
  have hkey : Set.InjOn (gFold c) (Set.univ \ {u | jacDet (gFold c) u = 0}) := by
    rw [hpath]
    refine injOn_pathMap_off_critical _ ?hdiff ?hinj
    case hdiff =>
      intro σ hσ
      fin_cases hσ
      · exact differentiable_blockBlowupMap _ _
      · exact nativeChart1_differentiable _
      · exact differentiable_blockBlowupMap _ _
      · exact differentiable_blockBlowupMap _ _
      · exact differentiable_psiOf c
    case hinj =>
      intro σ hσ
      fin_cases hσ
      · exact injOn_blockBlowupMap_off_critical hp1 (by rw [NativeJac334.S1_card]; norm_num)
      · exact (injective_nativeChart1 (p1Of c) hp1).injOn
      · exact injOn_blockBlowupMap_off_critical hp2 (by rw [NativeJac334.sigmaC1Fs_card]; norm_num)
      · exact injOn_blockBlowupMap_off_critical hp3 (by rw [NativeJac334.sigmaC2Fs_card]; norm_num)
      · exact (injective_psiOf c).injOn
  -- `.mono` down: `{jacDet (gFold c) = 0} ⊆ excepFold c` via the folded-Jacobian collapse.
  refine hkey.mono ?_
  unfold nbhdFold
  refine Set.diff_subset_diff_right ?_
  intro u hu
  have hcol := folded_jac_collapse c u
  have h0 : jacDet (gFold c) u = 0 := hu
  rw [h0, abs_zero] at hcol
  exact hcol.symm

end DLNFibre.DLN.Aoyagi.OverVanishHeadline334
