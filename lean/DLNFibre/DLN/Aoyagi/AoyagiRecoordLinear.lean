import DLNFibre.DLN.Aoyagi.CanonShear
import DLNFibre.DLN.Aoyagi.AoyagiCompLinear

/-!
# `DLN.Aoyagi.AoyagiRecoordLinear` — the recoord X-linearity of `N_p` on the deeper layer (SEAT-L3T3)

The faithful shear `canonNormalizationOf d s pv` (`N_p`) WRITES the deeper layer `sl = s.layer + 1`
(component (ii), the recoord `A_{S+1}·Q₁⁻¹`), degree-1-LINEAR in the layer-`(s.layer+1)` coordinates
with coefficients drawn from layer `s.layer` (per the `npivot-certificate`). This file exhibits the
`C`/`hlin`/`hC` inputs `AoyagiCompLinear.{affineOn,homogeneousDeg1On}_comp_of_linear` need at that layer,
so the homogeneity induction (`MultiAffineHomogWire`) and the slot descent (`MultiAffineStepWire`) can
push their per-layer grade across the layer-`(s.layer+1)` recoord (where the pre-`N_p` `…_comp_of_fixing`
no longer applies — the shear is not fixing there, it is linear).

The coefficient `recoordCoeff` reads `u` only through `readEntry d u s.layer …` (layer `s.layer`, OFF the
block `layerCoords d (s.layer+1)`), so it ignores that block — that is `hC`.
-/

open MeasureTheory Set
open DLNFibre.Core DLNFibre.Core.Aoyagi DLNFibre.DLN.RLCT DLNFibre.DLN.RLCT.Engine

namespace DLNFibre.DLN.Aoyagi

variable {N : ℕ}

/-- A `blockEntryFlat` value at layer `S` lands in `layerCoords d S`. -/
theorem blockEntryFlat_mem_layerCoords (d : Fin (N + 1) → ℕ) (S row col : ℕ) (fc : Fin (flatDim d))
    (h : blockEntryFlat d S row col = some fc) : fc ∈ layerCoords d S := by
  classical
  simp only [blockEntryFlat] at h
  split at h
  · rename_i hS
    split at h
    · rename_i hr
      split at h
      · rename_i hc
        have he := Option.some.inj h
        simp only [layerCoords, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨⟨⟨⟨S, hS⟩, ⟨row, hr⟩⟩, ⟨col, hc⟩⟩, rfl, he⟩
      · simp at h
    · simp at h
  · simp at h

/-- `readEntry` at layer `S` depends only on off-(layer `L`) coordinates, when `S ≠ L`: its unique
flat coord `blockEntryFlat d S row col` decodes to layer `S ≠ L`, hence lies outside `layerCoords d L`. -/
theorem readEntry_eq_of_agree_off (d : Fin (N + 1) → ℕ) (S L row col : ℕ) (hSL : S ≠ L)
    (u v : Fin (flatDim d) → ℝ) (hag : ∀ k, k ∉ layerCoords d L → u k = v k) :
    readEntry d u S row col = readEntry d v S row col := by
  classical
  simp only [readEntry]
  split
  · rename_i fc hfc
    refine hag fc (fun hmem => hSL ?_)
    rw [← decode_layer_of_mem_layerCoords d S fc (blockEntryFlat_mem_layerCoords d S row col fc hfc),
      decode_layer_of_mem_layerCoords d L fc hmem]
  · rfl

/-- The coefficient of the recoord X-linear form on layer `s.layer + 1`: the diagonal `[j=x]` plus the
recoord contribution (a sum over the layer-`(s.layer+1)` column index of layer-`s.layer` reads). The `u`
dependence is only through `readEntry d u s.layer …`, so it ignores `layerCoords d (s.layer+1)`. -/
noncomputable def recoordCoeff (d : Fin (N + 1) → ℕ) (s : ConState N) (pv : Fin (flatDim d))
    (hSN : s.layer + 1 < N) (u : Fin (flatDim d) → ℝ) (x j : Fin (flatDim d)) : ℝ :=
  (if j = x then 1 else 0) +
    if (((tupIdxEquiv d).symm x).2 : ℕ) = (((tupIdxEquiv d).symm pv).1.2 : ℕ) then
      ∑ i ∈ Finset.range (d (⟨s.layer + 1, hSN⟩ : Fin N).castSucc),
        if blockEntryFlat d (s.layer + 1) (((tupIdxEquiv d).symm x).1.2 : ℕ) i = some j
            ∧ i ≠ (((tupIdxEquiv d).symm x).2 : ℕ)
        then readEntry d u s.layer i (((tupIdxEquiv d).symm pv).2 : ℕ) else 0
    else 0

/-- **The recoord X-linearity of `N_p` on the deeper layer.** For `x ∈ layerCoords d (s.layer+1)` the
faithful shear `blockShear (canonNormalizationOf d s pv)` acts by a homogeneous-`X`-linear form
`∑_{j∈X} recoordCoeff · u_j`, with each coefficient ignoring `X = layerCoords d (s.layer+1)`. Feeds
`AoyagiCompLinear.{affineOn,homogeneousDeg1On}_comp_of_linear`. -/
theorem canonNorm_blockShear_linear_on_succLayer (d : Fin (N + 1) → ℕ) (s : ConState N)
    (pv : Fin (flatDim d)) (hSN : s.layer + 1 < N) :
    (∀ u, ∀ x ∈ layerCoords d (s.layer + 1),
        blockShear (canonNormalizationOf d s pv) u x
          = ∑ j ∈ layerCoords d (s.layer + 1), recoordCoeff d s pv hSN u x j * u j) ∧
      (∀ x ∈ layerCoords d (s.layer + 1), ∀ j ∈ layerCoords d (s.layer + 1),
        IgnoresCoords (fun u => recoordCoeff d s pv hSN u x j) (layerCoords d (s.layer + 1))
          Set.univ) := by
  classical
  refine ⟨?_, ?_⟩
  · -- hlin (Codex-drafted route: diagonal `sum_ite_eq'` + recoord `sum_comm`/`sum_ite_eq` reindex).
    -- Raw `(tupIdxEquiv d).symm …` / `⟨s.layer+1, hSN⟩` throughout so every term matches the def unfolds.
    intro u x hx
    have hlayNat : (((tupIdxEquiv d).symm x).1.1 : ℕ) = s.layer + 1 :=
      decode_layer_of_mem_layerCoords d (s.layer + 1) x hx
    have hlay : ((tupIdxEquiv d).symm x).1.1 = (⟨s.layer + 1, hSN⟩ : Fin N) :=
      Fin.ext (by simpa using hlayNat)
    have hfirst : ¬ ((((tupIdxEquiv d).symm x).1.1 : ℕ) = s.layer ∧
        (((tupIdxEquiv d).symm x).1.2 : ℕ) ≠ (((tupIdxEquiv d).symm pv).1.2 : ℕ) ∧
        (((tupIdxEquiv d).symm x).2 : ℕ) ≠ (((tupIdxEquiv d).symm pv).2 : ℕ) ∧
        s.cleared ≤ (((tupIdxEquiv d).symm x).1.2 : ℕ) ∧
        s.cleared ≤ (((tupIdxEquiv d).symm x).2 : ℕ)) := by intro h; omega
    have hrow : (((tupIdxEquiv d).symm x).1.2 : ℕ) < d (⟨s.layer + 1, hSN⟩ : Fin N).succ := by
      simpa only [hlay] using ((tupIdxEquiv d).symm x).1.2.isLt
    have hentry : ∀ i ∈ Finset.range (d (⟨s.layer + 1, hSN⟩ : Fin N).castSucc),
        ∃ fc : Fin (flatDim d),
          blockEntryFlat d (s.layer + 1) (((tupIdxEquiv d).symm x).1.2 : ℕ) i = some fc ∧
          fc ∈ layerCoords d (s.layer + 1) ∧
          readEntry d u (s.layer + 1) (((tupIdxEquiv d).symm x).1.2 : ℕ) i = u fc := by
      intro i hi
      have hcol : i < d (⟨s.layer + 1, hSN⟩ : Fin N).castSucc := Finset.mem_range.mp hi
      have hB : blockEntryFlat d (s.layer + 1) (((tupIdxEquiv d).symm x).1.2 : ℕ) i
          = some (tupIdxEquiv d ⟨⟨⟨s.layer + 1, hSN⟩, ⟨(((tupIdxEquiv d).symm x).1.2 : ℕ), hrow⟩⟩,
              ⟨i, hcol⟩⟩) := by
        simp only [blockEntryFlat, dif_pos hSN, dif_pos hrow, dif_pos hcol]
      exact ⟨_, hB, blockEntryFlat_mem_layerCoords d _ _ _ _ hB, by rw [readEntry, hB]⟩
    have hdelta : (∑ j ∈ layerCoords d (s.layer + 1), (if j = x then (1 : ℝ) else 0) * u j) = u x := by
      simp only [ite_mul, one_mul, zero_mul]
      rw [Finset.sum_ite_eq', if_pos hx]
    have hfiber : (∑ j ∈ layerCoords d (s.layer + 1),
        (∑ i ∈ Finset.range (d (⟨s.layer + 1, hSN⟩ : Fin N).castSucc),
          if blockEntryFlat d (s.layer + 1) (((tupIdxEquiv d).symm x).1.2 : ℕ) i = some j
              ∧ i ≠ (((tupIdxEquiv d).symm x).2 : ℕ)
          then readEntry d u s.layer i (((tupIdxEquiv d).symm pv).2 : ℕ) else 0) * u j) =
        ∑ i ∈ Finset.range (d (⟨s.layer + 1, hSN⟩ : Fin N).castSucc),
          if i = (((tupIdxEquiv d).symm x).2 : ℕ) then 0 else
            readEntry d u s.layer i (((tupIdxEquiv d).symm pv).2 : ℕ)
              * readEntry d u (s.layer + 1) (((tupIdxEquiv d).symm x).1.2 : ℕ) i := by
      rw [Finset.sum_congr rfl (fun j _ => Finset.sum_mul _ _ _), Finset.sum_comm]
      refine Finset.sum_congr rfl (fun i hi => ?_)
      by_cases hic : i = (((tupIdxEquiv d).symm x).2 : ℕ)
      · simp only [hic, ne_eq, not_true_eq_false, and_false, if_false, if_true, zero_mul,
          Finset.sum_const_zero]
      · rw [if_neg hic]
        obtain ⟨fc, hB, hmem, hread⟩ := hentry i hi
        simp only [hB, Option.some.injEq, hic, ne_eq, not_false_eq_true, and_true, ite_mul, zero_mul]
        rw [Finset.sum_ite_eq, if_pos hmem, hread]
    -- `canonNormalizationOf` at the layer-`(s.layer+1)` coord `x`: guard-1 dead, guard-2 = the recoord sum
    have hcanon : canonNormalizationOf d s pv u x
        = if (((tupIdxEquiv d).symm x).2 : ℕ) = (((tupIdxEquiv d).symm pv).1.2 : ℕ)
          then ∑ i ∈ Finset.range (d (⟨s.layer + 1, hSN⟩ : Fin N).castSucc),
            if i = (((tupIdxEquiv d).symm x).2 : ℕ) then 0
            else readEntry d u s.layer i (((tupIdxEquiv d).symm pv).2 : ℕ)
              * readEntry d u (s.layer + 1) (((tupIdxEquiv d).symm x).1.2 : ℕ) i
          else 0 := by
      simp only [canonNormalizationOf]
      rw [if_neg hfirst]
      by_cases hg : (((tupIdxEquiv d).symm x).2 : ℕ) = (((tupIdxEquiv d).symm pv).1.2 : ℕ)
      · rw [if_pos ⟨hlayNat, hg⟩, if_pos hg]; simp only [hlay]
      · rw [if_neg (fun h => hg h.2), if_neg hg]
    -- the recoord coefficient sum matches, via the diagonal `hdelta` + fiber `hfiber`
    have hRHS : (∑ j ∈ layerCoords d (s.layer + 1), recoordCoeff d s pv hSN u x j * u j)
        = u x + (if (((tupIdxEquiv d).symm x).2 : ℕ) = (((tupIdxEquiv d).symm pv).1.2 : ℕ)
          then ∑ i ∈ Finset.range (d (⟨s.layer + 1, hSN⟩ : Fin N).castSucc),
            if i = (((tupIdxEquiv d).symm x).2 : ℕ) then 0
            else readEntry d u s.layer i (((tupIdxEquiv d).symm pv).2 : ℕ)
              * readEntry d u (s.layer + 1) (((tupIdxEquiv d).symm x).1.2 : ℕ) i
          else 0) := by
      simp only [recoordCoeff, add_mul, Finset.sum_add_distrib, hdelta]
      congr 1
      by_cases hg : (((tupIdxEquiv d).symm x).2 : ℕ) = (((tupIdxEquiv d).symm pv).1.2 : ℕ)
      · rw [if_pos hg, ← hfiber]
        exact Finset.sum_congr rfl (fun j _ => by rw [if_pos hg])
      · rw [if_neg hg]
        refine Finset.sum_eq_zero (fun j _ => ?_)
        rw [if_neg hg, zero_mul]
    simp only [blockShear, Pi.add_apply]
    rw [hcanon, hRHS]
  · -- hC: `recoordCoeff` reads `u` only via `readEntry d u s.layer …`, off `layerCoords d (s.layer+1)`
    intro x hx j hj
    refine (ignoresCoords_univ_iff_agree _ _).mpr (fun u v hag => ?_)
    simp only [recoordCoeff]
    by_cases hguard : (((tupIdxEquiv d).symm x).2 : ℕ) = (((tupIdxEquiv d).symm pv).1.2 : ℕ)
    · rw [if_pos hguard, if_pos hguard]
      refine congrArg _ (Finset.sum_congr rfl (fun i _ => ?_))
      by_cases hcond : blockEntryFlat d (s.layer + 1) (((tupIdxEquiv d).symm x).1.2 : ℕ) i = some j
          ∧ i ≠ (((tupIdxEquiv d).symm x).2 : ℕ)
      · rw [if_pos hcond, if_pos hcond]
        exact readEntry_eq_of_agree_off d s.layer (s.layer + 1) i
          (((tupIdxEquiv d).symm pv).2 : ℕ) (by omega) u v hag
      · rw [if_neg hcond, if_neg hcond]
    · rw [if_neg hguard, if_neg hguard]

/-- Reverse of `decode_layer_of_mem_layerCoords`: a coord whose decoded layer is `ℓ` lies in
`layerCoords d ℓ`. -/
theorem mem_layerCoords_of_decode (d : Fin (N + 1) → ℕ) (ℓ : ℕ) (k : Fin (flatDim d))
    (h : (((tupIdxEquiv d).symm k).1.1 : ℕ) = ℓ) : k ∈ layerCoords d ℓ := by
  simp only [layerCoords, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨(tupIdxEquiv d).symm k, h, (tupIdxEquiv d).apply_symm_apply k⟩

/-- **`canonNormalizationOf` reads only off-`(layer s.layer+1)` coords at an off-`(layer s.layer+1)`
coord.** For `k ∉ layerCoords d (s.layer+1)` the recoord guard (which alone reads layer `s.layer+1`)
is dead — only the layer-`s.layer` cross-term (guard-1) or `0` survives, and both read layer `s.layer`
(off `layerCoords d (s.layer+1)`). This supplies the `hagree` clause of the comp helpers AT the support
layer, where `ShearWithinCarveRaw`'s `sl < ℓ` read-clause does not reach. -/
theorem canonNormalizationOf_agree_off_succLayer (d : Fin (N + 1) → ℕ) (s : ConState N)
    (pv : Fin (flatDim d)) (u v : Fin (flatDim d) → ℝ)
    (hag : ∀ t, t ∉ layerCoords d (s.layer + 1) → u t = v t)
    (k : Fin (flatDim d)) (hk : k ∉ layerCoords d (s.layer + 1)) :
    canonNormalizationOf d s pv u k = canonNormalizationOf d s pv v k := by
  have hlayne : (((tupIdxEquiv d).symm k).1.1 : ℕ) ≠ s.layer + 1 :=
    fun h => hk (mem_layerCoords_of_decode d _ k h)
  simp only [canonNormalizationOf]
  by_cases hg1 : (((tupIdxEquiv d).symm k).1.1 : ℕ) = s.layer ∧
      (((tupIdxEquiv d).symm k).1.2 : ℕ) ≠ (((tupIdxEquiv d).symm pv).1.2 : ℕ) ∧
      (((tupIdxEquiv d).symm k).2 : ℕ) ≠ (((tupIdxEquiv d).symm pv).2 : ℕ) ∧
      s.cleared ≤ (((tupIdxEquiv d).symm k).1.2 : ℕ) ∧ s.cleared ≤ (((tupIdxEquiv d).symm k).2 : ℕ)
  · rw [if_pos hg1, if_pos hg1,
      readEntry_eq_of_agree_off d s.layer (s.layer + 1) _ _ (by omega) u v hag,
      readEntry_eq_of_agree_off d s.layer (s.layer + 1) _ _ (by omega) u v hag]
  · have hg2 : ¬ ((((tupIdxEquiv d).symm k).1.1 : ℕ) = s.layer + 1 ∧
        (((tupIdxEquiv d).symm k).2 : ℕ) = (((tupIdxEquiv d).symm pv).1.2 : ℕ)) := fun h => hlayne h.1
    rw [if_neg hg1, if_neg hg1, if_neg hg2, if_neg hg2]

end DLNFibre.DLN.Aoyagi
