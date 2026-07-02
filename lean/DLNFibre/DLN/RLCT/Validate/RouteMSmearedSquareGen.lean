import DLNFibre.DLN.RLCT.Validate.RouteMSmearedBoxGen
import DLNFibre.DLN.RLCT.Validate.RouteMSmearedFrontFactor
import DLNFibre.DLN.RLCT.Validate.RouteMSmearedSquareL2

/-!
# `RouteMSmearedSquareGen` — the general-`L` Field-A entry bound `hSpre` (R2)

The general-`L` analog of the L=2 `condBox_subset_preimage` (`RouteMSmearedSquareL2`). Bounds every
decoded flat coord of `psiMapG (RmapG u)` by `ε` on the conditioned box `boxGen`, so the image lands in
`cubeBox ε` — discharging the Field-A containment `hSpre` that
`smearedChartDataGen_of_dets`/`smearedChartDataGen` take as an input.

The decode (`genDecode_params`) says `(paramsEquivFlat M).symm (psiMapG (RmapG u)) = chartGenParams …`,
so each flat coord is a `chartGenParams` entry. The three entry families:

* **front layers** `t ≠ deepLayer`: `frontTupleG u t i j = u (coordOfG (frontSlotG t i j))`, a direct
  box coord (`≤ δ`);
* **deep-bottom rows** `S_bot b j = u (coordOfG (botSlotG b j))`, a direct box coord (`≤ η`);
* **deep-top rows** `(z·H̄_unit − Λ₀·S_bot) a j`: the radial `z·H̄` (`≤ δ·1`) minus the shear
  `Λ₀·S_bot`. The shear is where the crux `Λ₀`-entry bound bites.

## The `Λ₀`-entry bound (the crux, decorrelated-Codex route 4)

`Λ₀ = (P₁ᵀP₁)⁻¹ P₁ᵀ P₂` with `P₁` **tall** (`M0 × r`, `M0 ≥ r`) — the L=2 square trick
`Λ₀ = P₁⁻¹P₂` is unavailable, and the tall Gram `P₁ᵀP₁` sums over the `M0−r` UNCONTROLLED front-product
rows, so a direct Varah bound on `P₁ᵀP₁` fails. Instead route through the width-`r` waist: `frontProd =
U·V` (`V : r × M⟨L−1⟩`, exactly `r` rows — the "first `r` rows only" limitation of `WideCarrierBound`
disappears). Then `Λ₀ = Vρ⁻¹·Vσ` (`gram_routing_eq_factor` + `front_factorsThrough_general`), and
`Vρ` is strictly row-dominant (a `WideCarrierBound` on the SUFFIX product `V`), so
`|Λ₀ a b| ≤ nb_V / γ_V = O(η)` (`StrictRowDominant.inv_mul_entry_bound`).
-/

open MeasureTheory Matrix
open scoped ENNReal BigOperators

namespace DLNFibre.DLN.RLCT

open DLNFibre.Core.Matrix

variable {L : ℕ} {M : Fin (L + 1) → ℕ} {r s : ℕ}

/-- **The flat decode** `paramsEquivFlat H A (Fintype.equivFin (FlatIdx H) idx) = A idx.1.1 idx.1.2 idx.2`
(local copy of `DeepestFrameRaw.paramsEquivFlat_apply_equivFin`, to avoid the heavy import). -/
theorem paramsEquivFlat_apply_equivFin' (H : Fin (L + 1) → ℕ) (A : Params H) (idx : FlatIdx H) :
    paramsEquivFlat H A (Fintype.equivFin (FlatIdx H) idx) = A idx.1.1 idx.1.2 idx.2 := by
  unfold paramsEquivFlat
  erw [MeasurableEquiv.trans_apply, MeasurableEquiv.trans_apply]
  simp only [MeasurableEquiv.coe_piCurry_symm]
  erw [Equiv.arrowCongr_apply]
  simp only [Function.comp_apply]
  erw [Equiv.symm_apply_apply]
  rfl

/-! ## The suffix-product carrier bound (the shifted `wideCarrierBound_prodAux`)

`prodAux_split_exists` factors `prodAux M A k = prodAux M A p * Y`; here we build the SAME `Y` with a
`WideCarrierBound` on it. `Y` is the segment product `A^p·…·A^{k−1}`, a right-fold from the identity at
`k = p` (`wideCarrierBound_one`) advancing one `CarrierLayer` at a time (`wideCarrier_mul`). Mirrors
`wideCarrierBound_prodAux` with the endpoint shifted to start at `p`. -/

/-- **The suffix-product carrier bound (existence).** For `p ≤ k` with layers `p..k−1` each a
`CarrierLayer` and widths `≥ r` throughout `p..k`, there is a `Y` with `prodAux M A k = prodAux M A p * Y`
and a `WideCarrierBound Y r dlb nb pub` with the fused invariant (`nb ≤ η·Acc`,
`(δ/2)^{k−p} − η·Acc ≤ dlb`). The base `k = p` is `Y = 1`; each step right-multiplies a `CarrierLayer`. -/
theorem wideCarrierBound_suffix (A : Params M) {δ η : ℝ} (hδ : 0 < δ) (hη : 0 ≤ η) (hηδ : η ≤ δ)
    (p : ℕ) (hp : p < L + 1)
    (hwidth : ∀ t : ℕ, ∀ ht : t < L + 1, r ≤ M ⟨t, ht⟩)
    (hlayers : ∀ t : Fin L, p ≤ (t : ℕ) → (t : ℕ) < L - 1 → CarrierLayer (A t) r δ η) :
    ∀ (k : ℕ) (hpk : p ≤ k) (hkub : k ≤ L - 1) (hk : k < L + 1),
      ∃ (Y : Matrix (Fin (M ⟨p, hp⟩)) (Fin (M ⟨k, hk⟩)) ℝ) (dlb nb pub Acc : ℝ),
        prodAux M A k hk = prodAux M A p hp * Y
          ∧ WideCarrierBound Y r dlb nb pub
          ∧ 0 ≤ nb ∧ 0 ≤ pub ∧ 0 ≤ Acc
          ∧ nb ≤ η * Acc ∧ (δ / 2) ^ (k - p) - η * Acc ≤ dlb := by
  intro k hpk
  induction k, hpk using Nat.le_induction with
  | base =>
      intro _ hk
      -- base `k = p`: `Y = 1`, `prodAux p = prodAux p * 1`; `WideCarrierBound 1 r 1 0 1`
      refine ⟨1, 1, 0, 1, 0, (Matrix.mul_one _).symm, wideCarrierBound_one, le_refl _,
        by norm_num, le_refl _, by simp, ?_⟩
      simp
  | succ k hpk ih =>
      intro hkub hk
      have hk' : k < L + 1 := Nat.lt_of_succ_lt hk
      have hkL : k < L := Nat.lt_of_succ_lt_succ hk
      have hkub' : k ≤ L - 1 := by omega
      -- the folded layer `A^k` is a free front layer (`p ≤ k < L−1`)
      have hkLm1 : k < L - 1 := by omega
      obtain ⟨Y, dlb, nb, pub, Acc, hY, hWCB, hnb0, hpub0, hAcc0, hnbA, hdlbA⟩ :=
        ih hkub' hk'
      -- peel the last layer of the PARENT at index `k`
      have e1 : M (⟨k, hk'⟩ : Fin (L + 1)) = M ((⟨k, hkL⟩ : Fin L).castSucc) := by
        apply congrArg; apply Fin.ext; simp [Fin.castSucc]
      have e2 : M (⟨k + 1, hk⟩ : Fin (L + 1)) = M ((⟨k, hkL⟩ : Fin L).succ) := by
        apply congrArg; apply Fin.ext; simp [Fin.succ]
      rw [prodAux_succ M A k hk e1 e2, hY]
      set Alay := Matrix.reindex (finCongr e1.symm) (finCongr e2.symm) (A ⟨k, hkL⟩) with hAlay
      -- the reindexed layer is a CarrierLayer
      have hCL : CarrierLayer Alay r δ η :=
        carrierLayer_reindex (A ⟨k, hkL⟩) (hlayers ⟨k, hkL⟩ hpk hkLm1) e1.symm e2.symm
      -- the interface width `M ⟨k,_⟩ ≥ r`
      have hrw : r ≤ M (⟨k, hk'⟩ : Fin (L + 1)) := hwidth k hk'
      -- one composition step: `Y' = Y * Alay`
      have hstep := wideCarrier_mul hWCB hCL hpub0 hnb0 hη hηδ hrw
      refine ⟨Y * Alay, dlb * (δ / 2) - (M (⟨k, hk'⟩ : Fin (L + 1)) - 1 : ℕ) * pub * η,
        nb * δ + M (⟨k, hk'⟩ : Fin (L + 1)) * pub * η, M (⟨k, hk'⟩ : Fin (L + 1)) * pub * δ,
        δ * Acc + M (⟨k, hk'⟩ : Fin (L + 1)) * pub, ?_, hstep, ?_, ?_, ?_, ?_, ?_⟩
      · -- `prodAux p * (Y * Alay)`: reassociate
        rw [← Matrix.mul_assoc]
      · have : (0:ℝ) ≤ (M (⟨k, hk'⟩ : Fin (L + 1)) : ℝ) := Nat.cast_nonneg _
        positivity
      · have : (0:ℝ) ≤ (M (⟨k, hk'⟩ : Fin (L + 1)) : ℝ) := Nat.cast_nonneg _
        positivity
      · have hM : (0:ℝ) ≤ (M (⟨k, hk'⟩ : Fin (L + 1)) : ℝ) := Nat.cast_nonneg _
        have : (0:ℝ) ≤ δ * Acc := mul_nonneg (le_of_lt hδ) hAcc0
        positivity
      · -- `nb' ≤ η · Acc'`
        have hM : (0:ℝ) ≤ (M (⟨k, hk'⟩ : Fin (L + 1)) : ℝ) := Nat.cast_nonneg _
        have h1 : nb * δ ≤ η * (δ * Acc) := by
          nlinarith [hnbA, hδ.le, mul_le_mul_of_nonneg_right hnbA hδ.le]
        nlinarith [h1, mul_nonneg (mul_nonneg hM hpub0) hη]
      · -- `(δ/2)^{(k+1)−p} − η·Acc' ≤ dlb'`
        have hM : (0:ℝ) ≤ (M (⟨k, hk'⟩ : Fin (L + 1)) : ℝ) := Nat.cast_nonneg _
        have hwcast : ((M (⟨k, hk'⟩ : Fin (L + 1)) - 1 : ℕ) : ℝ)
            ≤ (M (⟨k, hk'⟩ : Fin (L + 1)) : ℝ) := by exact_mod_cast Nat.sub_le _ 1
        have hlow : ((δ / 2) ^ (k - p) - η * Acc) * (δ / 2) ≤ dlb * (δ / 2) :=
          mul_le_mul_of_nonneg_right hdlbA (by positivity)
        have hcross : ((M (⟨k, hk'⟩ : Fin (L + 1)) - 1 : ℕ) : ℝ) * pub * η
            ≤ (M (⟨k, hk'⟩ : Fin (L + 1)) : ℝ) * pub * η :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hwcast hpub0) hη
        have hexp : (δ / 2) ^ (k + 1 - p) = (δ / 2) ^ (k - p) * (δ / 2) := by
          rw [show k + 1 - p = (k - p) + 1 by omega, pow_succ]
        nlinarith [hlow, hcross, hexp, mul_nonneg (mul_nonneg hM hpub0) hη, hAcc0, hη, hδ.le]

/-! ## The flat-entry readoff `psiMapG (RmapG u) i = chartGenParams entry` -/

/-- **Each flat coord of `psiMapG (RmapG u)` is a `chartGenParams` entry.** From `genDecode_params`:
`psiMapG (RmapG u) = paramsEquivFlat M (chartGenParams …)`, and `paramsEquivFlat_apply_equivFin` reads
back the layer entry at the `equivFin.symm` slot. -/
theorem psiMapG_RmapG_entry (M : Fin (L + 1) → ℕ) (hL : 0 < L)
    (hrs : r + s = M ((deepLayer hL).castSucc)) (hr : 0 < r) (hc : 0 < M ((deepLayer hL).succ))
    (u : Fin (routeMAmbient M) → ℝ)
    (e1 : M (⟨L - 1, by omega⟩ : Fin (L + 1)) = M ((⟨L - 1, by omega⟩ : Fin L).castSucc))
    (e2 : M (Fin.last L) = M ((⟨L - 1, by omega⟩ : Fin L).succ))
    (i : Fin (routeMAmbient M)) :
    psiMapG M hL hrs (RmapG M hL hrs hr hc u) i
      = chartGenParams M (frontTupleG M u) hL (hrsAtom_of_hrs hL hrs) (zuG M hL hrs hr hc u)
          ((deepLayer_succ_width M hL) ▸ HbarUnitG M hL hrs hr hc u)
          ((deepLayer_succ_width M hL) ▸ SbotuG M hL hrs u) (Lam0uG M hL hrs u) e1 e2
          ((Fintype.equivFin (FlatIdx M)).symm i).1.1
          ((Fintype.equivFin (FlatIdx M)).symm i).1.2
          ((Fintype.equivFin (FlatIdx M)).symm i).2 := by
  -- `psiMapG (RmapG u) = paramsEquivFlat M (chartGenParams …)` (the decode)
  have hpsi : psiMapG M hL hrs (RmapG M hL hrs hr hc u)
      = paramsEquivFlat M (chartGenParams M (frontTupleG M u) hL (hrsAtom_of_hrs hL hrs)
          (zuG M hL hrs hr hc u) ((deepLayer_succ_width M hL) ▸ HbarUnitG M hL hrs hr hc u)
          ((deepLayer_succ_width M hL) ▸ SbotuG M hL hrs u) (Lam0uG M hL hrs u) e1 e2) := by
    simp only [psiMapG]
    rw [genDecode_params M hL hrs hr hc u e1 e2]
  rw [hpsi]
  -- read off at `i` via the `equivFin` round-trip
  conv_lhs => rw [← Equiv.apply_symm_apply (Fintype.equivFin (FlatIdx M)) i]
  rw [paramsEquivFlat_apply_equivFin']

end DLNFibre.DLN.RLCT
