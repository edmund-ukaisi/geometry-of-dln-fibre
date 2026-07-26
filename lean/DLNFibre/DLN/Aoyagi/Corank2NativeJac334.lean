import DLNFibre.DLN.Aoyagi.Corank2NativeValue334

/-!
# `DLN.Aoyagi.Corank2NativeJac334` — the (C)-seat composite Jacobian of the whole-conjugate leaf

The composite `|jacDet|` of the whole-conjugate born-native leaf chart `gFlat idx`
(`Corank2NativeFan334`), the reusable core of the (C)-seat `hjac`. Via the `jacDet_comp` chain rule
over the five atoms `bb(S1,p1) ∘ nativeSel p1 ∘ nativePerm p1 ∘ bb(σC1,p2) ∘ bb(σC2,p3)`:

* the two shears contribute `|jacDet| = 1` (`nativeSel_jacDet` = 1, `nativePerm_jacDet` = ±1);
* each block blow-up contributes `|·_pivot|^(|center|−1)` (`jacDet_blockBlowupMap`), so exponents
  `8` (`|S1| = 9`), `7` (`|σC1| = 8`), `3` (`|σC2| = 4`);
* the pivot coordinate `p1` is FIXED through the inner atoms (the two shears fix it, the two inner
  blow-ups are spectators at `p1`), so the outer blow-up reads `|u p1|^8`.

Result: `|jacDet (gFlat idx) u| = |u p1|^8 · |(bb σC2 p3 u) p2|^7 · |u p3|^3` — a single monomial (up
to the perm sign), so the `hjac` unit is `≡ 1`.

## Scope
- IN: the per-dominant pivot-fixing facts (`nativeSel_fix_pivot`, `nativePerm_fix_pivot`,
  `nativeChart1_fix_pivot`); the atom-count lemmas; `abs_jacDet_nativeChart1 = 1`; the composite
  `abs_jacDet_gFlat`.
- OUT: the per-leaf monomial `jac` exponent + `hjac` (jacWeight form) + `divisorMin ≥ 8` (the (C)
  tail, next); the over-vanishing feeder (elder-gated).
-/

open MeasureTheory Set Metric
open DLNFibre.Core.Aoyagi
open DLNFibre.DLN.Aoyagi.NativeShear334
open DLNFibre.DLN.Aoyagi.NativePerm334
open DLNFibre.DLN.Aoyagi.NativeFan334
open DLNFibre.DLN.Aoyagi.NativeValue334
open DLNFibre.DLN.Aoyagi.GeneralGeoAtlas

namespace DLNFibre.DLN.Aoyagi.NativeJac334

/-! ## §0 — atom counts + the pivot not in the inner centres -/

theorem S1_card : (S1).card = 9 := by decide
theorem sigmaC1Fs_card (p : Fin 21) : (sigmaC1Fs p).card = 8 := by revert p; decide
theorem sigmaC2Fs_card (p : Fin 21) : (sigmaC2Fs p).card = 4 := by revert p; decide

/-- No `p ∈ S1` lies in its own permuted node-3 centre `σC2(p)` (`p = σ(20) ∉ σ(C2)`). -/
theorem p1_notMem_sigmaC2Fs : ∀ p : Fin 21, p ∈ S1 → p ∉ sigmaC2Fs p := by decide

/-! ## §1 — the pivot coordinate `p1` is fixed through the node-1 shear -/

/-- The native shear fixes the dominant pivot coordinate (`p1` is a kept coordinate). -/
theorem nativeSel_fix_pivot (p : Fin 21) (hp : p ∈ S1) (w : Fin 21 → ℝ) :
    nativeSel p w p = w p := by
  fin_cases hp <;>
    simp [nativeSel, blockShear, qdisp, sterm, t1P0, t2P0, t1P1, t2P1, t1P2, t2P2, t1P3, t2P3,
      t1P4, t2P4, t1P5, t2P5, t1P6, t2P6, t1P7, t2P7, t1P20, t2P20]

/-- The native permutation fixes the dominant pivot coordinate (`cperm_p p = p`). -/
theorem nativePerm_fix_pivot (p : Fin 21) (hp : p ∈ S1) (w : Fin 21 → ℝ) :
    nativePerm p w p = w p := by
  fin_cases hp <;>
    simp only [nativePerm, Fin.reduceEq, if_true, if_false, cperm0, cperm1, cperm2, cperm3,
      cperm4, cperm5, cperm6, cperm7, cperm20, cpermS0, cpermS1, cpermS2, cpermS3, cpermS4,
      cpermS5, cpermS6, cpermS7, cpermS20, Equiv.ofBijective_apply]

/-- The composite node-1 shear fixes the dominant pivot coordinate. -/
theorem nativeChart1_fix_pivot (p : Fin 21) (hp : p ∈ S1) (w : Fin 21 → ℝ) :
    nativeChart1 p w p = w p := by
  rw [nativeChart1, Function.comp_apply, nativeSel_fix_pivot p hp (nativePerm p w),
    nativePerm_fix_pivot p hp w]

/-- `|jacDet (nativeChart1 p) u| = 1` (unipotent shear ∘ ±1 permutation). -/
theorem abs_jacDet_nativeChart1 (p : Fin 21) (hp : p ∈ S1) (u : Fin 21 → ℝ) :
    |jacDet (nativeChart1 p) u| = 1 := by
  rw [nativeChart1, jacDet_comp u (nativeSel_differentiable p).differentiableAt
    (nativePerm_differentiable p).differentiableAt, abs_mul, nativeSel_jacDet p hp,
    nativePerm_jacDet p hp, abs_one, one_mul]

/-! ## §2 — the composite Jacobian of the leaf chart -/

/-- **The composite leaf Jacobian** `|jacDet (gFlat idx) u| = |u p1|^8 · |(bb σC2 p3 u) p2|^7 ·
|u p3|^3`. The `jacDet_comp` telescope over the five atoms; the two shears drop out (`|jacDet| = 1`),
the three blow-ups give the center-size−1 monomial factors, and the outer factor reads `u p1` because
`p1` is fixed through the inner atoms. -/
theorem abs_jacDet_gFlat (idx : Idx) (u : Fin 21 → ℝ) :
    |jacDet (gFlat idx) u|
      = |u idx.1.1| ^ 8
        * |(blockBlowupMap (sigmaC2Fs idx.1.1) idx.2.2.1 u) idx.2.1.1| ^ 7
        * |u idx.2.2.1| ^ 3 := by
  obtain ⟨⟨p1, hp1⟩, ⟨p2, hp2⟩, ⟨p3, hp3⟩⟩ := idx
  have dA : Differentiable ℝ (blockBlowupMap S1 p1) := differentiable_blockBlowupMap _ _
  have dB : Differentiable ℝ (blockBlowupMap (sigmaC1Fs p1) p2) := differentiable_blockBlowupMap _ _
  have dC : Differentiable ℝ (blockBlowupMap (sigmaC2Fs p1) p3) := differentiable_blockBlowupMap _ _
  have dN : Differentiable ℝ (nativeChart1 p1) := nativeChart1_differentiable p1
  -- flatten the `∘ id`s: gFlat = A ∘ N ∘ B ∘ C
  have hflat : gFlat ⟨⟨p1, hp1⟩, ⟨p2, hp2⟩, ⟨p3, hp3⟩⟩
      = blockBlowupMap S1 p1 ∘ nativeChart1 p1
        ∘ blockBlowupMap (sigmaC1Fs p1) p2 ∘ blockBlowupMap (sigmaC2Fs p1) p3 := by
    funext x; simp only [gFlat, Function.comp_apply, id_eq]
  rw [hflat]
  -- telescope: A ∘ (N ∘ (B ∘ C)), all at base point u
  rw [jacDet_comp u dA.differentiableAt (dN.comp (dB.comp dC)).differentiableAt, abs_mul,
    jacDet_comp u dN.differentiableAt (dB.comp dC).differentiableAt, abs_mul,
    jacDet_comp u dB.differentiableAt dC.differentiableAt, abs_mul]
  simp only [Function.comp_apply]
  -- the four factors
  have fN : |jacDet (nativeChart1 p1)
      (blockBlowupMap (sigmaC1Fs p1) p2 (blockBlowupMap (sigmaC2Fs p1) p3 u))| = 1 :=
    abs_jacDet_nativeChart1 p1 hp1 _
  have e8 : (S1).card - 1 = 8 := by rw [S1_card]
  have e7 : (sigmaC1Fs p1).card - 1 = 7 := by rw [sigmaC1Fs_card]
  have e3 : (sigmaC2Fs p1).card - 1 = 3 := by rw [sigmaC2Fs_card]
  have fC : |jacDet (blockBlowupMap (sigmaC2Fs p1) p3) u| = |u p3| ^ 3 := by
    rw [jacDet_blockBlowupMap hp3, abs_pow, e3]
  have fB : |jacDet (blockBlowupMap (sigmaC1Fs p1) p2) (blockBlowupMap (sigmaC2Fs p1) p3 u)|
      = |(blockBlowupMap (sigmaC2Fs p1) p3 u) p2| ^ 7 := by
    rw [jacDet_blockBlowupMap hp2, abs_pow, e7]
  have hfix : (nativeChart1 p1
      (blockBlowupMap (sigmaC1Fs p1) p2 (blockBlowupMap (sigmaC2Fs p1) p3 u))) p1 = u p1 := by
    rw [nativeChart1_fix_pivot p1 hp1 _,
      blockBlowupMap_offCenter_eq _ _ _ (p1_notMem_sigmaC1Fs p1 hp1),
      blockBlowupMap_offCenter_eq _ _ _ (p1_notMem_sigmaC2Fs p1 hp1)]
  have fA : |jacDet (blockBlowupMap S1 p1) (nativeChart1 p1
      (blockBlowupMap (sigmaC1Fs p1) p2 (blockBlowupMap (sigmaC2Fs p1) p3 u)))| = |u p1| ^ 8 := by
    rw [jacDet_blockBlowupMap hp1, hfix, abs_pow, e8]
  rw [fN, fC, fB, fA]
  ring

end DLNFibre.DLN.Aoyagi.NativeJac334
