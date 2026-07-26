import DLNFibre.DLN.Aoyagi.Corank2OverVanishCanon334

/-!
# `DLN.Aoyagi.Corank2OverVanishA_20_1_5` — the per-type CONCRETE facts, leaf `(20,1,5)`

Pattern-A over-vanishing leaf `(p1,p2,p3) = (20,1,5)`. Mirrors the proven `(20,1,1)` template
`Corank2OverVanishCanon334`; shared leaf-independent lemmas `coreGen_eWrap_entry`, `A1_··`,
`blockShear_covers_cubic` reused from there. The 8 reg-seq entry values are `sympy`-verified
END-TO-END against the Lean `gFlat` (independent derivation matching `ov-pertype-16leaf-data.md`).
Reg-seq drops column `c = 2` (pattern A); straighten block `{12,13,14,15}`;
purely QUADRATIC straightening.
-/

open Matrix MeasureTheory Set Metric
open DLNFibre.Core.Aoyagi
open DLNFibre.DLN.Aoyagi.NativeFan334
open DLNFibre.DLN.Aoyagi.NativePerm334
open DLNFibre.DLN.Aoyagi.NativeShear334
open DLNFibre.DLN.Aoyagi.NativeJac334
open DLNFibre.DLN.Aoyagi.OverVanish334
open DLNFibre.DLN.Aoyagi.Corank2CoreGenWrap
open DLNFibre.DLN.Aoyagi.OverVanishCanon334 (coreGen_eWrap_entry
  A1_00 A1_01 A1_02 A1_10 A1_11 A1_12 A1_20 A1_21 A1_22 A1_30 A1_31 A1_32)

namespace DLNFibre.DLN.Aoyagi.OverVanishA_20_1_5

/-! ## §0 — the leaf and the composite -/

def idxCanon : Idx := ⟨⟨20, by decide⟩, ⟨1, by decide⟩, ⟨5, by decide⟩⟩

noncomputable def gCanon : (Fin 21 → ℝ) → (Fin 21 → ℝ) := fun w =>
  blockBlowupMap S1 20 (nativeChart1 20
    (blockBlowupMap (sigmaC1Fs 20) 1 (blockBlowupMap (sigmaC2Fs 20) 5 w)))

theorem gFlat_idxCanon : gFlat idxCanon = gCanon := by funext w; rfl

/-! ## §1 — the straightening shear `Ψ = psiCanon` -/

def phiCanon : (Fin 21 → ℝ) → (Fin 21 → ℝ) := fun u i =>
  if i = 12 then -(u 0 * u 10 + u 16 * u 5)
  else if i = 13 then -(u 10 * u 2 + u 17 * u 5)
  else if i = 14 then -(u 10 * u 3 + u 18 * u 5)
  else if i = 15 then -(u 10 * u 4 + u 19 * u 5)
  else 0

noncomputable def psiCanon : (Fin 21 → ℝ) → (Fin 21 → ℝ) := blockShear phiCanon

abbrev keepCanon : Fin 21 → Prop := fun i => i ≠ 12 ∧ i ≠ 13 ∧ i ≠ 14 ∧ i ≠ 15

theorem phiCanon_keep (u : Fin 21 → ℝ) (i : Fin 21) (hi : keepCanon i) : phiCanon u i = 0 := by
  obtain ⟨h12, h13, h14, h15⟩ := hi
  simp only [phiCanon, if_neg h12, if_neg h13, if_neg h14, if_neg h15]

set_option linter.unusedSimpArgs false in
theorem phiCanon_read (u v : Fin 21 → ℝ) (h : ∀ i, keepCanon i → u i = v i) :
    phiCanon u = phiCanon v := by
  have h0 := h 0 (by decide)
  have h2 := h 2 (by decide)
  have h3 := h 3 (by decide)
  have h4 := h 4 (by decide)
  have h5 := h 5 (by decide)
  have h10 := h 10 (by decide)
  have h16 := h 16 (by decide)
  have h17 := h 17 (by decide)
  have h18 := h 18 (by decide)
  have h19 := h 19 (by decide)
  funext i
  simp only [phiCanon]
  split_ifs <;> simp only [h0, h2, h3, h4, h5, h10, h16, h17, h18, h19]

set_option linter.unusedSimpArgs false in
theorem differentiable_phiCanon : Differentiable ℝ phiCanon := by
  apply differentiable_pi.2
  intro i
  fin_cases i <;>
    simp (config := { decide := true }) only [phiCanon, Fin.isValue, if_true, if_false] <;>
    fun_prop

theorem differentiable_psiCanon : Differentiable ℝ psiCanon := by
  unfold psiCanon blockShear
  exact differentiable_id.add differentiable_phiCanon

theorem jacDet_psiCanon (u : Fin 21 → ℝ) : jacDet psiCanon u = 1 := by
  unfold psiCanon
  exact jacDet_blockShear phiCanon keepCanon differentiable_phiCanon phiCanon_keep phiCanon_read u

theorem psiCanon_apply_offblock (u : Fin 21 → ℝ) (d : Fin 21) (hd : keepCanon d) :
    psiCanon u d = u d := by
  unfold psiCanon blockShear
  simp only [Pi.add_apply, phiCanon_keep u d hd, add_zero]

/-! ## §2 — the per-type data -/

def vmExpCanon : Fin 21 → ℕ := fun d => if d = 1 ∨ d = 5 ∨ d = 20 then 1 else 0

theorem prod_vmExpCanon (u : Fin 21 → ℝ) : (∏ d, (u d) ^ vmExpCanon d) = u 1 * u 5 * u 20 := by
  have h1 : ∀ d : Fin 21, u d ^ vmExpCanon d
      = if d = 1 ∨ d = 5 ∨ d = 20 then u d else 1 := fun d => by
    simp only [vmExpCanon]; split_ifs <;> simp
  simp_rw [h1]
  rw [Finset.prod_ite, Finset.prod_const_one, mul_one,
    show Finset.filter (fun d : Fin 21 => d = 1 ∨ d = 5 ∨ d = 20) Finset.univ
        = {1, 5, 20} from by decide,
    Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_singleton]
  ring

def pairsCanon : Finset (Fin 4 × Fin 3) :=
  {(0, 0), (0, 1), (1, 0), (1, 1), (2, 0), (2, 1), (3, 0), (3, 1)}

def Scanon : Finset (Fin (dvec (Fin.last 2) * dvec 0)) := pairsCanon.image finProdFinEquiv

def zcPair : Fin 4 × Fin 3 → Fin 21 := fun p =>
  if p = (0, 0) then 0 else if p = (0, 1) then 12 else if p = (1, 0) then 2
  else if p = (1, 1) then 13 else if p = (2, 0) then 3 else if p = (2, 1) then 14
  else if p = (3, 0) then 4 else 15

def zcCanon : Fin (dvec (Fin.last 2) * dvec 0) → Fin 21 := fun k => zcPair (finProdFinEquiv.symm k)

def Zcanon : Finset (Fin 21) := {0, 2, 3, 4, 12, 13, 14, 15}

theorem hzc_inj : ∀ x ∈ Scanon, ∀ y ∈ Scanon, zcCanon x = zcCanon y → x = y := by decide

theorem hzc_img : Scanon.image zcCanon = Zcanon := by decide

/-! ## §3 — the 8 reg-seq entry identities -/

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 8000 in
set_option linter.unusedSimpArgs false in
set_option linter.style.maxHeartbeats false in
theorem entry_00 (u : Fin 21 → ℝ) :
    coreGen dvec eWrap (finProdFinEquiv ((0 : Fin 4), (0 : Fin 3))) (gCanon (psiCanon u))
      = (∏ d, (u d) ^ vmExpCanon d) * u 0 := by
  rw [prod_vmExpCanon, coreGen_eWrap_entry]
  simp only [Equiv.symm_apply_apply, Fin.isValue]
  rw [Matrix.mul_apply, Fin.sum_univ_three]
  simp (config := { decide := true }) only [gCanon, psiCanon, phiCanon, blockShear,
    A0, A1_00, A1_01, A1_02, A1_10, A1_11, A1_12, A1_20, A1_21, A1_22, A1_30, A1_31, A1_32,
    nativeChart1, nativeSel, nativePerm, blockBlowupMap, sigmaC1Fs, sigmaC2Fs, qdisp, sterm,
    t1P20, t2P20, Function.comp_apply, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
    Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_fin_const,
    cpermS20, Equiv.ofBijective_apply, cperm20, Pi.add_apply, Fin.isValue, Option.elim,
    if_true, if_false]
  ring

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 8000 in
set_option linter.unusedSimpArgs false in
set_option linter.style.maxHeartbeats false in
theorem entry_01 (u : Fin 21 → ℝ) :
    coreGen dvec eWrap (finProdFinEquiv ((0 : Fin 4), (1 : Fin 3))) (gCanon (psiCanon u))
      = (∏ d, (u d) ^ vmExpCanon d) * u 12 := by
  rw [prod_vmExpCanon, coreGen_eWrap_entry]
  simp only [Equiv.symm_apply_apply, Fin.isValue]
  rw [Matrix.mul_apply, Fin.sum_univ_three]
  simp (config := { decide := true }) only [gCanon, psiCanon, phiCanon, blockShear,
    A0, A1_00, A1_01, A1_02, A1_10, A1_11, A1_12, A1_20, A1_21, A1_22, A1_30, A1_31, A1_32,
    nativeChart1, nativeSel, nativePerm, blockBlowupMap, sigmaC1Fs, sigmaC2Fs, qdisp, sterm,
    t1P20, t2P20, Function.comp_apply, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
    Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_fin_const,
    cpermS20, Equiv.ofBijective_apply, cperm20, Pi.add_apply, Fin.isValue, Option.elim,
    if_true, if_false]
  ring

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 8000 in
set_option linter.unusedSimpArgs false in
set_option linter.style.maxHeartbeats false in
theorem entry_10 (u : Fin 21 → ℝ) :
    coreGen dvec eWrap (finProdFinEquiv ((1 : Fin 4), (0 : Fin 3))) (gCanon (psiCanon u))
      = (∏ d, (u d) ^ vmExpCanon d) * u 2 := by
  rw [prod_vmExpCanon, coreGen_eWrap_entry]
  simp only [Equiv.symm_apply_apply, Fin.isValue]
  rw [Matrix.mul_apply, Fin.sum_univ_three]
  simp (config := { decide := true }) only [gCanon, psiCanon, phiCanon, blockShear,
    A0, A1_00, A1_01, A1_02, A1_10, A1_11, A1_12, A1_20, A1_21, A1_22, A1_30, A1_31, A1_32,
    nativeChart1, nativeSel, nativePerm, blockBlowupMap, sigmaC1Fs, sigmaC2Fs, qdisp, sterm,
    t1P20, t2P20, Function.comp_apply, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
    Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_fin_const,
    cpermS20, Equiv.ofBijective_apply, cperm20, Pi.add_apply, Fin.isValue, Option.elim,
    if_true, if_false]
  ring

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 8000 in
set_option linter.unusedSimpArgs false in
set_option linter.style.maxHeartbeats false in
theorem entry_11 (u : Fin 21 → ℝ) :
    coreGen dvec eWrap (finProdFinEquiv ((1 : Fin 4), (1 : Fin 3))) (gCanon (psiCanon u))
      = (∏ d, (u d) ^ vmExpCanon d) * u 13 := by
  rw [prod_vmExpCanon, coreGen_eWrap_entry]
  simp only [Equiv.symm_apply_apply, Fin.isValue]
  rw [Matrix.mul_apply, Fin.sum_univ_three]
  simp (config := { decide := true }) only [gCanon, psiCanon, phiCanon, blockShear,
    A0, A1_00, A1_01, A1_02, A1_10, A1_11, A1_12, A1_20, A1_21, A1_22, A1_30, A1_31, A1_32,
    nativeChart1, nativeSel, nativePerm, blockBlowupMap, sigmaC1Fs, sigmaC2Fs, qdisp, sterm,
    t1P20, t2P20, Function.comp_apply, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
    Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_fin_const,
    cpermS20, Equiv.ofBijective_apply, cperm20, Pi.add_apply, Fin.isValue, Option.elim,
    if_true, if_false]
  ring

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 8000 in
set_option linter.unusedSimpArgs false in
set_option linter.style.maxHeartbeats false in
theorem entry_20 (u : Fin 21 → ℝ) :
    coreGen dvec eWrap (finProdFinEquiv ((2 : Fin 4), (0 : Fin 3))) (gCanon (psiCanon u))
      = (∏ d, (u d) ^ vmExpCanon d) * u 3 := by
  rw [prod_vmExpCanon, coreGen_eWrap_entry]
  simp only [Equiv.symm_apply_apply, Fin.isValue]
  rw [Matrix.mul_apply, Fin.sum_univ_three]
  simp (config := { decide := true }) only [gCanon, psiCanon, phiCanon, blockShear,
    A0, A1_00, A1_01, A1_02, A1_10, A1_11, A1_12, A1_20, A1_21, A1_22, A1_30, A1_31, A1_32,
    nativeChart1, nativeSel, nativePerm, blockBlowupMap, sigmaC1Fs, sigmaC2Fs, qdisp, sterm,
    t1P20, t2P20, Function.comp_apply, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
    Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_fin_const,
    cpermS20, Equiv.ofBijective_apply, cperm20, Pi.add_apply, Fin.isValue, Option.elim,
    if_true, if_false]
  ring

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 8000 in
set_option linter.unusedSimpArgs false in
set_option linter.style.maxHeartbeats false in
theorem entry_21 (u : Fin 21 → ℝ) :
    coreGen dvec eWrap (finProdFinEquiv ((2 : Fin 4), (1 : Fin 3))) (gCanon (psiCanon u))
      = (∏ d, (u d) ^ vmExpCanon d) * u 14 := by
  rw [prod_vmExpCanon, coreGen_eWrap_entry]
  simp only [Equiv.symm_apply_apply, Fin.isValue]
  rw [Matrix.mul_apply, Fin.sum_univ_three]
  simp (config := { decide := true }) only [gCanon, psiCanon, phiCanon, blockShear,
    A0, A1_00, A1_01, A1_02, A1_10, A1_11, A1_12, A1_20, A1_21, A1_22, A1_30, A1_31, A1_32,
    nativeChart1, nativeSel, nativePerm, blockBlowupMap, sigmaC1Fs, sigmaC2Fs, qdisp, sterm,
    t1P20, t2P20, Function.comp_apply, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
    Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_fin_const,
    cpermS20, Equiv.ofBijective_apply, cperm20, Pi.add_apply, Fin.isValue, Option.elim,
    if_true, if_false]
  ring

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 8000 in
set_option linter.unusedSimpArgs false in
set_option linter.style.maxHeartbeats false in
theorem entry_30 (u : Fin 21 → ℝ) :
    coreGen dvec eWrap (finProdFinEquiv ((3 : Fin 4), (0 : Fin 3))) (gCanon (psiCanon u))
      = (∏ d, (u d) ^ vmExpCanon d) * u 4 := by
  rw [prod_vmExpCanon, coreGen_eWrap_entry]
  simp only [Equiv.symm_apply_apply, Fin.isValue]
  rw [Matrix.mul_apply, Fin.sum_univ_three]
  simp (config := { decide := true }) only [gCanon, psiCanon, phiCanon, blockShear,
    A0, A1_00, A1_01, A1_02, A1_10, A1_11, A1_12, A1_20, A1_21, A1_22, A1_30, A1_31, A1_32,
    nativeChart1, nativeSel, nativePerm, blockBlowupMap, sigmaC1Fs, sigmaC2Fs, qdisp, sterm,
    t1P20, t2P20, Function.comp_apply, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
    Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_fin_const,
    cpermS20, Equiv.ofBijective_apply, cperm20, Pi.add_apply, Fin.isValue, Option.elim,
    if_true, if_false]
  ring

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 8000 in
set_option linter.unusedSimpArgs false in
set_option linter.style.maxHeartbeats false in
theorem entry_31 (u : Fin 21 → ℝ) :
    coreGen dvec eWrap (finProdFinEquiv ((3 : Fin 4), (1 : Fin 3))) (gCanon (psiCanon u))
      = (∏ d, (u d) ^ vmExpCanon d) * u 15 := by
  rw [prod_vmExpCanon, coreGen_eWrap_entry]
  simp only [Equiv.symm_apply_apply, Fin.isValue]
  rw [Matrix.mul_apply, Fin.sum_univ_three]
  simp (config := { decide := true }) only [gCanon, psiCanon, phiCanon, blockShear,
    A0, A1_00, A1_01, A1_02, A1_10, A1_11, A1_12, A1_20, A1_21, A1_22, A1_30, A1_31, A1_32,
    nativeChart1, nativeSel, nativePerm, blockBlowupMap, sigmaC1Fs, sigmaC2Fs, qdisp, sterm,
    t1P20, t2P20, Function.comp_apply, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
    Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_fin_const,
    cpermS20, Equiv.ofBijective_apply, cperm20, Pi.add_apply, Fin.isValue, Option.elim,
    if_true, if_false]
  ring

set_option linter.unusedSimpArgs false in
/-- **The 8 reg-seq entry identities.** -/
theorem canon_hentry (u : Fin 21 → ℝ) (k : Fin (dvec (Fin.last 2) * dvec 0)) (hk : k ∈ Scanon) :
    coreGen dvec eWrap k (gFlat idxCanon (psiCanon u))
      = (∏ d, (u d) ^ vmExpCanon d) * u (zcCanon k) := by
  rw [gFlat_idxCanon]
  simp only [Scanon, Finset.mem_image] at hk
  obtain ⟨p, hp, rfl⟩ := hk
  simp only [zcCanon, Equiv.symm_apply_apply]
  fin_cases hp
  · exact entry_00 u
  · exact entry_01 u
  · exact entry_10 u
  · exact entry_11 u
  · exact entry_20 u
  · exact entry_21 u
  · exact entry_30 u
  · exact entry_31 u

/-! ## §4 — the assembled per-type domination fact -/

theorem canon_domination (u : Fin 21 → ℝ) :
    monoSumSqGerm vmExpCanon Zcanon u
      ≤ sumSqFam (fun i ↦ coreGen dvec eWrap i ∘ (gFlat idxCanon ∘ psiCanon)) u :=
  monoSumSqGerm_le_of_regSeq_entries (S := Scanon) (zc := zcCanon) canon_hentry hzc_inj hzc_img u

/-! ## §5 — the folded Jacobian -/

set_option linter.unusedSimpArgs false in
theorem hfix_jacExp (u : Fin 21 → ℝ) :
    ∀ d, 0 < jacExp idxCanon d → psiCanon u d = u d := by
  intro d hd
  apply psiCanon_apply_offblock u d
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    (intro h; subst h;
     simp (config := { decide := true }) only [jacExp, idxCanon, NativeJac334.single,
       NativeFan334.sigmaC2Fs] at hd)

theorem canon_foldedJac (u : Fin 21 → ℝ) :
    |jacDet (gFlat idxCanon ∘ psiCanon) u| = jacWeight (jacExp idxCanon) u := by
  rw [jacDet_comp u (differentiable_gFlat idxCanon).differentiableAt
    differentiable_psiCanon.differentiableAt, abs_mul, jacDet_psiCanon, abs_one, mul_one,
    hjac_gFlat idxCanon (psiCanon u)]
  exact jacWeight_fixOn (jacExp idxCanon) (hfix_jacExp u)

/-! ## §6 — the QUADRATIC cover-transport atom -/

theorem phiCanon_norm_bound {x : Fin 21 → ℝ} {r : ℝ} (hx : ‖x‖ ≤ r) :
    ‖phiCanon x‖ ≤ 2 * r ^ 2 := by
  have hr0 : 0 ≤ r := le_trans (norm_nonneg x) hx
  have habs : ∀ i : Fin 21, |x i| ≤ r := fun i => by
    rw [← Real.norm_eq_abs]; exact (norm_le_pi_norm x i).trans hx
  have hq : ∀ a b : Fin 21, |x a * x b| ≤ r ^ 2 := fun a b => by
    rw [abs_mul, sq]; exact mul_le_mul (habs a) (habs b) (abs_nonneg _) hr0
  have slot : ∀ a b c d : Fin 21, |(-(x a * x b + x c * x d))| ≤ 2 * r ^ 2 := fun a b c d => by
    rw [abs_neg]
    calc |x a * x b + x c * x d| ≤ |x a * x b| + |x c * x d| := abs_add_le _ _
      _ ≤ r ^ 2 + r ^ 2 := add_le_add (hq a b) (hq c d)
      _ = 2 * r ^ 2 := by ring
  rw [pi_norm_le_iff_of_nonneg (by positivity)]
  intro i
  rw [Real.norm_eq_abs]
  by_cases h12 : i = 12
  · rw [h12, show phiCanon x 12 = -(x 0 * x 10 + x 16 * x 5) from rfl]; exact slot 0 10 16 5
  by_cases h13 : i = 13
  · rw [h13, show phiCanon x 13 = -(x 10 * x 2 + x 17 * x 5) from rfl]; exact slot 10 2 17 5
  by_cases h14 : i = 14
  · rw [h14, show phiCanon x 14 = -(x 10 * x 3 + x 18 * x 5) from rfl]; exact slot 10 3 18 5
  by_cases h15 : i = 15
  · rw [h15, show phiCanon x 15 = -(x 10 * x 4 + x 19 * x 5) from rfl]; exact slot 10 4 19 5
  · rw [phiCanon_keep x i ⟨h12, h13, h14, h15⟩, abs_zero]; positivity

/-- **The folded-chart cover survives the quadratic fold.** -/
theorem image_comp_psiCanon_quad_superset (g : (Fin 21 → ℝ) → (Fin 21 → ℝ)) {r : ℝ} :
    g '' closedBall 0 r ⊆ (g ∘ psiCanon) '' closedBall 0 (r + 2 * r ^ 2) := by
  unfold psiCanon
  exact image_comp_blockShear_superset g keepCanon phiCanon_keep phiCanon_read
    (fun x hx => phiCanon_norm_bound hx)

end DLNFibre.DLN.Aoyagi.OverVanishA_20_1_5
