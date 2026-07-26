import DLNFibre.DLN.Aoyagi.Corank2OverVanishCanon334

/-!
# `DLN.Aoyagi.Corank2OverVanishB_20_6_5` — pattern-B over-vanishing leaf `(20,6,5)`

The pattern-B per-type deliverables for the over-vanishing leaf `(p1,p2,p3) = (20,6,5)`, mirroring
the canonical `(20,1,1)` template (`Corank2OverVanishCanon334`). Pattern B = reg-seq DROPS column
`c = 1` (keeps columns `c = 0, 2`), `S = {0,2,3,5,6,8,9,11}`; straighten-block `{12, 13, 14, 15}` (`p2 = 6`).

`(20,6,5)` is NON-coinciding, `vm = u5 · u6 · u20`; its `φ` carries a degree-3 term, so the CUBIC cover atom applies. The 8
reg-seq entry values are `sympy`-verified end-to-end vs the Lean `gFlat` (`a3f030 @4ceface15`,
independently cross-checked by this seat, max err `1.3e-15`).
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
  A1_00 A1_01 A1_02 A1_10 A1_11 A1_12 A1_20 A1_21 A1_22 A1_30 A1_31 A1_32 blockShear_covers_cubic)

namespace DLNFibre.DLN.Aoyagi.OverVanishB_20_6_5

/-! ## §0 — the leaf and its composite -/

/-- The over-vanishing leaf index `(p1,p2,p3) = (20,6,5)`. -/
def idxCanon : Idx := ⟨⟨20, by decide⟩, ⟨6, by decide⟩, ⟨5, by decide⟩⟩

/-- The leaf composite `gFlat idxCanon`. -/
noncomputable def gCanon : (Fin 21 → ℝ) → (Fin 21 → ℝ) := fun w =>
  blockBlowupMap S1 20 (nativeChart1 20
    (blockBlowupMap (sigmaC1Fs 20) 6 (blockBlowupMap (sigmaC2Fs 20) 5 w)))

/-- `gFlat idxCanon = gCanon`. -/
theorem gFlat_idxCanon : gFlat idxCanon = gCanon := by funext w; rfl

/-! ## §1 — the straightening shear `Ψ = psiCanon` -/

/-- The straightening displacement `φ` (pattern-B, block `{12,13,14,15}`). -/
def phiCanon : (Fin 21 → ℝ) → (Fin 21 → ℝ) := fun u i =>
  if i = 12 then -(u 0 * u 11 + u 16 * u 5 * u 7)
  else if i = 13 then -(u 11 * u 2 + u 17 * u 5 * u 7)
  else if i = 14 then -(u 11 * u 3 + u 18 * u 5 * u 7)
  else if i = 15 then -(u 11 * u 4 + u 19 * u 5 * u 7)
  else 0

/-- The straightening `Ψ = blockShear φ`. -/
noncomputable def psiCanon : (Fin 21 → ℝ) → (Fin 21 → ℝ) := blockShear phiCanon

/-- The kept coordinates: everything outside the straightened block. -/
abbrev keepCanon : Fin 21 → Prop := fun i => i ≠ 12 ∧ i ≠ 13 ∧ i ≠ 14 ∧ i ≠ 15

/-- `φ` fixes every kept coordinate. -/
theorem phiCanon_keep (u : Fin 21 → ℝ) (i : Fin 21) (hi : keepCanon i) : phiCanon u i = 0 := by
  obtain ⟨h12, h13, h14, h15⟩ := hi
  simp only [phiCanon, if_neg h12, if_neg h13, if_neg h14, if_neg h15]

set_option linter.unusedSimpArgs false in
/-- `φ` reads only kept coordinates. -/
theorem phiCanon_read (u v : Fin 21 → ℝ) (h : ∀ i, keepCanon i → u i = v i) :
    phiCanon u = phiCanon v := by
  have h0 := h 0 (by decide)
  have h2 := h 2 (by decide)
  have h3 := h 3 (by decide)
  have h4 := h 4 (by decide)
  have h5 := h 5 (by decide)
  have h7 := h 7 (by decide)
  have h11 := h 11 (by decide)
  have h16 := h 16 (by decide)
  have h17 := h 17 (by decide)
  have h18 := h 18 (by decide)
  have h19 := h 19 (by decide)
  funext i
  simp only [phiCanon]
  split_ifs <;> simp only [h0, h2, h3, h4, h5, h7, h11, h16, h17, h18, h19]

set_option linter.unusedSimpArgs false in
/-- `φ` is differentiable. -/
theorem differentiable_phiCanon : Differentiable ℝ phiCanon := by
  apply differentiable_pi.2
  intro i
  fin_cases i <;>
    simp (config := { decide := true }) only [phiCanon, Fin.isValue, if_true, if_false] <;>
    fun_prop

/-- `Ψ` is differentiable. -/
theorem differentiable_psiCanon : Differentiable ℝ psiCanon := by
  unfold psiCanon blockShear
  exact differentiable_id.add differentiable_phiCanon

/-- **`|jacDet Ψ| = 1`**. -/
theorem jacDet_psiCanon (u : Fin 21 → ℝ) : jacDet psiCanon u = 1 := by
  unfold psiCanon
  exact jacDet_blockShear phiCanon keepCanon differentiable_phiCanon phiCanon_keep phiCanon_read u

/-- `Ψ` fixes every coordinate outside the block. -/
theorem psiCanon_apply_offblock (u : Fin 21 → ℝ) (d : Fin 21) (hd : keepCanon d) :
    psiCanon u d = u d := by
  unfold psiCanon blockShear
  simp only [Pi.add_apply, phiCanon_keep u d hd, add_zero]

/-! ## §2 — the per-type data -/

/-- The dominant monomial exponent `vm`. -/
def vmExpCanon : Fin 21 → ℕ := fun d => if d = 5 ∨ d = 6 ∨ d = 20 then 1 else 0

/-- `∏_d (u d)^(vmExpCanon d) = u 5 * u 6 * u 20`. -/
theorem prod_vmExpCanon (u : Fin 21 → ℝ) : (∏ d, (u d) ^ vmExpCanon d) = u 5 * u 6 * u 20 := by
  have h1 : ∀ d : Fin 21, u d ^ vmExpCanon d = if d = 5 ∨ d = 6 ∨ d = 20 then u d else 1 :=
    fun d => by simp only [vmExpCanon]; split_ifs <;> simp
  simp_rw [h1]
  rw [Finset.prod_ite, Finset.prod_const_one, mul_one,
    show Finset.filter (fun d : Fin 21 => d = 5 ∨ d = 6 ∨ d = 20) Finset.univ = {5, 6, 20} from by decide,
    Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_singleton]
  ring

/-- The 8 reg-seq `(row, col)` pairs (pattern B: columns `c = 0, 2`). -/
def pairsCanon : Finset (Fin 4 × Fin 3) :=
  {(0, 0), (0, 2), (1, 0), (1, 2), (2, 0), (2, 2), (3, 0), (3, 2)}

/-- The 8-element regular-sequence entry-index set `S`. -/
def Scanon : Finset (Fin (dvec (Fin.last 2) * dvec 0)) := pairsCanon.image finProdFinEquiv

/-- The straightening coordinate map on `(row, col)` pairs. -/
def zcPair : Fin 4 × Fin 3 → Fin 21 := fun p =>
  if p = (0, 0) then 0
  else if p = (0, 2) then 12
  else if p = (1, 0) then 2
  else if p = (1, 2) then 13
  else if p = (2, 0) then 3
  else if p = (2, 2) then 14
  else if p = (3, 0) then 4
  else 15

/-- The straightening coordinate map `zc`. -/
def zcCanon : Fin (dvec (Fin.last 2) * dvec 0) → Fin 21 := fun k => zcPair (finProdFinEquiv.symm k)

/-- The `jac`-free regular-sequence coordinate block `Z = zc '' S`. -/
def Zcanon : Finset (Fin 21) := {0, 2, 3, 4, 12, 13, 14, 15}

theorem hzc_inj : ∀ x ∈ Scanon, ∀ y ∈ Scanon, zcCanon x = zcCanon y → x = y := by decide

theorem hzc_img : Scanon.image zcCanon = Zcanon := by decide

/-! ## §3 — the 8 reg-seq entry identities -/

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 8000 in
set_option linter.unusedSimpArgs false in
set_option linter.style.maxHeartbeats false in
/-- Entry `(0,0)`, `zc = 0`. -/
theorem entry_00 (u : Fin 21 → ℝ) :
    coreGen dvec eWrap (finProdFinEquiv ((0 : Fin 4), (0 : Fin 3))) (gCanon (psiCanon u))
      = u 5 * u 6 * u 20 * u 0 := by
  rw [coreGen_eWrap_entry]
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
/-- Entry `(0,2)`, `zc = 12`. -/
theorem entry_02 (u : Fin 21 → ℝ) :
    coreGen dvec eWrap (finProdFinEquiv ((0 : Fin 4), (2 : Fin 3))) (gCanon (psiCanon u))
      = u 5 * u 6 * u 20 * u 12 := by
  rw [coreGen_eWrap_entry]
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
/-- Entry `(1,0)`, `zc = 2`. -/
theorem entry_10 (u : Fin 21 → ℝ) :
    coreGen dvec eWrap (finProdFinEquiv ((1 : Fin 4), (0 : Fin 3))) (gCanon (psiCanon u))
      = u 5 * u 6 * u 20 * u 2 := by
  rw [coreGen_eWrap_entry]
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
/-- Entry `(1,2)`, `zc = 13`. -/
theorem entry_12 (u : Fin 21 → ℝ) :
    coreGen dvec eWrap (finProdFinEquiv ((1 : Fin 4), (2 : Fin 3))) (gCanon (psiCanon u))
      = u 5 * u 6 * u 20 * u 13 := by
  rw [coreGen_eWrap_entry]
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
/-- Entry `(2,0)`, `zc = 3`. -/
theorem entry_20 (u : Fin 21 → ℝ) :
    coreGen dvec eWrap (finProdFinEquiv ((2 : Fin 4), (0 : Fin 3))) (gCanon (psiCanon u))
      = u 5 * u 6 * u 20 * u 3 := by
  rw [coreGen_eWrap_entry]
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
/-- Entry `(2,2)`, `zc = 14`. -/
theorem entry_22 (u : Fin 21 → ℝ) :
    coreGen dvec eWrap (finProdFinEquiv ((2 : Fin 4), (2 : Fin 3))) (gCanon (psiCanon u))
      = u 5 * u 6 * u 20 * u 14 := by
  rw [coreGen_eWrap_entry]
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
/-- Entry `(3,0)`, `zc = 4`. -/
theorem entry_30 (u : Fin 21 → ℝ) :
    coreGen dvec eWrap (finProdFinEquiv ((3 : Fin 4), (0 : Fin 3))) (gCanon (psiCanon u))
      = u 5 * u 6 * u 20 * u 4 := by
  rw [coreGen_eWrap_entry]
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
/-- Entry `(3,2)`, `zc = 15`. -/
theorem entry_32 (u : Fin 21 → ℝ) :
    coreGen dvec eWrap (finProdFinEquiv ((3 : Fin 4), (2 : Fin 3))) (gCanon (psiCanon u))
      = u 5 * u 6 * u 20 * u 15 := by
  rw [coreGen_eWrap_entry]
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
  rw [gFlat_idxCanon, prod_vmExpCanon]
  simp only [Scanon, Finset.mem_image] at hk
  obtain ⟨p, hp, rfl⟩ := hk
  simp only [zcCanon, Equiv.symm_apply_apply]
  fin_cases hp <;>
    first
      | exact entry_00 u | exact entry_02 u | exact entry_10 u | exact entry_12 u | exact entry_20 u | exact entry_22 u | exact entry_30 u | exact entry_32 u

/-! ## §4 — the assembled per-type domination -/

/-- **The over-vanishing product-germ domination (per-type FACT).** -/
theorem canon_domination (u : Fin 21 → ℝ) :
    monoSumSqGerm vmExpCanon Zcanon u
      ≤ sumSqFam (fun i ↦ coreGen dvec eWrap i ∘ (gFlat idxCanon ∘ psiCanon)) u :=
  monoSumSqGerm_le_of_regSeq_entries (S := Scanon) (zc := zcCanon) canon_hentry hzc_inj hzc_img u

/-! ## §5 — the folded Jacobian -/

set_option linter.unusedSimpArgs false in
/-- Every binding axis of `jacExp idxCanon` is outside the straightened block. -/
theorem hfix_jacExp (u : Fin 21 → ℝ) :
    ∀ d, 0 < jacExp idxCanon d → psiCanon u d = u d := by
  intro d hd
  apply psiCanon_apply_offblock u d
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    (intro h; subst h
     simp (config := { decide := true }) only [jacExp, idxCanon, Pi.add_apply,
       NativeJac334.single, sigmaC2Fs, Fin.isValue, Finset.mem_insert, Finset.mem_singleton,
       if_true, if_false, add_zero, zero_add, lt_self_iff_false] at hd)

/-- **The folded Jacobian.** -/
theorem canon_foldedJac (u : Fin 21 → ℝ) :
    |jacDet (gFlat idxCanon ∘ psiCanon) u| = jacWeight (jacExp idxCanon) u := by
  rw [jacDet_comp u (differentiable_gFlat idxCanon).differentiableAt
    differentiable_psiCanon.differentiableAt, abs_mul, jacDet_psiCanon, abs_one, mul_one,
    hjac_gFlat idxCanon (psiCanon u)]
  exact jacWeight_fixOn (jacExp idxCanon) (hfix_jacExp u)

/-! ## §6 — the CUBIC cover-transport (φ has a degree-3 term) -/

/-- **The cubic displacement bound** `‖φ x‖ ≤ 2·r³` for `r ≥ 1` (each block slot is a sum of two
products of ≤ 3 kept coords; `|quad| ≤ r² ≤ r³`, `|cubic| ≤ r³`). -/
theorem phiCanon_norm_bound {x : Fin 21 → ℝ} {r : ℝ} (hr1 : 1 ≤ r) (hx : ‖x‖ ≤ r) :
    ‖phiCanon x‖ ≤ 2 * r ^ 3 := by
  have hr0 : 0 ≤ r := by linarith
  have hr23 : r ^ 2 ≤ r ^ 3 := by nlinarith [sq_nonneg r, hr1]
  have habs : ∀ i : Fin 21, |x i| ≤ r := fun i => by
    rw [← Real.norm_eq_abs]; exact (norm_le_pi_norm x i).trans hx
  have hq : ∀ a b : Fin 21, |x a * x b| ≤ r ^ 3 := fun a b => by
    have h2 : |x a * x b| ≤ r ^ 2 := by
      rw [abs_mul, sq]; exact mul_le_mul (habs a) (habs b) (abs_nonneg _) hr0
    exact le_trans h2 hr23
  have hcube : ∀ a b c : Fin 21, |x a * x b * x c| ≤ r ^ 3 := fun a b c => by
    rw [abs_mul, abs_mul]
    calc |x a| * |x b| * |x c| ≤ r * r * r :=
          mul_le_mul (mul_le_mul (habs a) (habs b) (abs_nonneg _) hr0) (habs c) (abs_nonneg _)
            (by positivity)
      _ = r ^ 3 := by ring
  have slot : ∀ A B : ℝ, |A| ≤ r ^ 3 → |B| ≤ r ^ 3 → |(-(A + B))| ≤ 2 * r ^ 3 :=
    fun A B hA hB => by
      rw [abs_neg]
      calc |A + B| ≤ |A| + |B| := abs_add_le _ _
        _ ≤ r ^ 3 + r ^ 3 := add_le_add hA hB
        _ = 2 * r ^ 3 := by ring
  rw [pi_norm_le_iff_of_nonneg (by positivity)]
  intro i
  rw [Real.norm_eq_abs]
  by_cases h12 : i = 12
  · rw [h12, show phiCanon x 12 = -(x 0 * x 11 + x 16 * x 5 * x 7) from rfl]
    exact slot _ _ (hq 0 11) (hcube 16 5 7)
  by_cases h13 : i = 13
  · rw [h13, show phiCanon x 13 = -(x 11 * x 2 + x 17 * x 5 * x 7) from rfl]
    exact slot _ _ (hq 11 2) (hcube 17 5 7)
  by_cases h14 : i = 14
  · rw [h14, show phiCanon x 14 = -(x 11 * x 3 + x 18 * x 5 * x 7) from rfl]
    exact slot _ _ (hq 11 3) (hcube 18 5 7)
  by_cases h15 : i = 15
  · rw [h15, show phiCanon x 15 = -(x 11 * x 4 + x 19 * x 5 * x 7) from rfl]
    exact slot _ _ (hq 11 4) (hcube 19 5 7)
  · rw [phiCanon_keep x i ⟨h12, h13, h14, h15⟩, abs_zero]; positivity

/-- **The canonical cubic cover-transport** — `closedBall 0 r ⊆ Ψ '' closedBall 0 (r + 2·r³)` (`r ≥ 1`). -/
theorem psiCanon_cubic_cover {r : ℝ} (hr1 : 1 ≤ r) :
    closedBall (0 : Fin 21 → ℝ) r ⊆ psiCanon '' closedBall 0 (r + 2 * r ^ 3) := by
  unfold psiCanon
  exact blockShear_covers_cubic keepCanon phiCanon_keep phiCanon_read
    (fun x hx => phiCanon_norm_bound hr1 hx)

/-- **The folded-chart cover survives the cubic fold.** -/
theorem image_comp_psiCanon_cubic_superset (g : (Fin 21 → ℝ) → (Fin 21 → ℝ)) {r : ℝ}
    (hr1 : 1 ≤ r) :
    g '' closedBall 0 r ⊆ (g ∘ psiCanon) '' closedBall 0 (r + 2 * r ^ 3) := by
  calc g '' closedBall (0 : Fin 21 → ℝ) r
      ⊆ g '' (psiCanon '' closedBall 0 (r + 2 * r ^ 3)) :=
        Set.image_mono (psiCanon_cubic_cover hr1)
    _ = (g ∘ psiCanon) '' closedBall 0 (r + 2 * r ^ 3) := (Set.image_comp g psiCanon _).symm

end DLNFibre.DLN.Aoyagi.OverVanishB_20_6_5
