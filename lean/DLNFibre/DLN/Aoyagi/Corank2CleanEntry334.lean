import DLNFibre.DLN.Aoyagi.Corank2CleanEntryBase334

/-!
# `DLN.Aoyagi.Corank2CleanEntry334` — the CLEAN-144 per-pivot entry-equalities (the (B) deliverable)

The exact per-chart survivor entry-equality for the CLEAN-144 leaves:
`coreGen dvec eWrap (k0 c) (gFin c w) = w (pivot1 c) · w (pivot2 c) = ∏_d (w d)^(ek₀ c d)`.
This discharges the `hentry` field of `rlctAt_coreGen334_ge_four_of_survivor_entries` (CLEAN-144).
-/

open DLNFibre.Core.Aoyagi
open DLNFibre.DLN.Aoyagi
open DLNFibre.DLN.Aoyagi.NativeFan334
open DLNFibre.DLN.Aoyagi.NativeValue334
open DLNFibre.DLN.Aoyagi.NativePerm334
open DLNFibre.DLN.Aoyagi.NativeShear334
open DLNFibre.DLN.Aoyagi.Corank2CoreGenWrap

namespace DLNFibre.DLN.Aoyagi.CleanHentry334

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 8000 in
/-- Pivot `p1 = 20` (canonical): the clean node-2 pivots (`(20,p2) ∈ cleanPairs`), all node-3. -/
theorem clean_entry_p20 (p2 p3 : Fin 21) (hp2 : p2 ∈ sigmaC1Fs 20)
    (hp3 : p3 ∈ sigmaC2Fs 20) (hcl : ((20 : Fin 21), p2) ∈ cleanPairs) (w : Fin 21 → ℝ) :
    coreGen dvec eWrap (finProdFinEquiv (ijpair 20 p2)) (leafMap 20 p2 p3 w) = w 20 * w p2 := by
  fin_cases hp2 <;>
    first
    | exact absurd hcl (by decide)
    | (fin_cases hp3 <;>
        rw [coreGen_eWrap_entry] <;>
        simp only [Equiv.symm_apply_apply, ijpair, Fin.isValue] <;>
        rw [Matrix.mul_apply, Fin.sum_univ_three] <;>
        simp (config := { decide := true }) only [leafMap, A0, A1_00, A1_01, A1_02, A1_10, A1_11,
          A1_12, A1_20, A1_21, A1_22, A1_30, A1_31, A1_32,
          nativeChart1, nativeSel, nativePerm, blockShear, blockBlowupMap,
          sigmaC1Fs, sigmaC2Fs, qdisp, sterm, t1P20, t2P20,
          Function.comp_apply, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
          Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_fin_const,
          cpermS20, Equiv.ofBijective_apply, cperm20,
          Pi.add_apply, Fin.isValue, Option.elim, if_true, if_false, ite_true, ite_false] <;>
        ring)

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 8000 in
/-- Pivot `p1 = 0`. -/
theorem clean_entry_p0 (p2 p3 : Fin 21) (hp2 : p2 ∈ sigmaC1Fs 0)
    (hp3 : p3 ∈ sigmaC2Fs 0) (hcl : ((0 : Fin 21), p2) ∈ cleanPairs) (w : Fin 21 → ℝ) :
    coreGen dvec eWrap (finProdFinEquiv (ijpair 0 p2)) (leafMap 0 p2 p3 w) = w 0 * w p2 := by
  fin_cases hp2 <;>
    first
    | exact absurd hcl (by decide)
    | (fin_cases hp3 <;>
        rw [coreGen_eWrap_entry] <;>
        simp only [Equiv.symm_apply_apply, ijpair, Fin.isValue] <;>
        rw [Matrix.mul_apply, Fin.sum_univ_three] <;>
        simp (config := { decide := true }) only [leafMap, A0, A1_00, A1_01, A1_02, A1_10, A1_11,
          A1_12, A1_20, A1_21, A1_22, A1_30, A1_31, A1_32,
          nativeChart1, nativeSel, nativePerm, blockShear, blockBlowupMap,
          sigmaC1Fs, sigmaC2Fs, qdisp, sterm, t1P0, t2P0,
          Function.comp_apply, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
          Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_fin_const,
          cpermS0, Equiv.ofBijective_apply, cperm0,
          Pi.add_apply, Fin.isValue, Option.elim, if_true, if_false, ite_true, ite_false] <;>
        ring)

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 8000 in
/-- Pivot `p1 = 1`. -/
theorem clean_entry_p1 (p2 p3 : Fin 21) (hp2 : p2 ∈ sigmaC1Fs 1)
    (hp3 : p3 ∈ sigmaC2Fs 1) (hcl : ((1 : Fin 21), p2) ∈ cleanPairs) (w : Fin 21 → ℝ) :
    coreGen dvec eWrap (finProdFinEquiv (ijpair 1 p2)) (leafMap 1 p2 p3 w) = w 1 * w p2 := by
  fin_cases hp2 <;>
    first
    | exact absurd hcl (by decide)
    | (fin_cases hp3 <;>
        rw [coreGen_eWrap_entry] <;>
        simp only [Equiv.symm_apply_apply, ijpair, Fin.isValue] <;>
        rw [Matrix.mul_apply, Fin.sum_univ_three] <;>
        simp (config := { decide := true }) only [leafMap, A0, A1_00, A1_01, A1_02, A1_10, A1_11,
          A1_12, A1_20, A1_21, A1_22, A1_30, A1_31, A1_32,
          nativeChart1, nativeSel, nativePerm, blockShear, blockBlowupMap,
          sigmaC1Fs, sigmaC2Fs, qdisp, sterm, t1P1, t2P1,
          Function.comp_apply, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
          Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_fin_const,
          cpermS1, Equiv.ofBijective_apply, cperm1,
          Pi.add_apply, Fin.isValue, Option.elim, if_true, if_false, ite_true, ite_false] <;>
        ring)

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 8000 in
/-- Pivot `p1 = 2`. -/
theorem clean_entry_p2 (p2 p3 : Fin 21) (hp2 : p2 ∈ sigmaC1Fs 2)
    (hp3 : p3 ∈ sigmaC2Fs 2) (hcl : ((2 : Fin 21), p2) ∈ cleanPairs) (w : Fin 21 → ℝ) :
    coreGen dvec eWrap (finProdFinEquiv (ijpair 2 p2)) (leafMap 2 p2 p3 w) = w 2 * w p2 := by
  fin_cases hp2 <;>
    first
    | exact absurd hcl (by decide)
    | (fin_cases hp3 <;>
        rw [coreGen_eWrap_entry] <;>
        simp only [Equiv.symm_apply_apply, ijpair, Fin.isValue] <;>
        rw [Matrix.mul_apply, Fin.sum_univ_three] <;>
        simp (config := { decide := true }) only [leafMap, A0, A1_00, A1_01, A1_02, A1_10, A1_11,
          A1_12, A1_20, A1_21, A1_22, A1_30, A1_31, A1_32,
          nativeChart1, nativeSel, nativePerm, blockShear, blockBlowupMap,
          sigmaC1Fs, sigmaC2Fs, qdisp, sterm, t1P2, t2P2,
          Function.comp_apply, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
          Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_fin_const,
          cpermS2, Equiv.ofBijective_apply, cperm2,
          Pi.add_apply, Fin.isValue, Option.elim, if_true, if_false, ite_true, ite_false] <;>
        ring)

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 8000 in
/-- Pivot `p1 = 3`. -/
theorem clean_entry_p3 (p2 p3 : Fin 21) (hp2 : p2 ∈ sigmaC1Fs 3)
    (hp3 : p3 ∈ sigmaC2Fs 3) (hcl : ((3 : Fin 21), p2) ∈ cleanPairs) (w : Fin 21 → ℝ) :
    coreGen dvec eWrap (finProdFinEquiv (ijpair 3 p2)) (leafMap 3 p2 p3 w) = w 3 * w p2 := by
  fin_cases hp2 <;>
    first
    | exact absurd hcl (by decide)
    | (fin_cases hp3 <;>
        rw [coreGen_eWrap_entry] <;>
        simp only [Equiv.symm_apply_apply, ijpair, Fin.isValue] <;>
        rw [Matrix.mul_apply, Fin.sum_univ_three] <;>
        simp (config := { decide := true }) only [leafMap, A0, A1_00, A1_01, A1_02, A1_10, A1_11,
          A1_12, A1_20, A1_21, A1_22, A1_30, A1_31, A1_32,
          nativeChart1, nativeSel, nativePerm, blockShear, blockBlowupMap,
          sigmaC1Fs, sigmaC2Fs, qdisp, sterm, t1P3, t2P3,
          Function.comp_apply, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
          Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_fin_const,
          cpermS3, Equiv.ofBijective_apply, cperm3,
          Pi.add_apply, Fin.isValue, Option.elim, if_true, if_false, ite_true, ite_false] <;>
        ring)

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 8000 in
/-- Pivot `p1 = 4`. -/
theorem clean_entry_p4 (p2 p3 : Fin 21) (hp2 : p2 ∈ sigmaC1Fs 4)
    (hp3 : p3 ∈ sigmaC2Fs 4) (hcl : ((4 : Fin 21), p2) ∈ cleanPairs) (w : Fin 21 → ℝ) :
    coreGen dvec eWrap (finProdFinEquiv (ijpair 4 p2)) (leafMap 4 p2 p3 w) = w 4 * w p2 := by
  fin_cases hp2 <;>
    first
    | exact absurd hcl (by decide)
    | (fin_cases hp3 <;>
        rw [coreGen_eWrap_entry] <;>
        simp only [Equiv.symm_apply_apply, ijpair, Fin.isValue] <;>
        rw [Matrix.mul_apply, Fin.sum_univ_three] <;>
        simp (config := { decide := true }) only [leafMap, A0, A1_00, A1_01, A1_02, A1_10, A1_11,
          A1_12, A1_20, A1_21, A1_22, A1_30, A1_31, A1_32,
          nativeChart1, nativeSel, nativePerm, blockShear, blockBlowupMap,
          sigmaC1Fs, sigmaC2Fs, qdisp, sterm, t1P4, t2P4,
          Function.comp_apply, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
          Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_fin_const,
          cpermS4, Equiv.ofBijective_apply, cperm4,
          Pi.add_apply, Fin.isValue, Option.elim, if_true, if_false, ite_true, ite_false] <;>
        ring)

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 8000 in
/-- Pivot `p1 = 5`. -/
theorem clean_entry_p5 (p2 p3 : Fin 21) (hp2 : p2 ∈ sigmaC1Fs 5)
    (hp3 : p3 ∈ sigmaC2Fs 5) (hcl : ((5 : Fin 21), p2) ∈ cleanPairs) (w : Fin 21 → ℝ) :
    coreGen dvec eWrap (finProdFinEquiv (ijpair 5 p2)) (leafMap 5 p2 p3 w) = w 5 * w p2 := by
  fin_cases hp2 <;>
    first
    | exact absurd hcl (by decide)
    | (fin_cases hp3 <;>
        rw [coreGen_eWrap_entry] <;>
        simp only [Equiv.symm_apply_apply, ijpair, Fin.isValue] <;>
        rw [Matrix.mul_apply, Fin.sum_univ_three] <;>
        simp (config := { decide := true }) only [leafMap, A0, A1_00, A1_01, A1_02, A1_10, A1_11,
          A1_12, A1_20, A1_21, A1_22, A1_30, A1_31, A1_32,
          nativeChart1, nativeSel, nativePerm, blockShear, blockBlowupMap,
          sigmaC1Fs, sigmaC2Fs, qdisp, sterm, t1P5, t2P5,
          Function.comp_apply, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
          Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_fin_const,
          cpermS5, Equiv.ofBijective_apply, cperm5,
          Pi.add_apply, Fin.isValue, Option.elim, if_true, if_false, ite_true, ite_false] <;>
        ring)

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 8000 in
/-- Pivot `p1 = 6`. -/
theorem clean_entry_p6 (p2 p3 : Fin 21) (hp2 : p2 ∈ sigmaC1Fs 6)
    (hp3 : p3 ∈ sigmaC2Fs 6) (hcl : ((6 : Fin 21), p2) ∈ cleanPairs) (w : Fin 21 → ℝ) :
    coreGen dvec eWrap (finProdFinEquiv (ijpair 6 p2)) (leafMap 6 p2 p3 w) = w 6 * w p2 := by
  fin_cases hp2 <;>
    first
    | exact absurd hcl (by decide)
    | (fin_cases hp3 <;>
        rw [coreGen_eWrap_entry] <;>
        simp only [Equiv.symm_apply_apply, ijpair, Fin.isValue] <;>
        rw [Matrix.mul_apply, Fin.sum_univ_three] <;>
        simp (config := { decide := true }) only [leafMap, A0, A1_00, A1_01, A1_02, A1_10, A1_11,
          A1_12, A1_20, A1_21, A1_22, A1_30, A1_31, A1_32,
          nativeChart1, nativeSel, nativePerm, blockShear, blockBlowupMap,
          sigmaC1Fs, sigmaC2Fs, qdisp, sterm, t1P6, t2P6,
          Function.comp_apply, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
          Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_fin_const,
          cpermS6, Equiv.ofBijective_apply, cperm6,
          Pi.add_apply, Fin.isValue, Option.elim, if_true, if_false, ite_true, ite_false] <;>
        ring)

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 8000 in
/-- Pivot `p1 = 7`. -/
theorem clean_entry_p7 (p2 p3 : Fin 21) (hp2 : p2 ∈ sigmaC1Fs 7)
    (hp3 : p3 ∈ sigmaC2Fs 7) (hcl : ((7 : Fin 21), p2) ∈ cleanPairs) (w : Fin 21 → ℝ) :
    coreGen dvec eWrap (finProdFinEquiv (ijpair 7 p2)) (leafMap 7 p2 p3 w) = w 7 * w p2 := by
  fin_cases hp2 <;>
    first
    | exact absurd hcl (by decide)
    | (fin_cases hp3 <;>
        rw [coreGen_eWrap_entry] <;>
        simp only [Equiv.symm_apply_apply, ijpair, Fin.isValue] <;>
        rw [Matrix.mul_apply, Fin.sum_univ_three] <;>
        simp (config := { decide := true }) only [leafMap, A0, A1_00, A1_01, A1_02, A1_10, A1_11,
          A1_12, A1_20, A1_21, A1_22, A1_30, A1_31, A1_32,
          nativeChart1, nativeSel, nativePerm, blockShear, blockBlowupMap,
          sigmaC1Fs, sigmaC2Fs, qdisp, sterm, t1P7, t2P7,
          Function.comp_apply, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
          Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_fin_const,
          cpermS7, Equiv.ofBijective_apply, cperm7,
          Pi.add_apply, Fin.isValue, Option.elim, if_true, if_false, ite_true, ite_false] <;>
        ring)

-- Forced axiom gate: the 9 per-pivot entry-equalities rest only on
-- `[propext, Classical.choice, Quot.sound]`.
#assert_banked_clean_batch [clean_entry_p0, clean_entry_p1, clean_entry_p2, clean_entry_p3,
  clean_entry_p4, clean_entry_p5, clean_entry_p6, clean_entry_p7, clean_entry_p20]

end DLNFibre.DLN.Aoyagi.CleanHentry334
