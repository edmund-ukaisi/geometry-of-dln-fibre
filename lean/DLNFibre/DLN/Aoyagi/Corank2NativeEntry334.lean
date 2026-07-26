import DLNFibre.DLN.Aoyagi.Corank2NativeJac334
import DLNFibre.DLN.Aoyagi.Corank2CoreGenWrap

/-!
# `DLN.Aoyagi.Corank2NativeEntry334` — the uniform `u_{p1}` factor-out of the leaf loss (C-substrate)

The reusable uniform step for the value (`hentry`/`hsandwich`) seats: the node-1-pivot coordinate
`u_{p1}` factors out of EVERY one of the 12 `coreGen` entries of the whole-conjugate leaf chart
`gFlat idx`, because the loss reads `A0` on EXACTLY the outer blow-up centre `S1` and `A1` on its
spectator block `{8,…,19}`.

* `A0 (gFlat idx w) = w_{p1} • A0 (Function.update (gInner idx w) p1 1)` — `u_{p1}` is a clean
  scalar factor of the whole `A0` (the outer `blockBlowupMap S1 p1` multiplies every `S1\{p1}`
  coordinate by `w_{p1}` and pins `p1 ↦ w_{p1}`; the pivot slot becomes literal `1`).
* `A1 (gFlat idx w) = A1 (gInner idx w)` — the `A1`-block `{8,…,19}` is disjoint from `S1`, so those
  coordinates are spectators of the outer blow-up (no `u_{p1}`).

So `coreGen k (gFlat idx w) = w_{p1} · (A1 (gInner idx w) · A0'')_{k}` (the value seat's first vm
factor, uniform in `k`). The FURTHER per-type factors `u_{p2}` / `u_{p3}` come from
`blockBlowupMap (σC1 p1) p2` / `blockBlowupMap (σC2 p1) p3` inside `gInner` — the value seat's work.

`gInner idx w = nativeChart1 p1 (bb (σC1 p1) p2 (bb (σC2 p1) p3 w))` — the leaf chart before the outer
`S1` blow-up (`gFlat idx w = blockBlowupMap S1 p1 (gInner idx w)`). Additive on the reviewed
`(A-rework)`/`(C)` content.
-/

open MeasureTheory Set Metric
open DLNFibre.Core.Aoyagi
open DLNFibre.DLN.Aoyagi.NativePerm334
open DLNFibre.DLN.Aoyagi.NativeFan334
open DLNFibre.DLN.Aoyagi.NativeValue334
open DLNFibre.DLN.Aoyagi.NativeJac334
open DLNFibre.DLN.Aoyagi.Corank2CoreGenWrap

namespace DLNFibre.DLN.Aoyagi.NativeEntry334

/-- **The block-blow-up centre factoring**: on a centre coordinate, the pivot factors out —
`blockBlowupMap S p v c = v_p · (update v p 1)_c` for `c ∈ S` (pins `c = p ↦ v_p·1 = v_p`, and
`c ∈ S\{p} ↦ v_p·v_c`). General `Fin D`; the mechanism behind the uniform `u_{p1}` factor-out. -/
theorem blockBlowupMap_center_factor {D : ℕ} (S : Finset (Fin D)) (p : Fin D) (v : Fin D → ℝ)
    {c : Fin D} (hc : c ∈ S) :
    blockBlowupMap S p v c = v p * Function.update v p 1 c := by
  by_cases hcp : c = p
  · subst hcp; simp [blockBlowupMap, Function.update_self]
  · rw [blockBlowupMap, if_neg hcp, if_pos hc, Function.update_of_ne hcp, mul_comm]

/-- **The inner composite** of the whole-conjugate leaf chart — everything before the outer `S1`
blow-up. -/
noncomputable def gInner (idx : Idx) (w : Fin 21 → ℝ) : Fin 21 → ℝ :=
  nativeChart1 idx.1.1 (blockBlowupMap (sigmaC1Fs idx.1.1) idx.2.1.1
    (blockBlowupMap (sigmaC2Fs idx.1.1) idx.2.2.1 w))

/-- `gFlat idx w = blockBlowupMap S1 p1 (gInner idx w)` (the `∘ id`s drop). -/
theorem gFlat_eq_bb_gInner (idx : Idx) (w : Fin 21 → ℝ) :
    gFlat idx w = blockBlowupMap S1 idx.1.1 (gInner idx w) := by
  simp only [gFlat, gInner, Function.comp_apply, id_eq]

/-- **The pivot coordinate is fixed through the inner composite** — `(gInner idx w) p1 = w p1`
(nativeChart1 fixes `p1`; the two inner blow-ups are spectators at `p1`). So `A0''`'s pivot slot is
LITERAL `w p1` (⟹ `1` after the `update`), never `w p1 / w p1`. -/
theorem gInner_pivot (idx : Idx) (w : Fin 21 → ℝ) : gInner idx w idx.1.1 = w idx.1.1 := by
  rw [gInner, nativeChart1_fix_pivot idx.1.1 idx.1.2,
    blockBlowupMap_offCenter_eq _ _ _ (p1_notMem_sigmaC1Fs idx.1.1 idx.1.2),
    blockBlowupMap_offCenter_eq _ _ _ (p1_notMem_sigmaC2Fs idx.1.1 idx.1.2)]

/-- **The uniform `u_{p1}` factor-out of `A0`.** `A0 (gFlat idx w) = w_{p1} • A0''` where
`A0'' = A0 (update (gInner idx w) p1 1)` (the `A0`-pattern read of the inner composite with the pivot
slot normalised to `1`). Because `A0` reads exactly `S1` (the outer blow-up centre), `u_{p1}` is a
clean scalar factor of the whole matrix — hence of all 12 `coreGen` entries. -/
theorem A0_gFlat_factor (idx : Idx) (w : Fin 21 → ℝ) :
    A0 (gFlat idx w) = w idx.1.1 • A0 (Function.update (gInner idx w) idx.1.1 1) := by
  rw [gFlat_eq_bb_gInner]
  ext a b
  fin_cases a <;> fin_cases b <;>
    (simp only [A0, Matrix.smul_apply, smul_eq_mul, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.tail_cons,
      Matrix.head_cons, Matrix.head_fin_const, Matrix.cons_val_fin_one, Matrix.empty_val',
      Fin.reduceFinMk, Fin.reduceEq] <;>
     rw [blockBlowupMap_center_factor S1 idx.1.1 (gInner idx w) (by decide), gInner_pivot])

/-- **The `A1`-block is a spectator of the outer blow-up.** `A1 (gFlat idx w) = A1 (gInner idx w)` —
the `A1` coordinates `{8,…,19}` are disjoint from `S1`, so the outer `blockBlowupMap S1 p1` fixes
them (no `u_{p1}` on `A1`). -/
theorem A1_gFlat_spectator (idx : Idx) (w : Fin 21 → ℝ) :
    A1 (gFlat idx w) = A1 (gInner idx w) := by
  rw [gFlat_eq_bb_gInner]
  ext a b
  fin_cases a <;> fin_cases b <;>
    (simp only [A1, Fin.reduceFinMk, Nat.reduceAdd, Nat.reduceMul] <;>
     rw [blockBlowupMap_offCenter_eq S1 idx.1.1 (gInner idx w) (by decide)])

-- Forced axiom gate: the uniform `u_{p1}` factor-out rests only on `[propext, Classical.choice,
-- Quot.sound]`.
#assert_banked_clean_batch [blockBlowupMap_center_factor, gFlat_eq_bb_gInner, gInner_pivot,
  A0_gFlat_factor, A1_gFlat_spectator]

end DLNFibre.DLN.Aoyagi.NativeEntry334
