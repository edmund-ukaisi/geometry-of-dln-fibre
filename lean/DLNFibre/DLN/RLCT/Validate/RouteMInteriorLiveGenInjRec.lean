import DLNFibre.DLN.RLCT.Validate.RouteMInteriorLiveGenDet
import DLNFibre.DLN.RLCT.Validate.RouteMInteriorLiveGenSchurGate
import DLNFibre.DLN.RLCT.Validate.RouteMHmapGen
import DLNFibre.DLN.RLCT.Validate.RouteMProjV0Gate
import DLNFibre.DLN.RLCT.Validate.RouteMFlatBlockLE

/-!
# `RouteMInteriorLiveGenInjRec` — the general-`L` boundary-factor VALUE recovery (route (a))

The `BchartLeafGen`-recovery half of the general-`L` interior-chart injectivity, built from chart's
committed map (`RouteMInteriorLiveGenInj` module note): a TRIANGULAR forward-substitution over
boundaries `s : Fin L`, of which the `L = 2` `interiorLive_BparamsLeaf_injOn` is the 2-node instance.
This module is UPSTREAM of `RouteMInteriorLiveGenInj`, which consumes `BchartLeafGen_injOn_recover` to
close its `interiorLive_BchartLeaf_injOnGen`.

Route (a) — slot-disjoint faithful decode, eInGen-FREE (independent of the `eihd_hD_gen` det crux):

From `BchartLeafGen y = BchartLeafGen y'`, peel `paramsEquivFlat` (injective) to `BparamsLeafGen y =
BparamsLeafGen y'`, then per-layer `reindexLs_BparamsLeafGen` (banked) gives the chain-layer equality
`Agen 1 (B y) s.val = Agen 1 (B y') s.val` for every `s : Fin L` (`Agen_eq_of_BchartLeafGen_eq`).

Per boundary `s`, `Agen … s = chainA(Nblk s, Wblk s, Cgen(s+1)) = [Cgen(s+1) − Nblk s·Wblk s ; Wblk s]`
(banked `chainA_apply_castAdd`/`_natAdd`):
* the lift (`natAdd`) rows recover `Wblk s` (`Wblk_eq_of_Agen_eq`);
* the kept (`castAdd`) rows, given `Nblk s (= readN ⟨s−1⟩)` and `Wblk s` already recovered, recover
  `Cgen(s+1)` (`Cgen_eq_of_Agen_eq`);
* `Cgen(s+1)`, interior, is `schurFrameProd (readK/X/N/E ⟨s⟩)` (banked `Cgen_live_interior_…`),
  bridged to `schurFrameMap` (`flatBlock_schurFrameMap_eq_gen`) + `flatBlockLE.injective`, then inverted
  by `schurFrameMap_inj_of_det_ne_zero_gen` with `det K_s ≠ 0` (the shared gate `detK_ne_zero_gen`) to
  recover the frame readers (`frameRecoverGen`); the leaf `Cgen(L)` is `rfinDirectGen`.

A final `funext q; cases chartIdxEquiv q` (mirroring `kLDU_injStep2Gen`) upgrades the per-boundary
reader equality to `y = y'` (`BchartLeafGen_injOn_recover`) — eInGen-FREE.

Axiom-clean `[propext, Classical.choice, Quot.sound]` (matrix algebra + the shared gate; no analysis).
-/

open Matrix
open scoped BigOperators

namespace DLNFibre.DLN.RLCT

variable {L : ℕ}

/-- **The Schur frame map is injective when `K` is nonsingular** (general, network-free). `schurFrameMap
z = (K, K·N, (X·K, X·K·N + E))`; given `K.det ≠ 0`, the four blocks recover `(K,N,X,E)`. A local general
copy (the `L = 2` `RouteMInteriorLiveContract.schurFrameMap_inj_of_det_ne_zero` is stranded in the
`Fin 2`-pinned module; the statement is `{t r c}`-general). -/
theorem schurFrameMap_inj_of_det_ne_zero_gen {t r c : ℕ} {z z' : SchurInc t r c}
    (hK : z.1.det ≠ 0) (h : schurFrameMap z = schurFrameMap z') : z = z' := by
  obtain ⟨K, N, X, E⟩ := z
  obtain ⟨K', N', X', E'⟩ := z'
  simp only [schurFrameMap, Prod.mk.injEq] at h
  obtain ⟨hKK, hKN, hXK, hE⟩ := h
  subst hKK
  have hKunit : IsUnit K.det := isUnit_iff_ne_zero.mpr (by simpa using hK)
  have hN : N = N' := by
    have hh : K⁻¹ * (K * N) = K⁻¹ * (K * N') := by rw [hKN]
    rwa [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul K hKunit,
      Matrix.one_mul, Matrix.one_mul] at hh
  have hX : X = X' := by
    have hh : X * K * K⁻¹ = X' * K * K⁻¹ := by rw [hXK]
    rwa [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_nonsing_inv K hKunit,
      Matrix.mul_one, Matrix.mul_one] at hh
  subst hN; subst hX
  have hEeq : E = E' := add_left_cancel hE
  subst hEeq
  rfl

/-! ## Step 1 — the chain-layer equality from `BchartLeafGen`-equality -/

/-- **`Agen`-equality from `BchartLeafGen`-equality.** `BchartLeafGen y = BchartLeafGen y'` ⟹ the
chain layer `Agen 1 (B y) s.val = Agen 1 (B y') s.val` at every boundary `s : Fin L`. Peel
`paramsEquivFlat` (injective), then per-layer `reindexLs_BparamsLeafGen` + reindex injectivity. -/
theorem Agen_eq_of_BchartLeafGen_eq (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M))
    (y y' : Fin (routeMAmbient M) → ℝ)
    (heq : BchartLeafGen M ha y = BchartLeafGen M ha y') (s : Fin L) :
    Agen 1 M (tach M) (genBlkFlatLive M (tach M) ha (rfinDirectGen M ha y) y)
        (hleStruct M (tach M) ha) s.val
      = Agen 1 M (tach M) (genBlkFlatLive M (tach M) ha (rfinDirectGen M ha y') y')
          (hleStruct M (tach M) ha) s.val := by
  have hparams : BparamsLeafGen M ha y = BparamsLeafGen M ha y' :=
    (paramsEquivFlat M).injective heq
  have hs : (BparamsLeafGen M ha y s : Matrix (Fin (M (s.castSucc))) (Fin (M (s.succ))) ℝ)
      = BparamsLeafGen M ha y' s := congrFun hparams s
  have hy := reindexLs_BparamsLeafGen M ha y s
  have hy' := reindexLs_BparamsLeafGen M ha y' s
  rw [← hy, ← hy'] at hs
  exact (Matrix.reindexLinearEquiv ℝ ℝ _ _).injective hs

/-! ## Step 2 — the per-boundary block extraction (`Wblk` natAdd rows, `Cgen` castAdd rows) -/

/-- Local abbreviation: the live boundary-factor block data at `y` (radial `1`, leaf `rfinDirectGen`). -/
private noncomputable abbrev Bof (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M))
    (y : Fin (routeMAmbient M) → ℝ) : GenBlk M (tach M) :=
  genBlkFlatLive M (tach M) ha (rfinDirectGen M ha y) y

/-- **The lift block `Wblk s` is recovered from the `natAdd` rows of `Agen s`.** `Agen 1 (B y) s =
Agen 1 (B y') s` ⟹ `(B y).Wblk s.val = (B y').Wblk s.val` — read off the lower (`natAdd`) rows via
`chainA_apply_natAdd`. -/
theorem Wblk_eq_of_Agen_eq (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M))
    (y y' : Fin (routeMAmbient M) → ℝ) (s : Fin L)
    (hA : Agen 1 M (tach M) (Bof M ha y) (hleStruct M (tach M) ha) s.val
        = Agen 1 M (tach M) (Bof M ha y') (hleStruct M (tach M) ha) s.val) :
    (Bof M ha y).Wblk s.val = (Bof M ha y').Wblk s.val := by
  ext a j
  have hAe : chainA (genWidthEq M (tach M) (hleStruct M (tach M) ha) s.val s.isLt)
        ((Bof M ha y).Nblk s.val) ((Bof M ha y).Wblk s.val)
        (Cgen 1 M (tach M) (Bof M ha y) (hleStruct M (tach M) ha) (s.val + 1))
      = chainA (genWidthEq M (tach M) (hleStruct M (tach M) ha) s.val s.isLt)
        ((Bof M ha y').Nblk s.val) ((Bof M ha y').Wblk s.val)
        (Cgen 1 M (tach M) (Bof M ha y') (hleStruct M (tach M) ha) (s.val + 1)) := by
    rw [show chainA (genWidthEq M (tach M) (hleStruct M (tach M) ha) s.val s.isLt)
          ((Bof M ha y).Nblk s.val) ((Bof M ha y).Wblk s.val)
          (Cgen 1 M (tach M) (Bof M ha y) (hleStruct M (tach M) ha) (s.val + 1))
        = Agen 1 M (tach M) (Bof M ha y) (hleStruct M (tach M) ha) s.val from
        (by rw [Agen, dif_pos s.isLt]),
      show chainA (genWidthEq M (tach M) (hleStruct M (tach M) ha) s.val s.isLt)
          ((Bof M ha y').Nblk s.val) ((Bof M ha y').Wblk s.val)
          (Cgen 1 M (tach M) (Bof M ha y') (hleStruct M (tach M) ha) (s.val + 1))
        = Agen 1 M (tach M) (Bof M ha y') (hleStruct M (tach M) ha) s.val from
        (by rw [Agen, dif_pos s.isLt]), hA]
  have h1 := congrFun (congrFun hAe (Fin.cast
      (genWidthEq M (tach M) (hleStruct M (tach M) ha) s.val s.isLt)
      (Fin.natAdd (Text M (tach M) (s.val + 1)) a))) j
  rwa [chainA_apply_natAdd, chainA_apply_natAdd] at h1

/-- **The transition block `Cgen (s+1)` is recovered from the `castAdd` rows of `Agen s`**, given the
`Nblk s`/`Wblk s` agreement (so the `− Nblk s · Wblk s` subtraction terms match on both sides). Read
off the upper (`castAdd`) rows via `chainA_apply_castAdd`, then add back the matched `Nblk·Wblk`. -/
theorem Cgen_eq_of_Agen_eq (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M))
    (y y' : Fin (routeMAmbient M) → ℝ) (s : Fin L)
    (hA : Agen 1 M (tach M) (Bof M ha y) (hleStruct M (tach M) ha) s.val
        = Agen 1 M (tach M) (Bof M ha y') (hleStruct M (tach M) ha) s.val)
    (hN : (Bof M ha y).Nblk s.val = (Bof M ha y').Nblk s.val)
    (hW : (Bof M ha y).Wblk s.val = (Bof M ha y').Wblk s.val) :
    Cgen 1 M (tach M) (Bof M ha y) (hleStruct M (tach M) ha) (s.val + 1)
      = Cgen 1 M (tach M) (Bof M ha y') (hleStruct M (tach M) ha) (s.val + 1) := by
  have hAe : chainA (genWidthEq M (tach M) (hleStruct M (tach M) ha) s.val s.isLt)
        ((Bof M ha y).Nblk s.val) ((Bof M ha y).Wblk s.val)
        (Cgen 1 M (tach M) (Bof M ha y) (hleStruct M (tach M) ha) (s.val + 1))
      = chainA (genWidthEq M (tach M) (hleStruct M (tach M) ha) s.val s.isLt)
        ((Bof M ha y').Nblk s.val) ((Bof M ha y').Wblk s.val)
        (Cgen 1 M (tach M) (Bof M ha y') (hleStruct M (tach M) ha) (s.val + 1)) := by
    rw [show chainA (genWidthEq M (tach M) (hleStruct M (tach M) ha) s.val s.isLt)
          ((Bof M ha y).Nblk s.val) ((Bof M ha y).Wblk s.val)
          (Cgen 1 M (tach M) (Bof M ha y) (hleStruct M (tach M) ha) (s.val + 1))
        = Agen 1 M (tach M) (Bof M ha y) (hleStruct M (tach M) ha) s.val from
        (by rw [Agen, dif_pos s.isLt]),
      show chainA (genWidthEq M (tach M) (hleStruct M (tach M) ha) s.val s.isLt)
          ((Bof M ha y').Nblk s.val) ((Bof M ha y').Wblk s.val)
          (Cgen 1 M (tach M) (Bof M ha y') (hleStruct M (tach M) ha) (s.val + 1))
        = Agen 1 M (tach M) (Bof M ha y') (hleStruct M (tach M) ha) s.val from
        (by rw [Agen, dif_pos s.isLt]), hA]
  have hkept : (Cgen 1 M (tach M) (Bof M ha y) (hleStruct M (tach M) ha) (s.val + 1)
        - (Bof M ha y).Nblk s.val * (Bof M ha y).Wblk s.val)
      = (Cgen 1 M (tach M) (Bof M ha y') (hleStruct M (tach M) ha) (s.val + 1)
        - (Bof M ha y').Nblk s.val * (Bof M ha y').Wblk s.val) := by
    ext i j
    have h1 := congrFun (congrFun hAe (Fin.cast
        (genWidthEq M (tach M) (hleStruct M (tach M) ha) s.val s.isLt)
        (Fin.castAdd (Wext M s.val - Text M (tach M) (s.val + 1)) i))) j
    rwa [chainA_apply_castAdd, chainA_apply_castAdd] at h1
  have hgoal : Cgen 1 M (tach M) (Bof M ha y) (hleStruct M (tach M) ha) (s.val + 1)
      = (Cgen 1 M (tach M) (Bof M ha y) (hleStruct M (tach M) ha) (s.val + 1)
          - (Bof M ha y).Nblk s.val * (Bof M ha y).Wblk s.val)
        + (Bof M ha y).Nblk s.val * (Bof M ha y).Wblk s.val := by
    rw [sub_add_cancel]
  rw [hgoal, hkept, hN, hW, sub_add_cancel]

/-! ## Step 3 — the per-boundary frame reader recovery (`frameRecoverGen`) -/

/-- The `SchurInc` tuple of the frame readers at interior boundary `k` (index `⟨k, hk⟩ : Fin L`):
`(readK, readN, readX, readE)` in `SchurInc t_k r_k c_k` order. -/
private noncomputable def frameTuple (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M))
    (y : Fin (routeMAmbient M) → ℝ) (k : ℕ) (hk : k < L) :
    SchurInc (Text M (tach M) (k + 2)) (Text M (tach M) (k + 1) - Text M (tach M) (k + 2))
      (Wext M (k + 1) - Text M (tach M) (k + 2)) :=
  (Matrix.of (readK M (tach M) ha y ⟨k, hk⟩),
    Matrix.of (readN M (tach M) ha y ⟨k, hk⟩),
    Matrix.of (readX M (tach M) ha y ⟨k, hk⟩),
    Matrix.of (readE M (tach M) ha y ⟨k, hk⟩))

/-- **`schurFrameMap (frameTuple y k) = schurFrameProd 1 (readK)(readX)(readN)(readE)`** as block
matrices at the interior widths — the value bridge (the general-`k` lift of `flatBlock_schurFrameMap_eq`).
Established block-by-block over the `castAdd/natAdd` split via the four banked `schurFrameProd_block_*`
lemmas; `flatBlock` reshapes the tuple to the block-matrix type. -/
private theorem flatBlock_schurFrameMap_eq_gen (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M))
    (y : Fin (routeMAmbient M) → ℝ) (k : ℕ) (hk : k < L)
    (hr : Text M (tach M) (k + 2) + (Text M (tach M) (k + 1) - Text M (tach M) (k + 2))
        = Text M (tach M) (k + 1))
    (hc : Text M (tach M) (k + 2) + (Wext M (k + 1) - Text M (tach M) (k + 2)) = Wext M (k + 1)) :
    flatBlock hr hc (schurFrameMap (frameTuple M ha y k hk))
      = schurFrameProd M (tach M) (k + 1) (ha.hdesc k hk) (ha.hub k) (1 : ℝ)
          (Matrix.of (readK M (tach M) ha y ⟨k, hk⟩)) (Matrix.of (readX M (tach M) ha y ⟨k, hk⟩))
          (Matrix.of (readN M (tach M) ha y ⟨k, hk⟩)) (Matrix.of (readE M (tach M) ha y ⟨k, hk⟩)) := by
  ext i j
  obtain ⟨is, hieq⟩ : ∃ is, i = Fin.cast hr (finSumFinEquiv is) :=
    ⟨finSumFinEquiv.symm (Fin.cast hr.symm i), by rw [Equiv.apply_symm_apply]; apply Fin.ext; simp⟩
  obtain ⟨js, hjeq⟩ : ∃ js, j = Fin.cast hc (finSumFinEquiv js) :=
    ⟨finSumFinEquiv.symm (Fin.cast hc.symm j), by rw [Equiv.apply_symm_apply]; apply Fin.ext; simp⟩
  subst hieq hjeq
  rcases is with i' | a <;> rcases js with j' | b
  · rw [show finSumFinEquiv (Sum.inl i') = Fin.castAdd _ i' from rfl,
      show finSumFinEquiv (Sum.inl j') = Fin.castAdd _ j' from rfl, flatBlock_castAdd]
    rw [show Fin.cast hc.symm (Fin.cast hc (Fin.castAdd _ j')) = Fin.castAdd _ j' from by
        apply Fin.ext; simp, finSumFinEquiv_symm_apply_castAdd,
      Sum.elim_inl, schurFrameProd_block_K]
    rfl
  · rw [show finSumFinEquiv (Sum.inl i') = Fin.castAdd _ i' from rfl,
      show finSumFinEquiv (Sum.inr b) = Fin.natAdd _ b from rfl, flatBlock_castAdd]
    rw [show Fin.cast hc.symm (Fin.cast hc (Fin.natAdd _ b)) = Fin.natAdd _ b from by
        apply Fin.ext; simp, finSumFinEquiv_symm_apply_natAdd,
      Sum.elim_inr, schurFrameProd_block_KN]
    rfl
  · rw [show finSumFinEquiv (Sum.inr a) = Fin.natAdd _ a from rfl,
      show finSumFinEquiv (Sum.inl j') = Fin.castAdd _ j' from rfl, flatBlock_natAdd]
    rw [show Fin.cast hc.symm (Fin.cast hc (Fin.castAdd _ j')) = Fin.castAdd _ j' from by
        apply Fin.ext; simp, finSumFinEquiv_symm_apply_castAdd,
      Sum.elim_inl, schurFrameProd_block_XK]
    rfl
  · rw [show finSumFinEquiv (Sum.inr a) = Fin.natAdd _ a from rfl,
      show finSumFinEquiv (Sum.inr b) = Fin.natAdd _ b from rfl, flatBlock_natAdd]
    rw [show Fin.cast hc.symm (Fin.cast hc (Fin.natAdd _ b)) = Fin.natAdd _ b from by
        apply Fin.ext; simp, finSumFinEquiv_symm_apply_natAdd,
      Sum.elim_inr, schurFrameProd_block_XKNuE]
    show _ = (Matrix.of (readX M (tach M) ha y ⟨k, hk⟩) * Matrix.of (readK M (tach M) ha y ⟨k, hk⟩)
      * Matrix.of (readN M (tach M) ha y ⟨k, hk⟩)) a b + 1 * Matrix.of (readE M (tach M) ha y ⟨k, hk⟩) a b
    rw [one_mul]; rfl

/-- **`Cgen(k+1) = flatBlock (schurFrameMap (frameTuple y k))`** at an interior boundary (`k+1 < L`).
Chains the banked `Cgen_live_interior_eq_schurFrameProd` (the live decoder's transition is the Schur
frame) with the value bridge `flatBlock_schurFrameMap_eq_gen`. -/
private theorem Cgen_eq_flatBlock_schurFrameMap (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M))
    (rfin : Matrix (Fin (Text M (tach M) L)) (Fin (Wext M L)) ℝ)
    (y : Fin (routeMAmbient M) → ℝ) (k : ℕ) (hk1 : k + 1 < L)
    (hr : Text M (tach M) (k + 2) + (Text M (tach M) (k + 1) - Text M (tach M) (k + 2))
        = Text M (tach M) (k + 1))
    (hc : Text M (tach M) (k + 2) + (Wext M (k + 1) - Text M (tach M) (k + 2)) = Wext M (k + 1)) :
    Cgen 1 M (tach M) (genBlkFlatLive M (tach M) ha rfin y) (hleStruct M (tach M) ha) (k + 1)
      = flatBlock hr hc (schurFrameMap (frameTuple M ha y k (by omega))) := by
  rw [Cgen_live_interior_eq_schurFrameProd M (tach M) ha rfin (1 : ℝ) y k hk1,
    flatBlock_schurFrameMap_eq_gen M ha y k (by omega) hr hc]
  rfl

/-- **The frame readers are recovered at an interior boundary** (`k+1 < L`), given `Cgen(k+1)`
agreement and `det K ≠ 0`. From `Cgen(k+1)(y) = Cgen(k+1)(y')`, the value bridge + `flatBlock`
injectivity give `schurFrameMap (frameTuple y) = schurFrameMap (frameTuple y')`, and
`schurFrameMap_inj_of_det_ne_zero_gen` recovers all four `readK/N/X/E ⟨k⟩` readers. -/
theorem frameRecoverGen (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M))
    (y y' : Fin (routeMAmbient M) → ℝ) (k : ℕ) (hk1 : k + 1 < L)
    (hCg : Cgen 1 M (tach M) (Bof M ha y) (hleStruct M (tach M) ha) (k + 1)
        = Cgen 1 M (tach M) (Bof M ha y') (hleStruct M (tach M) ha) (k + 1))
    (hK : (Matrix.of (readK M (tach M) ha y ⟨k, by omega⟩)).det ≠ 0) :
    frameTuple M ha y k (by omega) = frameTuple M ha y' k (by omega) := by
  have hr : Text M (tach M) (k + 2) + (Text M (tach M) (k + 1) - Text M (tach M) (k + 2))
      = Text M (tach M) (k + 1) := by have := ha.hdesc k (by omega); omega
  have hc : Text M (tach M) (k + 2) + (Wext M (k + 1) - Text M (tach M) (k + 2)) = Wext M (k + 1) := by
    have := ha.hub k; omega
  have hSF : schurFrameMap (frameTuple M ha y k (by omega))
      = schurFrameMap (frameTuple M ha y' k (by omega)) := by
    apply (flatBlockLE hr hc).injective
    show flatBlock hr hc (schurFrameMap (frameTuple M ha y k (by omega)))
      = flatBlock hr hc (schurFrameMap (frameTuple M ha y' k (by omega)))
    rw [← Cgen_eq_flatBlock_schurFrameMap M ha (rfinDirectGen M ha y) y k hk1 hr hc,
      ← Cgen_eq_flatBlock_schurFrameMap M ha (rfinDirectGen M ha y') y' k hk1 hr hc]
    exact hCg
  exact schurFrameMap_inj_of_det_ne_zero_gen hK hSF

/-! ## Step 4 — the block ↔ reader identity + the forward induction over boundaries -/

/-- `readN` agreement from `frameTuple` agreement (the `.2.1` component). -/
private theorem readN_eq_of_frameTuple_eq (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M))
    (y y' : Fin (routeMAmbient M) → ℝ) (k : ℕ) (hk : k < L)
    (h : frameTuple M ha y k hk = frameTuple M ha y' k hk) :
    (fun i j => readN M (tach M) ha y ⟨k, hk⟩ i j)
      = fun i j => readN M (tach M) ha y' ⟨k, hk⟩ i j := by
  have := congrArg (fun z => z.2.1) h
  simpa [frameTuple] using this

/-- The live decoder's `Nblk` agrees iff the `readN` readers agree (`Nblk (k+1) = readN ⟨k⟩`,
`Nblk 0 = 0`). Package the `Nblk s.val` agreement for the `Cgen_eq_of_Agen_eq` subtraction. -/
private theorem Nblk_eq_of_readN_eq (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M))
    (y y' : Fin (routeMAmbient M) → ℝ) (s : Fin L)
    (hN : ∀ (j : ℕ) (hj : j < L), j + 1 = s.val →
      (fun a b => readN M (tach M) ha y ⟨j, hj⟩ a b)
        = fun a b => readN M (tach M) ha y' ⟨j, hj⟩ a b) :
    (Bof M ha y).Nblk s.val = (Bof M ha y').Nblk s.val := by
  match hs : s.val with
  | 0 => show (0 : Matrix _ _ ℝ) = 0; rfl
  | (j + 1) =>
    have hjL : j < L := by omega
    rw [genBlkFlatLive_Nblk_succ M (tach M) ha (rfinDirectGen M ha y) y j hjL,
      genBlkFlatLive_Nblk_succ M (tach M) ha (rfinDirectGen M ha y') y' j hjL]
    exact hN j hjL hs.symm

/-- **The transition block `Cgen(k+1)` agrees at EVERY interior boundary `k < L`** — the forward
induction (route (a)'s triangular substitution). At `k`, `Wblk k` agrees (from `Agen k`, uncond.);
`Nblk k = readN ⟨k−1⟩` agrees from `frameRecoverGen (k−1)` (needs `Cgen(k)` = the previous step);
`Cgen_eq_of_Agen_eq` then gives `Cgen(k+1)`. Base `k = 0`: `Nblk 0 = 0`, direct. -/
theorem Cgen_succ_eq_of_BchartLeafGen_eq (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M)) (hL : 0 < L)
    (h0r : 0 < Text M (tach M) L) (h0c : 0 < Wext M L)
    (y y' : Fin (routeMAmbient M) → ℝ)
    (hymem : y ∈ kLDU M (tach M) ha ''
      (pivotBlowupOn (activeMGen M ha) (leafPivot M ha hL h0r h0c) ''
        interiorLiveInjDomGen M ha hL h0r h0c))
    (heq : BchartLeafGen M ha y = BchartLeafGen M ha y') :
    ∀ k, (hk : k < L) →
      Cgen 1 M (tach M) (Bof M ha y) (hleStruct M (tach M) ha) (k + 1)
        = Cgen 1 M (tach M) (Bof M ha y') (hleStruct M (tach M) ha) (k + 1) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    have hAgen := Agen_eq_of_BchartLeafGen_eq M ha y y' heq ⟨k, hk⟩
    have hW : (Bof M ha y).Wblk k = (Bof M ha y').Wblk k :=
      Wblk_eq_of_Agen_eq M ha y y' ⟨k, hk⟩ hAgen
    have hN : (Bof M ha y).Nblk k = (Bof M ha y').Nblk k := by
      refine Nblk_eq_of_readN_eq M ha y y' ⟨k, hk⟩ (fun j hjL hjeq => ?_)
      have hjk : j < k := by simp only at hjeq; omega
      have hCgj : Cgen 1 M (tach M) (Bof M ha y) (hleStruct M (tach M) ha) (j + 1)
          = Cgen 1 M (tach M) (Bof M ha y') (hleStruct M (tach M) ha) (j + 1) := ih j hjk hjL
      have hj1L : j + 1 < L := by simp only at hjeq; omega
      have hdetKj : (Matrix.of (readK M (tach M) ha y ⟨j, by omega⟩)).det ≠ 0 :=
        detK_ne_zero_gen M ha hL h0r h0c hymem ⟨j, by omega⟩
      have hFrame := frameRecoverGen M ha y y' j hj1L hCgj hdetKj
      exact readN_eq_of_frameTuple_eq M ha y y' j (by omega) hFrame
    exact Cgen_eq_of_Agen_eq M ha y y' ⟨k, hk⟩ hAgen hN hW

/-! ## Step 5 — the reader-agreement bundle + the funext coverage-closer -/

/-- The four frame readers agree at every INTERIOR boundary `k` (`k + 1 < L`) — from `Cgen(k+1)`
agreement (`Cgen_succ_eq_…`) + `det K ≠ 0` (gate) via `frameRecoverGen`. -/
theorem frameReaders_eq (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M)) (hL : 0 < L)
    (h0r : 0 < Text M (tach M) L) (h0c : 0 < Wext M L) (y y' : Fin (routeMAmbient M) → ℝ)
    (hymem : y ∈ kLDU M (tach M) ha ''
      (pivotBlowupOn (activeMGen M ha) (leafPivot M ha hL h0r h0c) ''
        interiorLiveInjDomGen M ha hL h0r h0c))
    (heq : BchartLeafGen M ha y = BchartLeafGen M ha y') (k : ℕ) (hk1 : k + 1 < L) :
    frameTuple M ha y k (by omega) = frameTuple M ha y' k (by omega) := by
  refine frameRecoverGen M ha y y' k hk1
    (Cgen_succ_eq_of_BchartLeafGen_eq M ha hL h0r h0c y y' hymem heq k (by omega)) ?_
  exact detK_ne_zero_gen M ha hL h0r h0c hymem ⟨k, by omega⟩

/-- The leaf reader agrees — `Cgen(L) = 1 • rfinDirectGen` (`Cgen` leaf arm), so `Cgen(L)`-agreement
(`Cgen_succ_eq_…` at `k = L−1`) gives `rfinDirectGen y = rfinDirectGen y'`. -/
theorem rfinDirectGen_eq (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M)) (hL : 0 < L)
    (h0r : 0 < Text M (tach M) L) (h0c : 0 < Wext M L) (y y' : Fin (routeMAmbient M) → ℝ)
    (hymem : y ∈ kLDU M (tach M) ha ''
      (pivotBlowupOn (activeMGen M ha) (leafPivot M ha hL h0r h0c) ''
        interiorLiveInjDomGen M ha hL h0r h0c))
    (heq : BchartLeafGen M ha y = BchartLeafGen M ha y') :
    rfinDirectGen M ha y = rfinDirectGen M ha y' := by
  have hCgL := Cgen_succ_eq_of_BchartLeafGen_eq M ha hL h0r h0c y y' hymem heq (L - 1) (by omega)
  rw [show L - 1 + 1 = L by omega] at hCgL
  have hleaf : ∀ z : Fin (routeMAmbient M) → ℝ,
      Cgen 1 M (tach M) (Bof M ha z) (hleStruct M (tach M) ha) L = rfinDirectGen M ha z := by
    intro z
    rw [Cgen, dif_neg (lt_irrefl L), show (Bof M ha z).Rfin L = rfinDirectGen M ha z from dif_pos rfl,
      one_smul]
  rw [hleaf y, hleaf y'] at hCgL
  exact hCgL

/-- The lift readers agree at every interior boundary `k` (`k.val + 1 < L`) — from `Wblk (k.val+1)`
agreement (`Wblk_eq_of_Agen_eq` at boundary `⟨k.val+1⟩`), which unfolds (`genBlkFlatStruct`) to
`readW k`. -/
theorem readW_eq (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M)) (y y' : Fin (routeMAmbient M) → ℝ)
    (heq : BchartLeafGen M ha y = BchartLeafGen M ha y') (k : Fin L) (hk1 : k.val + 1 < L) :
    (fun i j => readW M (tach M) ha y k hk1 i j)
      = fun i j => readW M (tach M) ha y' k hk1 i j := by
  have hkL : k.val < L := k.isLt
  have hAgen := Agen_eq_of_BchartLeafGen_eq M ha y y' heq ⟨k.val + 1, hk1⟩
  have hW := Wblk_eq_of_Agen_eq M ha y y' ⟨k.val + 1, hk1⟩ hAgen
  have hyW : (Bof M ha y).Wblk (k.val + 1)
      = fun i j => readW M (tach M) ha y ⟨k.val, hkL⟩ hk1 i j := by
    show (genBlkFlatStruct M (tach M) ha y).Wblk (k.val + 1) = _
    simp only [genBlkFlatStruct, dif_pos hkL, dif_pos hk1]
  have hy'W : (Bof M ha y').Wblk (k.val + 1)
      = fun i j => readW M (tach M) ha y' ⟨k.val, hkL⟩ hk1 i j := by
    show (genBlkFlatStruct M (tach M) ha y').Wblk (k.val + 1) = _
    simp only [genBlkFlatStruct, dif_pos hkL, dif_pos hk1]
  rw [hyW, hy'W] at hW
  exact hW

/-- **Frame-slot coverage at an interior boundary** (`k + 1 < L`): `y` and `y'` agree on EVERY frame
slot `chartIdxEquiv.symm ⟨k, Sum.inl s⟩`. Decode `s` via `frameSplitEquiv` into the K/X/N/E role and
match the corresponding reader (all four agree by `frameReaders_eq`). -/
theorem frameSlot_eq (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M)) (hL : 0 < L)
    (h0r : 0 < Text M (tach M) L) (h0c : 0 < Wext M L) (y y' : Fin (routeMAmbient M) → ℝ)
    (hymem : y ∈ kLDU M (tach M) ha ''
      (pivotBlowupOn (activeMGen M ha) (leafPivot M ha hL h0r h0c) ''
        interiorLiveInjDomGen M ha hL h0r h0c))
    (heq : BchartLeafGen M ha y = BchartLeafGen M ha y') (k : Fin L) (hk1 : k.val + 1 < L)
    (s : Fin (schurDim M (tDesc M (tach M)) k.val)) :
    y ((chartIdxEquiv M (tDesc M (tach M)) ha.h0 ha.hc ha.hL).symm ⟨k, Sum.inl s⟩)
      = y' ((chartIdxEquiv M (tDesc M (tach M)) ha.h0 ha.hc ha.hL).symm ⟨k, Sum.inl s⟩) := by
  have hFrame := frameReaders_eq M ha hL h0r h0c y y' hymem heq k.val hk1
  have hK : (fun i j => readK M (tach M) ha y ⟨k.val, k.isLt⟩ i j)
      = fun i j => readK M (tach M) ha y' ⟨k.val, k.isLt⟩ i j := by
    have := congrArg (fun z => z.1) hFrame; simpa [frameTuple] using this
  have hX : (fun i j => readX M (tach M) ha y ⟨k.val, k.isLt⟩ i j)
      = fun i j => readX M (tach M) ha y' ⟨k.val, k.isLt⟩ i j := by
    have := congrArg (fun z => z.2.2.1) hFrame; simpa [frameTuple] using this
  have hN : (fun i j => readN M (tach M) ha y ⟨k.val, k.isLt⟩ i j)
      = fun i j => readN M (tach M) ha y' ⟨k.val, k.isLt⟩ i j := by
    have := congrArg (fun z => z.2.1) hFrame; simpa [frameTuple] using this
  have hE : (fun i j => readE M (tach M) ha y ⟨k.val, k.isLt⟩ i j)
      = fun i j => readE M (tach M) ha y' ⟨k.val, k.isLt⟩ i j := by
    have := congrArg (fun z => z.2.2.2) hFrame; simpa [frameTuple] using this
  have hkidx : (⟨k.val, k.isLt⟩ : Fin L) = k := rfl
  match heqf : frameSplitEquiv M (tach M) (k.val + 1) (ha.hdesc k.val k.isLt) (ha.hub k.val) s with
  | Sum.inl (Sum.inl (Sum.inl qK)) =>
    have hslot : ∀ z : Fin (routeMAmbient M) → ℝ,
        z ((chartIdxEquiv M (tDesc M (tach M)) ha.h0 ha.hc ha.hL).symm ⟨k, Sum.inl s⟩)
          = readK M (tach M) ha z k (finProdFinEquiv.symm qK).1 (finProdFinEquiv.symm qK).2 := by
      intro z
      rw [readK, Prod.mk.eta, finProdFinEquiv.apply_symm_apply qK, ← heqf,
        Equiv.symm_apply_apply]
    rw [hslot y, hslot y']
    exact congrFun (congrFun hK _) _
  | Sum.inl (Sum.inl (Sum.inr qX)) =>
    have hslot : ∀ z : Fin (routeMAmbient M) → ℝ,
        z ((chartIdxEquiv M (tDesc M (tach M)) ha.h0 ha.hc ha.hL).symm ⟨k, Sum.inl s⟩)
          = readX M (tach M) ha z k (finProdFinEquiv.symm qX).1 (finProdFinEquiv.symm qX).2 := by
      intro z
      rw [readX, Prod.mk.eta, finProdFinEquiv.apply_symm_apply qX, ← heqf,
        Equiv.symm_apply_apply]
    rw [hslot y, hslot y']
    exact congrFun (congrFun hX _) _
  | Sum.inl (Sum.inr qN) =>
    have hslot : ∀ z : Fin (routeMAmbient M) → ℝ,
        z ((chartIdxEquiv M (tDesc M (tach M)) ha.h0 ha.hc ha.hL).symm ⟨k, Sum.inl s⟩)
          = readN M (tach M) ha z k (finProdFinEquiv.symm qN).1 (finProdFinEquiv.symm qN).2 := by
      intro z
      rw [readN, Prod.mk.eta, finProdFinEquiv.apply_symm_apply qN, ← heqf,
        Equiv.symm_apply_apply]
    rw [hslot y, hslot y']
    exact congrFun (congrFun hN _) _
  | Sum.inr qE =>
    have hslot : ∀ z : Fin (routeMAmbient M) → ℝ,
        z ((chartIdxEquiv M (tDesc M (tach M)) ha.h0 ha.hc ha.hL).symm ⟨k, Sum.inl s⟩)
          = readE M (tach M) ha z k (finProdFinEquiv.symm qE).1 (finProdFinEquiv.symm qE).2 := by
      intro z
      rw [readE, Prod.mk.eta, finProdFinEquiv.apply_symm_apply qE, ← heqf,
        Equiv.symm_apply_apply]
    rw [hslot y, hslot y']
    exact congrFun (congrFun hE _) _

/-- **Leaf-slot coverage** (`k = L − 1`): `y` and `y'` agree on every frame slot
`chartIdxEquiv.symm ⟨⟨L−1,_⟩, Sum.inl s⟩`. The frame slot at boundary `L − 1` IS the leaf slot
(`leafSlot` reads it via `schurSlotEquiv`), so `rfinDirectGen_eq` covers it: decode `s` via
`schurSlotEquiv` to `(a, b)`, and `leafSlot (cast a) (cast b) = chartIdxEquiv.symm ⟨⟨L−1,_⟩, Sum.inl
s⟩`. -/
theorem leafSlot_eq (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M)) (hL : 0 < L)
    (h0r : 0 < Text M (tach M) L) (h0c : 0 < Wext M L) (y y' : Fin (routeMAmbient M) → ℝ)
    (hymem : y ∈ kLDU M (tach M) ha ''
      (pivotBlowupOn (activeMGen M ha) (leafPivot M ha hL h0r h0c) ''
        interiorLiveInjDomGen M ha hL h0r h0c))
    (heq : BchartLeafGen M ha y = BchartLeafGen M ha y')
    (k : Fin L) (hkeq : k = ⟨L - 1, by omega⟩)
    (s : Fin (schurDim M (tDesc M (tach M)) k.val)) :
    y ((chartIdxEquiv M (tDesc M (tach M)) ha.h0 ha.hc ha.hL).symm ⟨k, Sum.inl s⟩)
      = y' ((chartIdxEquiv M (tDesc M (tach M)) ha.h0 ha.hc ha.hL).symm ⟨k, Sum.inl s⟩) := by
  subst hkeq
  have hrfin := rfinDirectGen_eq M ha hL h0r h0c y y' hymem heq
  have hi : Text M (tach M) L = tDesc M (tach M) (L - 1) := by
    rw [tDesc_apply]; congr 1; omega
  have hj : Wext M L = Wext M (L - 1 + 1) := by congr 1; omega
  set a := (schurSlotEquiv M (tDesc M (tach M)) (L - 1) s).1 with ha_def
  set b := (schurSlotEquiv M (tDesc M (tach M)) (L - 1) s).2 with hb_def
  set i₀ : Fin (Text M (tach M) L) := Fin.cast hi.symm a with hi₀
  set j₀ : Fin (Wext M L) := Fin.cast hj.symm b with hj₀
  have hsum : ((schurSlotEquiv M (tDesc M (tach M)) (L - 1)).symm
        (Fin.cast hi i₀, Fin.cast hj j₀) : _) = s := by
    rw [hi₀, hj₀,
      show (Fin.cast hi (Fin.cast hi.symm a)) = a from by apply Fin.ext; simp,
      show (Fin.cast hj (Fin.cast hj.symm b)) = b from by apply Fin.ext; simp,
      ha_def, hb_def, Prod.mk.eta, Equiv.symm_apply_apply]
  have hleaf : leafSlot M (tach M) ha ha.hL i₀ j₀
      = (chartIdxEquiv M (tDesc M (tach M)) ha.h0 ha.hc ha.hL).symm
          ⟨⟨L - 1, by omega⟩, Sum.inl s⟩ := by
    rw [leafSlot]
    exact congrArg _ (congrArg _ (congrArg Sum.inl hsum))
  rw [← hleaf]
  show rfinDirectGen M ha y i₀ j₀ = rfinDirectGen M ha y' i₀ j₀
  exact congrFun (congrFun hrfin _) _

/-! ## Step 6 — the funext coverage-closer -/

/-- **`BchartLeafGen` injective on the kLDU-image of `pbo '' injDom`** (general-`L`) — the route (a)
close. From `BchartLeafGen y = BchartLeafGen y'`, funext over the ambient coordinate `q`, decode via
`chartIdxEquiv`: a lift slot `⟨k, Sum.inr s⟩` (nonempty ⟹ `k + 1 < L`) is a `readW k` coord
(`readW_eq`); a frame slot `⟨k, Sum.inl s⟩` is recovered by `frameSlot_eq` (interior `k + 1 < L`) or
`leafSlot_eq` (leaf `k = L − 1`). -/
theorem BchartLeafGen_injOn_recover (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M)) (hL : 0 < L)
    (h0r : 0 < Text M (tach M) L) (h0c : 0 < Wext M L) :
    Set.InjOn (BchartLeafGen M ha)
      (kLDU M (tach M) ha
        '' (pivotBlowupOn (activeMGen M ha) (leafPivot M ha hL h0r h0c)
          '' interiorLiveInjDomGen M ha hL h0r h0c)) := by
  intro y hy y' _ heq
  funext q
  obtain ⟨c, hc⟩ : ∃ c, q = (chartIdxEquiv M (tDesc M (tach M)) ha.h0 ha.hc ha.hL).symm c :=
    ⟨chartIdxEquiv M (tDesc M (tach M)) ha.h0 ha.hc ha.hL q, by
      rw [Equiv.symm_apply_apply]⟩
  subst hc
  obtain ⟨k, side⟩ := c
  cases side with
  | inl s =>
    by_cases hk1 : k.val + 1 < L
    · exact frameSlot_eq M ha hL h0r h0c y y' hy heq k hk1 s
    · have hk1' : ¬ (k.val + 1 < L) := hk1
      have hkv : k.val = L - 1 := by have := k.isLt; omega
      have hkeq : k = ⟨L - 1, by omega⟩ := Fin.ext hkv
      exact leafSlot_eq M ha hL h0r h0c y y' hy heq k hkeq s
  | inr s =>
    by_cases hk1 : k.val + 1 < L
    · set e := liftSlotEquiv M (tDesc M (tach M)) k.val hk1 with he
      have hslot : ∀ z : Fin (routeMAmbient M) → ℝ,
          z ((chartIdxEquiv M (tDesc M (tach M)) ha.h0 ha.hc ha.hL).symm ⟨k, Sum.inr s⟩)
            = readW M (tach M) ha z k hk1 (e s).1 (e s).2 := by
        intro z
        rw [readW, ← he, Prod.mk.eta, Equiv.symm_apply_apply]
      rw [hslot y, hslot y']
      exact congrFun (congrFun (readW_eq M ha y y' heq k hk1) _) _
    · have hz : liftDim M (tDesc M (tach M)) k.val = 0 := by
        rw [liftDim, if_neg (by omega)]
      have hslt : (s : ℕ) < liftDim M (tDesc M (tach M)) k.val := s.isLt
      omega

end DLNFibre.DLN.RLCT
