import DLNFibre.DLN.RLCT.Validate.RouteMDecoderDiff
import DLNFibre.DLN.RLCT.Validate.RouteMChartDiff
import DLNFibre.DLN.RLCT.Validate.RouteMFlatLive
import Mathlib.Analysis.Calculus.FDeriv.Comp

/-!
# `RouteMChainAssembleDiff` — b-FrameM-2 DONE: `DifferentiableAt phiFlatLiveR1`

The culminating chain-telescope assembly of b-FrameM-2 (`item3-frameM-buildspec.md`): threads the
banked differentiability atoms (`RouteMChainDiff`'s `chainQ`/`chainA`/`matMul`, `RouteMDecoderDiff`'s
`bmatStack`/`rmatPad`) through the live decoder's blocks → `Cgen` → `Agen` → the reduction
`RouteMChartDiff.phiFlatLiveR1_differentiableAt_of_Agen`, giving

  `phiFlatLiveR1_differentiableAt : DifferentiableAt ℝ (phiFlatLiveR1 …) x₀`

(given `rfin` differentiable). This is the EXISTENCE of the chart Jacobian `DFrame_M` that the
b-FrameM-3 keystone (`toMatrix_blockTriangular_of_locality`) consumes to discharge the interior-det
headline's `hbt`.

**Cast-management lessons used** (all empirical, Codex at-capacity): work over the Pi form; matMul
ENTRIES go explicit-sum (not the CLM, which whnf-stalls); the live `Rmat`'s `Function.update` over a
dependent matrix codomain is cased by `split_ifs` INSIDE the diff goal (no index rewrite — sidesteps the
"motive not type correct" dependent-type change); `Rfin`'s `dite (k = L)` by `by_cases` + `subst`.

* `diffAt_read{K,X,N,E,W}` — the single-coordinate reader blocks are differentiable.
* `diffAt_live{Bmat,Nblk,Wblk,Rmat,Rfin}` — the five live-decoder blocks are differentiable in `x`.
* `diffAt_Cgen` / `diffAt_Agen` — the chain `C`/`A` layers are differentiable (interior + leaf).
* `phiFlatLiveR1_differentiableAt` — **b-FrameM-2 complete**: the chart is differentiable.

Axiom-clean `[propext, Classical.choice, Quot.sound]` (Mathlib calculus + the banked matrix fderiv).
-/

open scoped BigOperators
open Matrix

namespace DLNFibre.DLN.RLCT

variable {L : ℕ}

/-! ## The reader blocks are differentiable (single-coordinate reads) -/

theorem diffAt_readK (M t : Fin (L + 1) → ℕ) (ha : StructAdm M t) (k : Fin L)
    (u : Fin (routeMAmbient M) → ℝ) : DifferentiableAt ℝ (fun x => readK M t ha x k) u := by
  apply differentiableAt_pi.mpr; intro i; apply differentiableAt_pi.mpr; intro j
  unfold readK; exact differentiableAt_apply _ u

theorem diffAt_readX (M t : Fin (L + 1) → ℕ) (ha : StructAdm M t) (k : Fin L)
    (u : Fin (routeMAmbient M) → ℝ) : DifferentiableAt ℝ (fun x => readX M t ha x k) u := by
  apply differentiableAt_pi.mpr; intro i; apply differentiableAt_pi.mpr; intro j
  unfold readX; exact differentiableAt_apply _ u

theorem diffAt_readN (M t : Fin (L + 1) → ℕ) (ha : StructAdm M t) (k : Fin L)
    (u : Fin (routeMAmbient M) → ℝ) : DifferentiableAt ℝ (fun x => readN M t ha x k) u := by
  apply differentiableAt_pi.mpr; intro i; apply differentiableAt_pi.mpr; intro j
  unfold readN; exact differentiableAt_apply _ u

theorem diffAt_readE (M t : Fin (L + 1) → ℕ) (ha : StructAdm M t) (k : Fin L)
    (u : Fin (routeMAmbient M) → ℝ) : DifferentiableAt ℝ (fun x => readE M t ha x k) u := by
  apply differentiableAt_pi.mpr; intro i; apply differentiableAt_pi.mpr; intro j
  unfold readE; exact differentiableAt_apply _ u

theorem diffAt_readW (M t : Fin (L + 1) → ℕ) (ha : StructAdm M t) (k : Fin L) (hk : k.val + 1 < L)
    (u : Fin (routeMAmbient M) → ℝ) : DifferentiableAt ℝ (fun x => readW M t ha x k hk) u := by
  apply differentiableAt_pi.mpr; intro i; apply differentiableAt_pi.mpr; intro j
  unfold readW; exact differentiableAt_apply _ u

/-! ## The live-decoder blocks are differentiable in `x` -/

variable (M t : Fin (L + 1) → ℕ) (ha : StructAdm M t) (p : ℕ)
  (hp1 : Text M t (p + 1) ≤ Text M t p) (hp2 : Text M t (p + 1) ≤ Wext M p)
  (rfin : (Fin (routeMAmbient M) → ℝ) → Matrix (Fin (Text M t L)) (Fin (Wext M L)) ℝ)

/-- The live decoder's `Bmat k` is differentiable in `x` (`bmatStack(readK, readX)` interior; const
identity boundary; `0` out of range). -/
theorem diffAt_liveBmat (u : Fin (routeMAmbient M) → ℝ) (k : ℕ) :
    DifferentiableAt ℝ (fun x => (genBlkFlatLiveR1 M t ha p hp1 hp2 (rfin x) x).Bmat k) u := by
  show DifferentiableAt ℝ (fun x => (genBlkFlatStruct M t ha x).Bmat k) u
  match k with
  | 0 => exact differentiableAt_const _
  | (j + 1) =>
    by_cases hj : j < L
    · simp only [genBlkFlatStruct, dif_pos hj]
      exact diffAt_bmatStack M t (j + 1) (ha.hdesc j hj) _ _ u
        (diffAt_readK M t ha ⟨j, hj⟩ u) (diffAt_readX M t ha ⟨j, hj⟩ u)
    · simp only [genBlkFlatStruct, dif_neg hj]; exact differentiableAt_const _

/-- The live decoder's `Nblk k` is differentiable in `x` (`readN` interior; `0` else). -/
theorem diffAt_liveNblk (u : Fin (routeMAmbient M) → ℝ) (k : ℕ) :
    DifferentiableAt ℝ (fun x => (genBlkFlatLiveR1 M t ha p hp1 hp2 (rfin x) x).Nblk k) u := by
  show DifferentiableAt ℝ (fun x => (genBlkFlatStruct M t ha x).Nblk k) u
  match k with
  | 0 => exact differentiableAt_const _
  | (j + 1) =>
    by_cases hj : j < L
    · simp only [genBlkFlatStruct, dif_pos hj]; exact diffAt_readN M t ha ⟨j, hj⟩ u
    · simp only [genBlkFlatStruct, dif_neg hj]; exact differentiableAt_const _

/-- The live decoder's `Wblk k` is differentiable in `x` (`readW` deep interior; `0` else). -/
theorem diffAt_liveWblk (u : Fin (routeMAmbient M) → ℝ) (k : ℕ) :
    DifferentiableAt ℝ (fun x => (genBlkFlatLiveR1 M t ha p hp1 hp2 (rfin x) x).Wblk k) u := by
  show DifferentiableAt ℝ (fun x => (genBlkFlatStruct M t ha x).Wblk k) u
  match k with
  | 0 => exact differentiableAt_const _
  | (j + 1) =>
    by_cases hj : j < L
    · by_cases hj2 : j + 1 < L
      · simp only [genBlkFlatStruct, dif_pos hj, dif_pos hj2]
        exact diffAt_readW M t ha ⟨j, hj⟩ hj2 u
      · simp only [genBlkFlatStruct, dif_pos hj, dif_neg hj2]; exact differentiableAt_const _
    · simp only [genBlkFlatStruct, dif_neg hj]; exact differentiableAt_const _

/-- The live decoder's `Rmat k` is differentiable in `x` — `Function.update (rmatPad(readE)) p (const)`;
cased by `split_ifs` INSIDE the diff goal (no dependent index rewrite). -/
theorem diffAt_liveRmat (u : Fin (routeMAmbient M) → ℝ) (k : ℕ) :
    DifferentiableAt ℝ (fun x => (genBlkFlatLiveR1 M t ha p hp1 hp2 (rfin x) x).Rmat k) u := by
  show DifferentiableAt ℝ
    (fun x => Function.update (genBlkFlatLive M t ha (rfin x) x).Rmat p
      (rmatPad M t p hp1 hp2 (pivotEIndicator M t p)) k) u
  simp only [Function.update]
  split_ifs with hkp
  · exact differentiableAt_const _
  · show DifferentiableAt ℝ (fun x => (genBlkFlatStruct M t ha x).Rmat k) u
    match k with
    | 0 => exact differentiableAt_const _
    | (j + 1) =>
      by_cases hj : j < L
      · simp only [genBlkFlatStruct, dif_pos hj]
        exact diffAt_rmatPad M t (j + 1) (ha.hdesc j hj) (ha.hub j) _ u
          (diffAt_readE M t ha ⟨j, hj⟩ u)
      · simp only [genBlkFlatStruct, dif_neg hj]; exact differentiableAt_const _

/-- The live decoder's `Rfin k` is differentiable in `x` — `dite (k = L) (rfin x) 0`; the live leaf is
`rfin x` (given `rfin` differentiable), else `0`. -/
theorem diffAt_liveRfin (u : Fin (routeMAmbient M) → ℝ) (k : ℕ) (hrfin : DifferentiableAt ℝ rfin u) :
    DifferentiableAt ℝ (fun x => (genBlkFlatLiveR1 M t ha p hp1 hp2 (rfin x) x).Rfin k) u := by
  show DifferentiableAt ℝ (fun x => (genBlkFlatLive M t ha (rfin x) x).Rfin k) u
  by_cases hkL : k = L
  · subst hkL
    rw [show (fun x => (genBlkFlatLive M t ha (rfin x) x).Rfin k) = rfin from by
      funext x; simp [genBlkFlatLive]]
    exact hrfin
  · rw [show (fun x => (genBlkFlatLive M t ha (rfin x) x).Rfin k) = fun _ => 0 from by
      funext x; simp only [genBlkFlatLive, dif_neg hkL]]
    exact differentiableAt_const _

/-! ## The chain `C` / `A` layers are differentiable -/

/-- `Cgen` (the chain `C`) of the live chart is differentiable at each `k` (interior `Bmat·chainQ(Nblk)
+ (x p₀)·Rmat`; leaf `(x p₀)·Rfin`). -/
theorem diffAt_Cgen (hN : 0 < routeMAmbient M) (u : Fin (routeMAmbient M) → ℝ) (k : ℕ)
    (hrfin : DifferentiableAt ℝ rfin u) :
    DifferentiableAt ℝ (fun x => Cgen (x (structPivot M hN)) M t
      (genBlkFlatLiveR1 M t ha p hp1 hp2 (rfin x) x) (hleStruct M t ha) k) u := by
  by_cases hk : k < L
  · rw [show (fun x => Cgen (x (structPivot M hN)) M t
          (genBlkFlatLiveR1 M t ha p hp1 hp2 (rfin x) x) (hleStruct M t ha) k)
        = fun x => (genBlkFlatLiveR1 M t ha p hp1 hp2 (rfin x) x).Bmat k
            * chainQ (genWidthEq M t (hleStruct M t ha) k hk)
              ((genBlkFlatLiveR1 M t ha p hp1 hp2 (rfin x) x).Nblk k)
            + (x (structPivot M hN)) • (genBlkFlatLiveR1 M t ha p hp1 hp2 (rfin x) x).Rmat k from by
      funext x; rw [Cgen, dif_pos hk]]
    exact (DifferentiableAt.matMul (diffAt_liveBmat M t ha p hp1 hp2 rfin u k)
      (diffAt_chainQ _ _ u (diffAt_liveNblk M t ha p hp1 hp2 rfin u k))).add
      ((differentiableAt_apply _ u).smul (diffAt_liveRmat M t ha p hp1 hp2 rfin u k))
  · rw [show (fun x => Cgen (x (structPivot M hN)) M t
          (genBlkFlatLiveR1 M t ha p hp1 hp2 (rfin x) x) (hleStruct M t ha) k)
        = fun x => (x (structPivot M hN))
            • (genBlkFlatLiveR1 M t ha p hp1 hp2 (rfin x) x).Rfin k from by
      funext x; rw [Cgen, dif_neg hk]]
    exact (differentiableAt_apply _ u).smul (diffAt_liveRfin M t ha p hp1 hp2 rfin u k hrfin)

/-- `Agen` (the chain `A`) of the live chart is differentiable at each `s`
(`chainA(Nblk, Wblk, Cgen(s+1))` interior; `0` leaf). -/
theorem diffAt_Agen (hN : 0 < routeMAmbient M) (u : Fin (routeMAmbient M) → ℝ) (s : ℕ)
    (hrfin : DifferentiableAt ℝ rfin u) :
    DifferentiableAt ℝ (fun x => Agen (x (structPivot M hN)) M t
      (genBlkFlatLiveR1 M t ha p hp1 hp2 (rfin x) x) (hleStruct M t ha) s) u := by
  by_cases hs : s < L
  · rw [show (fun x => Agen (x (structPivot M hN)) M t
          (genBlkFlatLiveR1 M t ha p hp1 hp2 (rfin x) x) (hleStruct M t ha) s)
        = fun x => chainA (genWidthEq M t (hleStruct M t ha) s hs)
            ((genBlkFlatLiveR1 M t ha p hp1 hp2 (rfin x) x).Nblk s)
            ((genBlkFlatLiveR1 M t ha p hp1 hp2 (rfin x) x).Wblk s)
            (Cgen (x (structPivot M hN)) M t (genBlkFlatLiveR1 M t ha p hp1 hp2 (rfin x) x)
              (hleStruct M t ha) (s + 1)) from by funext x; rw [Agen, dif_pos hs]]
    exact diffAt_chainA _ _ _ _ u (diffAt_liveNblk M t ha p hp1 hp2 rfin u s)
      (diffAt_liveWblk M t ha p hp1 hp2 rfin u s)
      (diffAt_Cgen M t ha p hp1 hp2 rfin hN u (s + 1) hrfin)
  · rw [show (fun x => Agen (x (structPivot M hN)) M t
          (genBlkFlatLiveR1 M t ha p hp1 hp2 (rfin x) x) (hleStruct M t ha) s) = fun _ => 0 from by
      funext x; rw [Agen, dif_neg hs]]
    exact differentiableAt_const _

/-! ## b-FrameM-2 complete: `DifferentiableAt phiFlatLiveR1` -/

/-- **b-FrameM-2 DONE.** The R1 active-center chart `phiFlatLiveR1` is `DifferentiableAt` (given the live
leaf `rfin` differentiable) — its Jacobian `DFrame_M` exists. Threads `diffAt_Agen` (per layer) through
`phiFlatLiveR1_differentiableAt_of_Agen`. This is the existence the b-FrameM-3 keystone
`toMatrix_blockTriangular_of_locality` consumes to discharge the interior-det headline's `hbt`. -/
theorem phiFlatLiveR1_differentiableAt (hN : 0 < routeMAmbient M) (u : Fin (routeMAmbient M) → ℝ)
    (hrfin : DifferentiableAt ℝ rfin u) :
    DifferentiableAt ℝ (phiFlatLiveR1 M t ha hN p hp1 hp2 rfin) u :=
  phiFlatLiveR1_differentiableAt_of_Agen M t ha hN p hp1 hp2 rfin u
    (fun s => diffAt_Agen M t ha p hp1 hp2 rfin hN u s.val hrfin)

end DLNFibre.DLN.RLCT
