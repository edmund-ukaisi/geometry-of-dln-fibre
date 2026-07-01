import DLNFibre.DLN.RLCT.Validate.RouteMInteriorLiveGenPbo
import DLNFibre.DLN.RLCT.Validate.RouteMKLDUAmbientDet

/-!
# `RouteMInteriorLiveGenAmbient` — the general-`L` multi-boundary ambient lens det at `pbo u`

The general-`L` lift of `RouteMBdetMonomial.kLDU_ambient_det_pbo` (`Fin 2`-pinned, boundary-`0`-only
via `Fin.prod_univ_two` + a vacuous leaf `k = 1`). The banked `kLDU_ambient_abs_det`
(`RouteMKLDUAmbientDet`, ∀L) already reads

  `|det D(kLDU) y| = ∏_{k : Fin L} ∏_i |(matrixSplit (readK y k)).2.1 i|^{2(t_k−1−i)}`.

This module instantiates it at `y = pbo u` and rewrites each per-boundary K-diagonal pivot via
`readK_pbo_all` (`RouteMInteriorLiveGenPbo`, ∀L: `pbo` fixes every K-slot) into the flat coordinate
`u (readKslot k i i)` — the general-`L` diagonal axis. NO `Fin.prod_univ_two`, NO leaf collapse: the
product runs over ALL boundaries `k : Fin L` (the leaf boundary's factor is the empty product `1`
automatically, since its K-index type `Fin (Text(L+1)) = Fin 0` is empty — no manual `mul_one`).

* `diagAxisGen k i := readKslot k i i` — the general-`L` diagonal K-axis (the `L = 2` `diagAxis` is
  `diagAxisGen 0`).
* `kLDU_ambient_det_pbo_gen` — `|det D(kLDU)(pbo u)| = ∏_{k : Fin L} ∏_i |u (diagAxisGen k i)|^{2(t_k−1−i)}`.

Axiom-clean `[propext, Classical.choice, Quot.sound]` (the banked ambient det + the pbo-fixing;
no analysis). Task (iii) of `genm-glift`.
-/

namespace DLNFibre.DLN.RLCT

open Matrix
open scoped BigOperators

variable {L : ℕ}

/-- **The general-`L` diagonal K-axis** at boundary `k`, index `i`: the flat coordinate reading
`readK · k i i`. The `L = 2` `RouteMBdetMonomial.diagAxis` is `diagAxisGen 0`. -/
noncomputable def diagAxisGen (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M)) (k : Fin L)
    (i : Fin (Text M (tach M) (k.val + 2))) : Fin (routeMAmbient M) :=
  readKslot M ha k i i

/-- `u (diagAxisGen k i) = readK u k i i` (the diagonal K-core entry). -/
theorem u_diagAxisGen (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M))
    (u : Fin (routeMAmbient M) → ℝ) (k : Fin L) (i : Fin (Text M (tach M) (k.val + 2))) :
    u (diagAxisGen M ha k i) = readK M (tach M) ha u k i i := by
  rw [diagAxisGen, readK_eq_readKslot]

/-- **The general-`L` ambient lens det at `pbo u`** — `|det D(kLDU)(pbo u)| =
∏_{k : Fin L} ∏_i |u (diagAxisGen k i)|^{2(t_k−1−i)}`. The banked ∀L `kLDU_ambient_abs_det` at
`y = pbo u`, with each per-boundary K-diagonal pivot `(matrixSplit (readK (pbo u) k)).2.1 i =
readK (pbo u) k i i = readK u k i i = u (diagAxisGen k i)` (`readK_pbo_all`). No leaf collapse — the
leaf boundary's K-index type is empty, so its factor is the empty product `1` automatically. -/
theorem kLDU_ambient_det_pbo_gen (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M)) (hL : 0 < L)
    (h0r : 0 < Text M (tach M) L) (h0c : 0 < Wext M L) (u : Fin (routeMAmbient M) → ℝ) :
    |LinearMap.det (fderiv ℝ (kLDU M (tach M) ha)
        (pivotBlowupOn (activeMGen M ha) (leafPivot M ha hL h0r h0c) u)).toLinearMap|
      = ∏ k : Fin L, ∏ i : Fin (Text M (tach M) (k.val + 2)),
          |u (diagAxisGen M ha k i)| ^ (2 * ((Text M (tach M) (k.val + 2) : ℕ) - 1 - (i : ℕ))) := by
  rw [kLDU_ambient_abs_det M (tach M) ha]
  refine Finset.prod_congr rfl (fun k _ => ?_)
  refine Finset.prod_congr rfl (fun i _ => ?_)
  -- `(matrixSplit (readK (pbo u) k)).2.1 i = readK (pbo u) k i i = readK u k i i = u (diagAxisGen k i)`.
  have hpiv : (matrixSplit (Matrix.of (readK M (tach M) ha
        (pivotBlowupOn (activeMGen M ha) (leafPivot M ha hL h0r h0c) u) k))).2.1 i
      = u (diagAxisGen M ha k i) := by
    rw [u_diagAxisGen M ha u k i]
    exact readK_pbo_all M ha hL h0r h0c u k i i
  rw [hpiv]

end DLNFibre.DLN.RLCT
