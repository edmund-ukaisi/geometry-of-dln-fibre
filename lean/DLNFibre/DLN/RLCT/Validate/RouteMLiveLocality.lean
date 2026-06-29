import DLNFibre.DLN.RLCT.Validate.RouteMLayerGrade
import DLNFibre.DLN.RLCT.Validate.RouteMFlatLive

/-!
# `RouteMLiveLocality` — the value-level layer-locality LIFTED to the live decoder `genBlkFlatLiveR1`

The b-0 off-block-vanishing for the LIVE decoder (`item3-frameM-buildspec.md`, the "carry the locality
to `genBlkFlatLiveR1`" note): `Agen` of the R1 active-center chart at layer `s` reads only input layers
`≤ s`, exactly as for the dead-leaf `genBlkFlatStruct` (`Agen_genBlkFlatStruct_reads_le`, banked). The
live decoder differs from the structured one ONLY by:
* `Rmat` = `Function.update (struct.Rmat) p (const)` — at the fixed pivot `p`, so for `j ≠ p` it is the
  struct's `Rmat` (`update_of_ne`; the struct locality carries), and at `j = p` it is the fixed const
  (trivially `x`-invariant).
* `Rfin L` = `rfin` (the live leaf) — carried by a hypothesis `rfinx = rfiny` (the leaf reader's
  layer-locality; the budget-piece reader supplies it, the same shape as the chart's `rfin` argument).

`Bmat`/`Nblk`/`Wblk` are the struct's verbatim, so their `_indep_of` lemmas carry directly.

* `genBlkFlatLiveR1_Rmat_indep` — the live `Rmat (j+1)` is invariant under changing `x` away from layer
  `j` (the `update`-at-fixed-pivot handling).
* `Agen_genBlkFlatLiveR1_reads_le` — the live-decoder locality: `Agen … s` reads only layers `≤ s`
  (given the leaf-reader hypothesis `rfinx = rfiny`).

Axiom-clean `[propext, Classical.choice, Quot.sound]` (the banked struct locality + `update`/`dite`
handling; no analysis).
-/

open scoped BigOperators
open Matrix

namespace DLNFibre.DLN.RLCT

variable {L : ℕ}

/-- **The live `Rmat (j+1)` is invariant under changing `x` away from layer `j`.** `Function.update`
at the fixed pivot `p`: for `j+1 = p` it is the fixed const (invariant); for `j+1 ≠ p` it is the
struct's `Rmat (j+1)` (via `update_of_ne` + `genBlkFlatStruct_Rmat_indep_of`). -/
theorem genBlkFlatLiveR1_Rmat_indep (M t : Fin (L + 1) → ℕ) (ha : StructAdm M t) (p : ℕ)
    (hp1 : Text M t (p + 1) ≤ Text M t p) (hp2 : Text M t (p + 1) ≤ Wext M p)
    (x y : Fin (routeMAmbient M) → ℝ) (rfinx rfiny : Matrix (Fin (Text M t L)) (Fin (Wext M L)) ℝ)
    (j : ℕ) (hj : j < L) (h : ∀ q, bLayer M t ha q = j → x q = y q) :
    (genBlkFlatLiveR1 M t ha p hp1 hp2 rfinx x).Rmat (j + 1)
      = (genBlkFlatLiveR1 M t ha p hp1 hp2 rfiny y).Rmat (j + 1) := by
  show Function.update (genBlkFlatLive M t ha rfinx x).Rmat p
      (rmatPad M t p hp1 hp2 (pivotEIndicator M t p)) (j + 1)
    = Function.update (genBlkFlatLive M t ha rfiny y).Rmat p
      (rmatPad M t p hp1 hp2 (pivotEIndicator M t p)) (j + 1)
  by_cases hjp : (j + 1) = p
  · rw [hjp, Function.update_self, Function.update_self]
  · rw [Function.update_of_ne hjp, Function.update_of_ne hjp]
    exact genBlkFlatStruct_Rmat_indep_of M t ha x y j hj h

/-- **VERIFY-1 for the LIVE decoder: `Agen` of the R1 chart at layer `s` reads only layers `≤ s`.**
If `x`, `y` agree on every coordinate at layer `≤ s` and the leaf readers agree (`rfinx = rfiny`), the
layer-`s` chart parameter is unchanged. The live-decoder analog of `Agen_genBlkFlatStruct_reads_le`,
the off-block-vanishing the fused frame's block-triangularity rests on (the `hloc` content). -/
theorem Agen_genBlkFlatLiveR1_reads_le (M t : Fin (L + 1) → ℕ) (ha : StructAdm M t) (p : ℕ)
    (hp1 : Text M t (p + 1) ≤ Text M t p) (hp2 : Text M t (p + 1) ≤ Wext M p)
    (u : ℝ) (x y : Fin (routeMAmbient M) → ℝ) (s : ℕ)
    (rfinx rfiny : Matrix (Fin (Text M t L)) (Fin (Wext M L)) ℝ)
    (h : ∀ q, bLayer M t ha q ≤ s → x q = y q) (hrfin : rfinx = rfiny) :
    Agen u M t (genBlkFlatLiveR1 M t ha p hp1 hp2 rfinx x) (hleStruct M t ha) s
      = Agen u M t (genBlkFlatLiveR1 M t ha p hp1 hp2 rfiny y) (hleStruct M t ha) s := by
  by_cases hs : s < L
  · have hNs : (genBlkFlatLiveR1 M t ha p hp1 hp2 rfinx x).Nblk s
        = (genBlkFlatLiveR1 M t ha p hp1 hp2 rfiny y).Nblk s := by
      show (genBlkFlatStruct M t ha x).Nblk s = (genBlkFlatStruct M t ha y).Nblk s
      match s with
      | 0 => rfl
      | (j + 1) =>
        exact genBlkFlatStruct_Nblk_indep_of M t ha x y j (by omega) (fun q hq => h q (by omega))
    have hWs : (genBlkFlatLiveR1 M t ha p hp1 hp2 rfinx x).Wblk s
        = (genBlkFlatLiveR1 M t ha p hp1 hp2 rfiny y).Wblk s := by
      show (genBlkFlatStruct M t ha x).Wblk s = (genBlkFlatStruct M t ha y).Wblk s
      match s with
      | 0 => rfl
      | (j + 1) =>
        exact genBlkFlatStruct_Wblk_indep_of M t ha x y j (by omega) (fun q hq => h q (by omega))
    have hBs1 : (genBlkFlatLiveR1 M t ha p hp1 hp2 rfinx x).Bmat (s + 1)
        = (genBlkFlatLiveR1 M t ha p hp1 hp2 rfiny y).Bmat (s + 1) := by
      show (genBlkFlatStruct M t ha x).Bmat (s + 1) = (genBlkFlatStruct M t ha y).Bmat (s + 1)
      exact genBlkFlatStruct_Bmat_indep_of M t ha x y s hs (fun q hq => h q (by omega))
    have hNs1 : (genBlkFlatLiveR1 M t ha p hp1 hp2 rfinx x).Nblk (s + 1)
        = (genBlkFlatLiveR1 M t ha p hp1 hp2 rfiny y).Nblk (s + 1) := by
      show (genBlkFlatStruct M t ha x).Nblk (s + 1) = (genBlkFlatStruct M t ha y).Nblk (s + 1)
      exact genBlkFlatStruct_Nblk_indep_of M t ha x y s hs (fun q hq => h q (by omega))
    have hRs1 : (genBlkFlatLiveR1 M t ha p hp1 hp2 rfinx x).Rmat (s + 1)
        = (genBlkFlatLiveR1 M t ha p hp1 hp2 rfiny y).Rmat (s + 1) :=
      genBlkFlatLiveR1_Rmat_indep M t ha p hp1 hp2 x y rfinx rfiny s hs (fun q hq => h q (by omega))
    have hCs1 : Cgen u M t (genBlkFlatLiveR1 M t ha p hp1 hp2 rfinx x) (hleStruct M t ha) (s + 1)
        = Cgen u M t (genBlkFlatLiveR1 M t ha p hp1 hp2 rfiny y) (hleStruct M t ha) (s + 1) := by
      by_cases hs1 : s + 1 < L
      · simp only [Cgen, dif_pos hs1, hBs1, hNs1, hRs1]
      · -- leaf: `s + 1 = L` (from `s < L`, `¬ s+1 < L`); `Cgen L = u • Rfin L = u • rfin`.
        have hsL : s + 1 = L := by omega
        subst hsL
        have hRfin : (genBlkFlatLiveR1 M t ha p hp1 hp2 rfinx x).Rfin (s + 1)
            = (genBlkFlatLiveR1 M t ha p hp1 hp2 rfiny y).Rfin (s + 1) := by
          show (genBlkFlatLive M t ha rfinx x).Rfin (s + 1)
            = (genBlkFlatLive M t ha rfiny y).Rfin (s + 1)
          rw [show (genBlkFlatLive M t ha rfinx x).Rfin (s + 1) = rfinx from by simp [genBlkFlatLive],
              show (genBlkFlatLive M t ha rfiny y).Rfin (s + 1) = rfiny from by simp [genBlkFlatLive],
              hrfin]
        simp only [Cgen, dif_neg hs1, hRfin]
    simp only [Agen, dif_pos hs, hNs, hWs, hCs1]
  · simp only [Agen, dif_neg hs]

end DLNFibre.DLN.RLCT
