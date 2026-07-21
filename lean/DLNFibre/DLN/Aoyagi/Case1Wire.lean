import DLNFibre.DLN.Aoyagi.MonumentAtlas
import DLNFibre.Core.Aoyagi.BlockDivision

/-!
# `DLN.Aoyagi.Case1Wire` — the wall's crux, wired to the fold defs (SEAT-L4)

The reusable per-entry FIX-RESID identity that discharges the δ=1 divisibility of
`case1_preserves_stepInv` (and `case2` δ=1) against the CONCRETE fold defs (`foldResid`, `stepMap`,
`edgeShear`), using `Deg1SupportedOn`'s center-exact degree-1 structure + seat-L4's `BlockDivision`
FIX-A enabler. Kept in a separate file (not `MonumentAtlas`) during the canonCenter parallel-dev round.
-/

open MeasureTheory Set Filter Topology RLCT
open DLNFibre.Core DLNFibre.Core.Aoyagi

namespace DLNFibre.DLN.Aoyagi

variable {N : ℕ}

/-- **The edge shear keeps the pivot coordinate** — `id` at case11/rollover, `blockShear` (via
`hshear_pivot`) at case12/case2. The uniform fact the FIX-A center-division consumes. -/
theorem edgeShear_keeps_pivot (d : Fin (N + 1) → ℕ) {p : TreePath d} (ed : TreeEdge d p)
    (u : Fin (flatDim d) → ℝ) : edgeShear d ed u ed.pivot = u ed.pivot := by
  unfold edgeShear edgeShearRaw
  split
  · rfl
  · rfl
  · exact ed.hshear_pivot u
  · exact ed.hshear_pivot u

/-- **The FIX-RESID per-entry identity (the wall's δ=1 crux).** For a `Deg1SupportedOn` parent residual
(center `ed.center`), the parent residual pulled back through `stepMap` (blow-up OUTERMOST) factors as
`u_pivot ·` the residual at the `blockBlowupCoordQuot`-map (the strict transform): each center
coordinate gains the pivot factor (`blockBlowupMap_shear_center_eq`, FIX-A) and the center-DISJOINT
coefficient is unchanged (`IgnoresCoords`, since `stepMap u` and the quot-map agree off the center). -/
theorem foldResid_stepMap_eq_pivot_mul (d : Fin (N + 1) → ℕ)
    (e : (Fin (flatDim d) → ℝ) ≃ₜ Tuple (k := ℝ) d) {p : TreePath d} (ed : TreeEdge d p)
    (hdeg1 : Deg1SupportedOn (foldResid d e p) ed.center (foldRegion d e p))
    (j : Fin (foldNR d p)) (u : Fin (flatDim d) → ℝ) :
    foldResid d e p j (stepMap d ed u)
      = u ed.pivot
        * foldResid d e p j (fun k ↦ blockBlowupCoordQuot ed.pivot k (edgeShear d ed u)) := by
  classical
  -- the quot-map and its off-center agreement with `stepMap u`
  set qm : Fin (flatDim d) → ℝ := fun k ↦ blockBlowupCoordQuot ed.pivot k (edgeShear d ed u) with hqm
  set σu : Fin (flatDim d) → ℝ := stepMap d ed u with hσu
  have hσu_eq : ∀ k, σu k = blockBlowupMap ed.center ed.pivot (edgeShear d ed u) k := fun k ↦ rfl
  -- off-center, `σu` and `qm` agree (spectators of the blow-up are the shear's values; the coord quot
  -- off-pivot is the shear's value too).
  have hagree : ∀ s, s ∉ ed.center → σu s = qm s := by
    intro s hs
    have hsp : s ≠ ed.pivot := fun h ↦ hs (h ▸ ed.hpivot)
    rw [hσu_eq s, blockBlowupMap, hqm, blockBlowupCoordQuot]
    simp [hsp, hs]
  -- the Deg1 witness for entry `j`
  obtain ⟨c, _hc, hrepr, hign⟩ := hdeg1 j
  have hmem : ∀ w : Fin (flatDim d) → ℝ, w ∈ foldRegion d e p := by
    rw [foldRegion_eq_univ]; exact fun w ↦ Set.mem_univ w
  -- coefficients agree at `σu` and `qm` (they agree off center; `c i` ignores center)
  have hceq : ∀ i, c i σu = c i qm := by
    intro i
    have := (ignoresCoords_univ_iff_agree (c i) ed.center)
    rw [foldRegion_eq_univ] at hign
    exact (this.mp (hign i)) σu qm hagree
  rw [hrepr σu (hmem _), hrepr qm (hmem _), Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i hi ↦ ?_)
  have hcenter : σu i = u ed.pivot * qm i := by
    rw [hσu_eq i, hqm]
    exact blockBlowupMap_shear_center_eq ed.center ed.pivot hi (edgeShear d ed)
      (edgeShear_keeps_pivot d ed) u
  rw [hceq i, hcenter]; ring

end DLNFibre.DLN.Aoyagi
