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
  change edgeShearRaw d ed.case ed.shearφ u ed.pivot = u ed.pivot
  cases ed.case
  · rfl                       -- case11: `id`
  · exact ed.hshear_pivot u   -- case12: `blockShear`
  · exact ed.hshear_pivot u   -- case2:  `blockShear`
  · rfl                       -- rollover: `id`

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
    rw [hσu_eq s, blockBlowupMap_spectator_eq ed.center ed.hpivot hs (edgeShear d ed u), hqm]
    change edgeShear d ed u s = (if s = ed.pivot then (1 : ℝ) else edgeShear d ed u s)
    rw [if_neg hsp]
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

/-! ### Child-state reductions (conjunct-2 plumbing, seat-L4)

The `foldResid`/`foldNR` values at a non-terminal child `p.extend ed`, split by `edgeδ`. Consumed
by `case1_preserves_stepInv`'s conjunct-2 (the descend of `Deg1SupportedSlot`, parent to child). All
proof-free reductions off the fold defs; `hlt : ¬ N ≤ ed.nextState.layer` comes from `hlayer`. -/

/-- The child residual width is the parent's at a non-terminal step (`foldNR` collapses to `1` only
at a TERMINAL child). -/
theorem foldNR_extend_of_lt (d : Fin (N + 1) → ℕ) {p : TreePath d} (ed : TreeEdge d p)
    (hlt : ¬ N ≤ ed.nextState.layer) : foldNR d (p.extend ed) = foldNR d p := by
  change (if N ≤ ed.nextState.layer then 1 else foldNR d p) = foldNR d p
  rw [if_neg hlt]

/-- **δ=1 child residual = parent's STRICT TRANSFORM** at a non-terminal case edge: the
pivot-quotiented sheared point (`blockBlowupCoordQuot` removes the blow-up `u_pivot`). -/
theorem foldResid_extend_delta1 (d : Fin (N + 1) → ℕ)
    (e : (Fin (flatDim d) → ℝ) ≃ₜ Tuple (k := ℝ) d) {p : TreePath d} (ed : TreeEdge d p)
    (hlt : ¬ N ≤ ed.nextState.layer) (hδ : edgeδ d p = true)
    (j : Fin (foldNR d (p.extend ed))) (u : Fin (flatDim d) → ℝ) :
    foldResid d e (p.extend ed) j u
      = foldResid d e p (Fin.cast (foldNR_extend_of_lt d ed hlt) j)
          (fun k ↦ blockBlowupCoordQuot ed.pivot k (edgeShear d ed u)) := by
  change foldResid d e (TreePath.step p ed.center ed.pivot ed.case ed.nextState ed.shearφ) j u = _
  rw [foldResid, dif_neg hlt, if_pos hδ]; rfl

/-- **δ=0 child residual = parent's PULLBACK** at a non-terminal case edge (no `u_pivot`). -/
theorem foldResid_extend_delta0 (d : Fin (N + 1) → ℕ)
    (e : (Fin (flatDim d) → ℝ) ≃ₜ Tuple (k := ℝ) d) {p : TreePath d} (ed : TreeEdge d p)
    (hlt : ¬ N ≤ ed.nextState.layer) (hδ : edgeδ d p = false)
    (j : Fin (foldNR d (p.extend ed))) (u : Fin (flatDim d) → ℝ) :
    foldResid d e (p.extend ed) j u
      = foldResid d e p (Fin.cast (foldNR_extend_of_lt d ed hlt) j) (stepMap d ed u) := by
  change foldResid d e (TreePath.step p ed.center ed.pivot ed.case ed.nextState ed.shearφ) j u = _
  rw [foldResid, dif_neg hlt, if_neg (by simp [hδ])]; rfl

end DLNFibre.DLN.Aoyagi
