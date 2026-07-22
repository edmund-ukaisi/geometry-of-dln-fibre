import DLNFibre.DLN.Aoyagi.MonumentAtlas
import DLNFibre.Core.Aoyagi.BlockBlowup

/-!
# `DLN.Aoyagi.PivotPreservation` — M4: the (★) pivot-preservation core

The producer-side of L5's Jacobian-collapse clause (`FoldRealizes` third conjunct): each step's
pivot coordinate is preserved by all deeper steps, so the per-step Jacobian monomials evaluate at the
same source pivot value and telescope to `jacWeight (jac c)` with unit ≡ 1 (`chart_of_collapse`
consumes the collapse; this file produces the (★) it rests on). Route R2 (bridge-free): worked on
`canonCenterOf`/`cornerToFlat`/`divBirthCoord` directly (the `tupIdxEquiv` encoding), NOT the engine
`flatCoordOf` machinery.

Atom family (L5FoldSpec §E, M4):
* **A1** `blockBlowupMap` fixes the pivot and fixes off-center coordinates (raw def facts).
* **A2** `canonCenterOf` disjointness: an earlier divisor's birth corner is fixed by a deeper step's
  block blow-up — it is either the deeper pivot (fixed) or off the deeper center (fixed); a NON-pivot
  center membership is excluded by `DivBirthInv` clause-3 freshness (`a = layer → b < cleared`).
* A3 `DivBirthInv` along a real branch + `divBirthCoord` persistence (supplies A2's freshness).
* A4 clause-III shear extraction at an earlier corner (via A3).
* A5 the branch-level (★) glue over the path suffix (foldG frame), for L5's collapse (§D.3).
-/

open MeasureTheory Set Filter Topology RLCT
open DLNFibre.Core DLNFibre.Core.Aoyagi DLNFibre.DLN.RLCT DLNFibre.DLN.RLCT.Engine

namespace DLNFibre.DLN.Aoyagi.PivotPres

variable {N : ℕ}

/-! ## A1 — raw `blockBlowupMap` fixed-coordinate atoms -/

/-- **A1a** — the block blow-up fixes its pivot coordinate (`= w p`, def's first branch). -/
theorem blockBlowupMap_apply_pivot {D : ℕ} (S : Finset (Fin D)) (p : Fin D) (w : Fin D → ℝ) :
    blockBlowupMap S p w p = w p := by
  simp [blockBlowupMap]

/-- **A1b** — the block blow-up fixes every coordinate off its center (`c₀ ∉ S ⟹ = w c₀`); holds even
if `c₀ = p` (then both sides are `w p`). -/
theorem blockBlowupMap_fixes_offCenter {D : ℕ} (S : Finset (Fin D)) (p : Fin D) (w : Fin D → ℝ)
    (c₀ : Fin D) (h : c₀ ∉ S) : blockBlowupMap S p w c₀ = w c₀ := by
  unfold blockBlowupMap
  split_ifs with h1
  · exact congrArg w h1.symm
  · rfl

/-- **A1 (the fixed-point criterion)** — `blockBlowupMap S p` fixes `c₀` whenever `c₀` is the pivot or
lies off the center. This is exactly the shape the (★) blow-up half needs: a deeper step fixes an
earlier pivot corner because that corner is the deeper pivot (case-1 re-pivot) or off the deeper
center (A2). -/
theorem blockBlowupMap_fixes_of_pivot_or_offCenter {D : ℕ} (S : Finset (Fin D)) (p : Fin D)
    (w : Fin D → ℝ) (c₀ : Fin D) (h : c₀ = p ∨ c₀ ∉ S) :
    blockBlowupMap S p w c₀ = w c₀ := by
  rcases h with h | h
  · subst h; exact blockBlowupMap_apply_pivot S c₀ w
  · exact blockBlowupMap_fixes_offCenter S p w c₀ h

end DLNFibre.DLN.Aoyagi.PivotPres
