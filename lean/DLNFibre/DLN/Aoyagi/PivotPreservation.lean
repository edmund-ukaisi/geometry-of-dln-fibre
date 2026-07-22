import DLNFibre.DLN.Aoyagi.MonumentAtlas
import DLNFibre.Core.Aoyagi.BlockBlowup
import DLNFibre.DLN.RLCT.Engine.DivBirthReach

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

/-! ## A2 — the `canonCenterOf` disjointness (freshness ⟹ earlier corner off the width-block) -/

/-- **A2 (width-block disjointness)** — an earlier divisor's diagonal birth corner
`cornerToFlat d a b` is NOT in the `widthMinUpto` block filter that `canonCenterOf` uses for
`case2`/`case12`, PROVIDED the `DivBirthInv` clause-3 freshness `a = s.layer → b < s.cleared` holds.
Pure `omega` on the filter predicate after collapsing the `image` by `tupIdxEquiv` injectivity: the
corner's `(layer, col) = (a, b)`, and the block demands `a = layer ∧ cleared ≤ b`, contradicting
freshness (`b < cleared`) when `a = layer`, and failing `q.1.1 = layer` when `a ≠ layer`. -/
theorem cornerToFlat_notMem_widthBlock {d : Fin (N + 1) → ℕ} (s : ConState N) (a b : ℕ)
    (i : Fin (flatDim d)) (hfresh : a = s.layer → b < s.cleared)
    (hcf : cornerToFlat d a b = some i) :
    i ∉ (Finset.univ.filter (fun q : tupIdx d =>
        (q.1.1 : ℕ) = s.layer ∧ s.cleared ≤ (q.1.2 : ℕ) ∧ s.cleared ≤ (q.2 : ℕ) ∧
          (q.2 : ℕ) < widthMinUpto d s.layer)).image (tupIdxEquiv d) := by
  -- Recover the corner tuple from `cornerToFlat`.
  simp only [cornerToFlat] at hcf
  split_ifs at hcf with hS hr hc
  -- hcf : some (tupIdxEquiv d ⟨⟨⟨a, hS⟩, ⟨b, hr⟩⟩, ⟨b, hc⟩⟩) = some i
  obtain rfl : tupIdxEquiv d ⟨⟨⟨a, hS⟩, ⟨b, hr⟩⟩, ⟨b, hc⟩⟩ = i := Option.some.injEq _ _ ▸ hcf
  intro hmem
  rw [Finset.mem_image] at hmem
  obtain ⟨q, hq, hqi⟩ := hmem
  rw [Finset.mem_filter] at hq
  -- `tupIdxEquiv` injective: `q = ⟨⟨⟨a,_⟩,⟨b,_⟩⟩,⟨b,_⟩⟩`.
  obtain rfl : q = ⟨⟨⟨a, hS⟩, ⟨b, hr⟩⟩, ⟨b, hc⟩⟩ := (tupIdxEquiv d).injective hqi
  obtain ⟨_, hP1, hP2, hP3, hP4⟩ := hq
  simp only at hP1 hP2 hP3 hP4
  -- hP1 : a = s.layer,  hP3 : s.cleared ≤ b,  freshness contradicts.
  omega

/-- **A2 (row-block disjointness)** — the `case11` row-block analog: the same freshness `omega`
excludes the earlier corner from the `[cleared, cleared+runLen)` row-block that `canonCenterOf(case11)`
adjoins to the reused pivot. -/
theorem cornerToFlat_notMem_rowBlock {d : Fin (N + 1) → ℕ} (s : ConState N) (runLen a b : ℕ)
    (i : Fin (flatDim d)) (hfresh : a = s.layer → b < s.cleared)
    (hcf : cornerToFlat d a b = some i) :
    i ∉ (Finset.univ.filter (fun q : tupIdx d =>
        (q.1.1 : ℕ) = s.layer ∧ s.cleared ≤ (q.1.2 : ℕ) ∧ s.cleared ≤ (q.2 : ℕ) ∧
          (q.2 : ℕ) < s.cleared + runLen)).image (tupIdxEquiv d) := by
  simp only [cornerToFlat] at hcf
  split_ifs at hcf with hS hr hc
  obtain rfl : tupIdxEquiv d ⟨⟨⟨a, hS⟩, ⟨b, hr⟩⟩, ⟨b, hc⟩⟩ = i := Option.some.injEq _ _ ▸ hcf
  intro hmem
  rw [Finset.mem_image] at hmem
  obtain ⟨q, hq, hqi⟩ := hmem
  rw [Finset.mem_filter] at hq
  obtain rfl : q = ⟨⟨⟨a, hS⟩, ⟨b, hr⟩⟩, ⟨b, hc⟩⟩ := (tupIdxEquiv d).injective hqi
  obtain ⟨_, hP1, hP2, hP3, hP4⟩ := hq
  simp only at hP1 hP2 hP3 hP4
  omega

/-! ## A3 — `DivBirthInv` holds along a real branch (supplies A2's freshness) -/

/-- **A3** — every node of a real branch carries `DivBirthInv` (TreePath induction off
`DivBirthInv_conRoot` + `DivBirthInv_conOracle_stepChildren`; a step's `conState` is its recorded
`nextState = sc.child`). Gives, at each deeper node, the clause-3 freshness A2 consumes for the
earlier (persisted, immutable) birth corner. -/
theorem divBirthInv_of_isRealBranch {d : Fin (N + 1) → ℕ}
    (e : (Fin (flatDim d) → ℝ) ≃ₜ Tuple (k := ℝ) d) :
    ∀ p : TreePath d, p.IsRealBranch e → DivBirthInv d p.conState := by
  intro p
  induction p with
  | root => intro _; exact DivBirthInv_conRoot
  | step p center pivot cse nextState shearφ ih =>
    intro hbranch
    obtain ⟨hrec, ⟨sc, hsc_mem, _hecase, hchild, _hcenter, _hpiv⟩, _hshear⟩ := hbranch
    have hp : DivBirthInv d p.conState := ih hrec
    have hchildInv := DivBirthInv_conOracle_stepChildren p.conState hp sc hsc_mem
    show DivBirthInv d nextState
    exact hchild ▸ hchildInv

end DLNFibre.DLN.Aoyagi.PivotPres
