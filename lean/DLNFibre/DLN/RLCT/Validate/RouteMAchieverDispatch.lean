import DLNFibre.DLN.RLCT.Validate.RouteMDeepBottleneck
import DLNFibre.DLN.RLCT.Validate.RouteMBoundaryCleanChartFull

/-!
# `RouteMAchieverDispatch` — the ∀M achiever box-divergence SPINE (4-way dispatch)

The spine-first assembly of the R1-LOWER leg headline `routeMCore_box_diverges_achiever`
(`RouteMLayerCoverGE:133`). It establishes the **dispatch logic** — every `M` with `1 ≤ minAdm M`
routes to exactly one of four branches — discharging the parts already DONE (`L = 0` vacuity, the
`2 ≤ L` trichotomy via the banked `achiever_trichotomy_total`, and the BOUNDARY-CLEAN branch via the
banked `routeMCore_box_diverges_clean`), and leaving the not-yet-built branches as PRECISELY-STATED
hypotheses (`L = 1`, INTERIOR, BOUNDARY-SMEARED). This reveals exactly the box-divergence each open
branch owes, and de-risks the dispatch before filling the heavy charts.

`routeMCore_box_diverges_achiever_spine` — the spine, sorry-free GIVEN the open-branch atoms:

* `L = 0` is VACUOUS (`minAdm M = 0` contradicts `hpos`).
* `L = 1` is ALWAYS BOUNDARY-CLEAN (`deepRank = deepRows = M 0`, `deepRank_eq_deepRows_L1`), so it
  routes through the banked `routeMCore_box_diverges_clean` — NO separate `L = 1` atom needed (the
  single-deepest-factor node is the cleanest radial).
* `2 ≤ L`, by `achiever_trichotomy_total` (UNCONDITIONALLY total, `deepRank ≤ deepRows` proven):
  - INTERIOR (`InteriorDrop M`) → `hInterior` (the colPath Schur chart atom — `#3`, the heaviest).
  - BOUNDARY-CLEAN (`deepRank = deepRows`) → the banked `routeMCore_box_diverges_clean` (DONE),
    given its structural side-conditions (`hNo`, `hne`, `hMpos` — carried as spine hyps; the clean
    chart is the whole-deepest radial).
  - BOUNDARY-SMEARED (`deepRank < deepRows`) → `hSmeared` (the rational single-pivot atom, `#2`
    verdict BOUNDED — assembled per-family via `routeMCore_box_diverges_smearedContract`). The
    smeared branch's chart needs the width-`r` waist, which rests on `NoInteriorBothDrop` (the
    interior Aoyagi blocks vanish); the spine HAS `hNo`, so the `hSmeared` slot threads it (the
    smeared stratum is genuinely `BoundarySmeared ∧ NoInteriorBothDrop`).

The dispatch itself is sorry-free; the open content is the TWO `2 ≤ L` branch atoms (INTERIOR,
SMEARED — each a hypothesis here, to be discharged by its per-branch build). The spine's axioms are
clean-three + the cited `monomial_rlct` (inherited from the clean branch's monomial atom); it adds
none of its own.
-/

open MeasureTheory
open scoped ENNReal BigOperators

namespace DLNFibre.DLN.RLCT

variable {L : ℕ}

/-- The achiever box-divergence conclusion for `M` at `(c', ε)` — the headline's RHS, abbreviated so
the branch hypotheses read uniformly. -/
abbrev BoxDiverges (M : Fin (L + 1) → ℕ) (c' : NNReal) (ε : ℝ) : Prop :=
  ∫⁻ x in cubeBox (routeMAmbient M) ε,
    ENNReal.ofReal (|routeMCore M x| ^ (-(c' : ℝ))) = ⊤

/-- **`L = 1` is always BOUNDARY-CLEAN** (`deepRank M = deepRows M`): the single deepest factor IS
the rank-carrying block. `deepRank = Text(tach)(1) = tach 0 = M 0`; `deepRows = Wext(0) = M 0`. So
the single-layer node needs no separate branch — it routes through the banked clean discharge. -/
theorem deepRank_eq_deepRows_L1 (M : Fin (1 + 1) → ℕ) : deepRank M = deepRows M := by
  have hdr : deepRank M = M 0 := by
    have h1 : Text M (tach M) (0 + 1) = tach M ⟨0, by omega⟩ := Text_succ M (tach M) 0 (by omega)
    rw [deepRank]
    exact h1.trans (tach_mk_zero M (by omega))
  have hrows : deepRows M = M 0 := by
    rw [deepRows]
    exact (Wext_apply M (1 - 1) (by omega)).trans rfl
  rw [hdr, hrows]

/-- **`NoInteriorBothDrop` holds vacuously at `L = 1`** (no `s` with `1 ≤ s < 1`). -/
theorem noInteriorBothDrop_L1 (M : Fin (1 + 1) → ℕ) : NoInteriorBothDrop M := by
  intro s hs hsl; omega

/-- **The ∀M achiever box-divergence SPINE (4-way dispatch).** For any `M` with `1 ≤ minAdm M`, the
achiever box integral diverges, GIVEN the three open-branch atoms (`L = 1`, INTERIOR,
BOUNDARY-SMEARED) and the BOUNDARY-CLEAN structural side-conditions. The dispatch (`L = 0` vacuity +
the `2 ≤ L` trichotomy + the clean branch's banked discharge) is sorry-free. This IS the headline
`routeMCore_box_diverges_achiever`, modulo the three stated branch obligations — the spine that
reveals what each owes and de-risks the assembly.

The clean branch's `hNo`/`hne`/`hMpos` are the structural preconditions
`routeMCore_box_diverges_clean` consumes (not derivable from `BoundaryClean` alone here): all widths
positive, the deepest block nonempty, no interior both-drop. They are decidable structural facts the
caller establishes per `M`. -/
theorem routeMCore_box_diverges_achiever_spine (M : Fin (L + 1) → ℕ) (hpos : 1 ≤ minAdm M)
    (c' : NNReal) (hc' : (minAdm M : ℝ≥0∞) / 2 ≤ (c' : ℝ≥0∞)) (ε : ℝ) (hε : 0 < ε)
    (hMpos : ∀ s, 0 < M s)
    (hne : ∀ hL : 0 < L, (deepestCoords M hL).Nonempty)
    (hNo : NoInteriorBothDrop M)
    (hInterior : ∀ _ : 2 ≤ L, InteriorDrop M → BoxDiverges M c' ε)
    (hSmeared : ∀ _ : 2 ≤ L, BoundarySmeared M → NoInteriorBothDrop M → BoxDiverges M c' ε) :
    BoxDiverges M c' ε := by
  rcases Nat.lt_or_ge L 2 with hLlt | hL2
  · -- `L < 2`: either `L = 0` (vacuous) or `L = 1` (always boundary-clean → the banked discharge).
    interval_cases L
    · -- `L = 0`: `minAdm M = 0` contradicts `hpos`.
      exact absurd hpos (by rw [show minAdm M = 0 from by rw [← minAdmRec_eq_minAdm]; rfl]; omega)
    · -- `L = 1`: always boundary-clean (`deepRank = deepRows = M 0`), routed through the banked
      -- clean discharge — NO separate L = 1 atom needed.
      exact routeMCore_box_diverges_clean M (by omega) (hne (by omega)) (noInteriorBothDrop_L1 M)
        (deepRank_eq_deepRows_L1 M) hpos hMpos c' hc' ε hε
  · -- `2 ≤ L`: the unconditionally-total trichotomy.
    rcases achiever_trichotomy_total M hL2 with hInt | hClean | hSmear
    · exact hInterior hL2 hInt
    · -- BOUNDARY-CLEAN: the banked whole-deepest radial discharge.
      exact routeMCore_box_diverges_clean M (by omega) (hne (by omega)) hNo hClean.2 hpos hMpos
        c' hc' ε hε
    · exact hSmeared hL2 hSmear hNo

end DLNFibre.DLN.RLCT
