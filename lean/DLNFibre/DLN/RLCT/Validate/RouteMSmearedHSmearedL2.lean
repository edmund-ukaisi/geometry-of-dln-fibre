import DLNFibre.DLN.RLCT.Validate.RouteMSmearedSquareReduce

/-!
# `RouteMSmearedHSmearedL2` — the spine's `hSmeared` slot at `L = 2`, as a NAMED atom

The ∀M achiever box-divergence SPINE (`RouteMAchieverDispatch.routeMCore_box_diverges_achiever_spine`)
discharges its BOUNDARY-SMEARED branch through a hypothesis slot

```
hSmeared : ∀ _ : 2 ≤ L, BoundarySmeared M → BoxDiverges M c' ε
```

(`BoxDiverges M c' ε := ∫⁻ x in cubeBox (routeMAmbient M) ε, |routeMCore M x|^{−c'} = ⊤`). This file
delivers that slot at `L = 2` as a single named theorem `hSmeared_L2`, so the spine's smeared branch
closes outright at `L = 2` by plugging it in (the assembly is a sibling thread's domain — this is the
NAMED atom it consumes).

## Why this is light wiring (the square-stratum reduction)

At `L = 2` the smeared branch IS the square-`P₁` stratum, with NO residual case:

* `BoundarySmeared M = ¬InteriorDrop M ∧ deepRank M < deepRows M`, and `deepRows M = M 1`.
* In the spine's regime (`1 ≤ minAdm M`), `widths_pos_of_minAdm` forces `0 < M 0, M 1, M 2`. With
  `¬InteriorDrop M`, `deepRank M < M 1`, `0 < M 2`, the L=2 `interiorDrop` characterization
  (`interiorDrop_L2_iff`) forces `deepRank M ≥ M 0`; `deepRank_le_M0` gives `deepRank M ≤ M 0`; hence
  `deepRank M = M 0` (`smeared_deepRank_eq_M0`) — the SQUARE stratum (`r = M 0`, `r + s = M 1`, `s > 0`),
  the exact hypotheses `routeMCore_smearedL2_square_uncond` consumes.

So `smearedChart_of_square` is a total chart-builder `BoundarySmeared M → SmearedAchieverChart M` on the
whole smeared-L=2 class, and `hSmeared_of_smearedChart` packages it into the spine's exact slot shape.
The fully-unconditional square box-divergence brick (`routeMCore_smearedL2_square_uncond`) is banked
sorry-free; this file is the spine-slot wiring + an explicit closer reading the slot back to the raw
integral (`hSmeared_L2_apply`).

No new analytic content; clean-three + the inherited cited `monomial_rlct` (none of its own — the
smeared box-divergence is itself S2-free, see `AxCheck`).
-/

open MeasureTheory
open scoped ENNReal BigOperators

namespace DLNFibre.DLN.RLCT

/-- **The spine's `hSmeared` slot at `L = 2`, as a named atom.** For any `M : Fin 3 → ℕ` with
`1 ≤ minAdm M`, and any `c' ≥ ½·minAdm M`, `ε > 0`, the BOUNDARY-SMEARED branch's achiever
box-divergence holds in exactly the curried shape the dispatch spine consumes:
`(2 ≤ 2) → BoundarySmeared M → ∫⁻_{cubeBox N ε} |routeMCore M|^{−c'} = ⊤`.

This is `hSmeared_of_smearedChart` instantiated at `L = 2` with the total square-stratum
chart-builder `smearedChart_of_square` (the smeared-L=2 class IS the square stratum,
`smeared_deepRank_eq_M0`). The `2 ≤ L` gate and `BoundarySmeared M` are the branch's own dispatch
conditions; the chart bundle absorbs all the geometry. Drop-in for the `hSmeared` parameter of
`routeMCore_box_diverges_achiever_spine` (with `L := 2`). -/
theorem hSmeared_L2 (M : Fin 3 → ℕ) (hpos : 1 ≤ minAdm M) (c' : NNReal)
    (hc' : (minAdm M : ℝ≥0∞) / 2 ≤ (c' : ℝ≥0∞)) (ε : ℝ) (hε : 0 < ε) :
    (2 ≤ 2) → BoundarySmeared M →
      ∫⁻ x in cubeBox (routeMAmbient M) ε,
        ENNReal.ofReal (|routeMCore M x| ^ (-(c' : ℝ))) = ⊤ :=
  hSmeared_of_smearedChart (L := 2) M (fun hsm => smearedChart_of_square M hpos hsm) c' hc' ε hε

/-- **The `hSmeared` L=2 atom, applied** — the raw box-divergence given the branch conditions, with
the trivial `2 ≤ 2` gate already discharged. A convenience reading of `hSmeared_L2` for callers that
hold `BoundarySmeared M` directly (rather than wiring the curried slot). -/
theorem hSmeared_L2_apply (M : Fin 3 → ℕ) (hpos : 1 ≤ minAdm M) (c' : NNReal)
    (hc' : (minAdm M : ℝ≥0∞) / 2 ≤ (c' : ℝ≥0∞)) (ε : ℝ) (hε : 0 < ε)
    (hsm : BoundarySmeared M) :
    ∫⁻ x in cubeBox (routeMAmbient M) ε,
      ENNReal.ofReal (|routeMCore M x| ^ (-(c' : ℝ))) = ⊤ :=
  hSmeared_L2 M hpos c' hc' ε hε (le_refl 2) hsm

end DLNFibre.DLN.RLCT
