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

So `smearedChart_of_square` is a total chart-builder `BoundarySmeared M → SmearedAchieverChart M` on
the whole smeared-L=2 class. The banked closer `hSmeared_squareSmeared_L2` fires it through the
M-agnostic `routeMCore_box_diverges_of_smearedChart` to give the raw box-divergence; this file
CURRIES that closer into the spine's exact `∀ _ : 2 ≤ L, BoundarySmeared M → BoxDiverges M c' ε` slot
shape (`hSmeared_L2`), and re-exposes the uncurried form (`hSmeared_L2_apply`).

No new analytic content (the fully-unconditional square box-divergence
`routeMCore_smearedL2_square_uncond` is banked sorry-free); clean-three, S2-free — the smeared
box-divergence carries no `monomial_rlct` (see `AxCheck`).
-/

open MeasureTheory
open scoped ENNReal BigOperators

namespace DLNFibre.DLN.RLCT

/-- **The spine's `hSmeared` slot at `L = 2`, as a named atom.** For any `M : Fin 3 → ℕ` with
`1 ≤ minAdm M`, and any `c' ≥ ½·minAdm M`, `ε > 0`, the BOUNDARY-SMEARED branch's achiever
box-divergence holds in exactly the curried shape the dispatch spine consumes:
`(2 ≤ 2) → BoundarySmeared M → ∫⁻_{cubeBox N ε} |routeMCore M|^{−c'} = ⊤`.

The body curries the banked closer `hSmeared_squareSmeared_L2` (which routes the smeared branch
through the square stratum `deepRank M = M 0`, `smeared_deepRank_eq_M0`, into the
fully-unconditional square box-divergence). The `2 ≤ L` gate and `BoundarySmeared M` are the
branch's own dispatch conditions. Drop-in for the `hSmeared` parameter of
`routeMCore_box_diverges_achiever_spine` (with `L := 2`). -/
theorem hSmeared_L2 (M : Fin 3 → ℕ) (hpos : 1 ≤ minAdm M) (c' : NNReal)
    (hc' : (minAdm M : ℝ≥0∞) / 2 ≤ (c' : ℝ≥0∞)) (ε : ℝ) (hε : 0 < ε) :
    (2 ≤ 2) → BoundarySmeared M →
      ∫⁻ x in cubeBox (routeMAmbient M) ε,
        ENNReal.ofReal (|routeMCore M x| ^ (-(c' : ℝ))) = ⊤ :=
  fun _ hsm => hSmeared_squareSmeared_L2 M hpos c' hc' ε hε hsm

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
