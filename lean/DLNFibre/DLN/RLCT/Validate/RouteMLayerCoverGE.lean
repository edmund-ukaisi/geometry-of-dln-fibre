import DLNFibre.DLN.RLCT.Validate.RouteMLayerCover

/-!
# `RouteMLayerCoverGE` — the achiever-path divergence atom (R1.6 lower bound)

The `cover_ge_div` (lower-bound) leg of the general-`M` layer-family cover, isolated to its
single load-bearing analytic atom: the **achiever-path box-integral divergence**

> for `c'` at-or-above the achiever threshold `½·minAdm M`, the flat-coordinate box integral
> `∫⁻_{[−ε,ε]^N} |routeMCore M|^{−c'}` is `⊤` for every `ε > 0`.

A pen-and-paper adjudication (`threads/20-r1-route-adjudication`) identified this as the single
most load-bearing residual atom for the general-`M` R1 gate, and the cleaner of the two cover
legs: it needs divergence along ONLY the minimum-threshold achiever leaf (one diverging leaf
suffices), so it is immune to the corank-≥2 obstruction that blocks the per-node `hnode`.

## What this banks (sorry-free)

- `layerCover_thresholdGe_half_minAdm` — per-leaf minimality: every layer leaf's
  `monomialThreshold` is `≥ ½·minAdm M` (achiever realises the min). Off `threshold_ge`.
- `layerCover_exists_thresholdLe_iff_half_le` — premise reduction: `(∃ i, threshold(i) ≤ c')`
  for the layer family is equivalent to `½·minAdm M ≤ c'` (`→` by minimality, `←` by the
  achiever leaf). This is what lets the ACHIEVER-ONLY divergence discharge the cover's `hdiv`
  field (existentially quantified over leaves) — the cert's "achiever-only suffices", in Lean.
- `layerCover_hdiv` — the `routeMLayerCover_of_atoms` `hdiv` field, DISCHARGED from the atom
  `routeMCore_box_diverges_achiever` + the premise reduction. Wiring sorry-free; the single
  open content is the analytic atom.

## The residual (the ONE honest `sorry`) and what it now costs

`routeMCore_box_diverges_achiever` is the genuine analytic content and carries the file's
single `sorry`, with a CORRECT statement. The **general-`M`** atom is still open — but it is
**reachable**, not a wall. (An earlier 2026-06-24 verdict here read "NOT reachable from the
banked machinery"; it predated the geometric anchors below and is **superseded**. The chart
route, not the squeeze, is the path.)

What the squeeze does NOT give, and why a chart is needed:
- The PROVEN squeeze (`rlctAtOn_squeeze`, `schur_recursion_step_squeeze`) computes the POINT
  RLCT `rlctAtOn (routeMCore M) 0` additively along the achiever path, giving the upper bound
  `rlctAtOn (routeMCore M) 0 ≤ ½·minAdm M`. That is STRICTLY WEAKER than this atom: `rlctAtOn ≤ t`
  is an `sSup` bound constraining only exponents STRICTLY above `t`, whereas the atom asks for
  divergence at-and-above `t` — the BOUNDARY divergence `c' = ½·minAdm M` is sharp (the monomial
  test integral `∫₀^ε u^{−1} = ⊤`) and is not implied by the point bound. (Asserting `=⊤` from
  `rlctAtOn ≤ t` would be the forbidden value-correct-germ-degenerate fill — the trap; NOT done.)
- The honest route is the flat→chart change-of-variables: a geometric `φ : box → flat` with
  `|det Dφ| = |u_p|^{minAdm M − 1}·(spectator monomial)` and `routeMCore M ∘ φ = (u_p)²·V`,
  `V` bounded + a.e.-positive on a box, so `∫ |det Dφ|·|F∘φ|^{−c'} ≥ B^{−c'}∫ u_p^{(minAdm−1)−2c'}
  = ⊤` at `c' = ½·minAdm` (exponent `−1`). `monomialIntegrand_lintegral_box_eq_top` supplies the
  sharp monomial divergence; `NodeAchieverChart M` (below) packages exactly this bundle.

The reachability evidence (banked + a decorrelated design read, 2026-06-26):
- The atom is reduced **M-agnostically, sorry-free**, to "construct one `NodeAchieverChart M`"
  (`NodeAchieverChart.lean`: `routeMCore_box_diverges_of_nodeChart`). Only the per-`M` chart
  **construction** is open.
- **Two anchors are built sorry-free**, from opposite ends of the family: `(4,4,2,2)` (pure
  radial, one weighted axis, `RouteM4422.lean`) and `(3,3,4)` (single-weighted radial, two
  weighted axes, `RouteMLayerCoverGEL2.lean`). The `(2,2,2)` `phiUnit` was the degenerate seed,
  not the only chart; the family generalises it.
- A pen-and-paper design read (`threads/32-r1-general-hdiv-design`, exact symbolic Jacobian +
  decorrelated Codex, xhigh) classifies the general atom as **NEEDS-DESIGN-then-build**: not a
  mechanical det-tactic tide (the chart's factor list is variable-length and the weighted-axis
  count grows `1→2→4`), but not the research wall either (each instance's det is a bounded
  `BlockTriangular det_comp`). The `(3,3,3,3)` instance is **build-now** (≈990 lines banked in
  `RouteM3333.lean`; only its staged det + 4-slice cov + atom remain) and is the stress-test for
  the eventual general design pass (a descent-path-indexed `φ_M` + one general composed-det lemma
  + a finite-family null-slice cov).

The WIRING into `routeMLayerCover_of_atoms` is sorry-free; the single open content is the
general-`M` chart construction.
-/

open MeasureTheory
open scoped ENNReal BigOperators

namespace DLNFibre.DLN.RLCT

variable {L : ℕ}

/-! ## The per-leaf minimality (banked, from `IsResolutionAtlas.threshold_ge`) -/

/-- **Every layer leaf's threshold is `≥ ½·minAdm M`** (for non-degenerate `1 ≤ minAdm M`). The
achiever leaf realises the minimum `½·minAdm M`; every leaf is at-or-above it. Read off the value
lane's `IsResolutionAtlas.threshold_ge` (whose `m₀ = ((Adm M).inf' Mval).toNat` is `minAdm M`
definitionally). -/
theorem layerCover_thresholdGe_half_minAdm (M : Fin (L + 1) → ℕ) (hpos : 1 ≤ minAdm M)
    (i : (routeLayerAtlas M).ι) :
    (minAdm M : ℝ≥0∞) / 2 ≤ monomialThreshold (layerD M i) (layerK M i) (layerH M i) :=
  (routeLayerAtlas_isResolutionAtlas M hpos).threshold_ge i

/-- **The achiever leaf realises `½·minAdm M`** (the `IsResolutionAtlas.achiever` clause, exposed in
the `(layerD, layerK, layerH)` tuple shape). -/
theorem layerCover_exists_achiever (M : Fin (L + 1) → ℕ) (hpos : 1 ≤ minAdm M) :
    ∃ i : (routeLayerAtlas M).ι,
      monomialThreshold (layerD M i) (layerK M i) (layerH M i) = (minAdm M : ℝ≥0∞) / 2 :=
  (routeLayerAtlas_isResolutionAtlas M hpos).achiever

/-- **The premise reduction (the "achiever-only suffices" fact).** For the layer family, the cover's
existential threshold premise `(∃ i, monomialThreshold(i) ≤ c')` is EQUIVALENT to `½·minAdm M ≤ c'`:
the `←` direction is the achiever leaf (which has `threshold = ½·minAdm M ≤ c'`), and the `→`
direction is the minimality `½·minAdm M ≤ threshold(i) ≤ c'` (`layerCover_thresholdGe_half_minAdm`).
This is why divergence along the achiever leaf alone discharges the cover's `hdiv` field — any leaf
below `c'` forces the achiever below `c'`, and the achiever is the one we diverge. -/
theorem layerCover_exists_thresholdLe_iff_half_le (M : Fin (L + 1) → ℕ) (hpos : 1 ≤ minAdm M)
    (c' : NNReal) :
    (∃ i : (routeLayerAtlas M).ι,
      monomialThreshold (layerD M i) (layerK M i) (layerH M i) ≤ (c' : ℝ≥0∞))
      ↔ (minAdm M : ℝ≥0∞) / 2 ≤ (c' : ℝ≥0∞) := by
  constructor
  · rintro ⟨i, hi⟩
    exact le_trans (layerCover_thresholdGe_half_minAdm M hpos i) hi
  · intro hle
    obtain ⟨i, hi⟩ := layerCover_exists_achiever M hpos
    exact ⟨i, hi ▸ hle⟩

/-! ## The genuine analytic atom (the ONE honest `sorry`) -/

/-- **Achiever-path box-integral divergence (R1.6 lower bound; the load-bearing residual atom).**
For `c'` at-or-above the achiever threshold `½·minAdm M`, the flat-coordinate box integral of the
threshold density `|routeMCore M|^{−c'}` over the cube `[−ε,ε]^N` is `⊤`, for every `ε > 0`.

This gives the lower bound `rlctAtOn (routeMCore M) 0 ≤ ½·minAdm M` (`cover_ge_div`, via
`routeM_coverGeDiv_of_boxDiverges` + the premise reduction below).

**HONEST RESIDUAL — NOT proven (general `M`); REACHABLE.** This carries the file's single `sorry`,
with a CORRECT statement. The banked squeeze delivers only the POINT-RLCT upper bound
`rlctAtOn ≤ ½·minAdm M`, strictly weaker than this BOUNDARY box-divergence; the route is the
flat→chart change-of-variables packaged by `NodeAchieverChart M` (see the file header). Two
instances are built sorry-free (`(4,4,2,2)`, `(3,3,4)`); the general construction is one design
pass + a bounded build away, with `(3,3,3,3)` build-now in flight (`threads/32-r1-general-hdiv-design`). -/
theorem routeMCore_box_diverges_achiever (M : Fin (L + 1) → ℕ) (hpos : 1 ≤ minAdm M)
    (c' : NNReal) (hc' : (minAdm M : ℝ≥0∞) / 2 ≤ (c' : ℝ≥0∞)) (ε : ℝ) (hε : 0 < ε) :
    ∫⁻ x in cubeBox (routeMAmbient M) ε, ENNReal.ofReal (|routeMCore M x| ^ (-(c' : ℝ))) = ⊤ := by
  sorry

/-! ## The `hdiv` field, discharged (sorry-free wiring) -/

/-- **The `routeMLayerCover_of_atoms` `hdiv` field, discharged from the achiever atom.** Given the
achiever-path divergence atom (above) and the non-degeneracy `1 ≤ minAdm M`, the cover's `hdiv`
hypothesis holds: whenever some leaf threshold is `≤ c'`, the box integral diverges. Routes the
existential premise through `layerCover_exists_thresholdLe_iff_half_le` (`∃ leaf below c'` ⟺
`½·minAdm M ≤ c'`), then applies the atom. SORRY-FREE — the only open content is the analytic
atom. -/
theorem layerCover_hdiv (M : Fin (L + 1) → ℕ) (hpos : 1 ≤ minAdm M) :
    ∀ c' : NNReal,
      (∃ i : (routeLayerAtlas M).ι,
        monomialThreshold (layerD M i) (layerK M i) (layerH M i) ≤ (c' : ℝ≥0∞)) →
      ∀ ε > 0, ∫⁻ x in cubeBox (routeMAmbient M) ε,
        ENNReal.ofReal (|routeMCore M x| ^ (-(c' : ℝ))) = ⊤ := by
  intro c' hex ε hε
  have hc' : (minAdm M : ℝ≥0∞) / 2 ≤ (c' : ℝ≥0∞) :=
    (layerCover_exists_thresholdLe_iff_half_le M hpos c').mp hex
  exact routeMCore_box_diverges_achiever M hpos c' hc' ε hε

end DLNFibre.DLN.RLCT
