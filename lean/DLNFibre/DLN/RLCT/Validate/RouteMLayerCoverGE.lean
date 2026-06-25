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

## The residual (the ONE honest `sorry` — the genuine R1.6 lower-bound mountain)

`routeMCore_box_diverges_achiever` is the genuine analytic content and carries the file's
single `sorry`, with a CORRECT statement. The verdict (this thread's validation + a
decorrelated `local-codex-consult`, 2026-06-24): the atom is NOT reachable from the banked
machinery.

- The PROVEN squeeze (`rlctAtOn_squeeze`, `schur_recursion_step_squeeze`) computes the POINT
  RLCT `rlctAtOn (routeMCore M) 0` additively along the achiever path, giving the upper bound
  `rlctAtOn (routeMCore M) 0 ≤ ½·minAdm M`. That is STRICTLY WEAKER than this atom: `rlctAtOn ≤ t`
  is an `sSup` bound constraining only exponents STRICTLY above `t`, whereas the atom asks for
  divergence at-and-above `t` — the BOUNDARY divergence `c' = ½·minAdm M` is sharp (the monomial
  test integral `∫₀^ε u^{−1} = ⊤`) and is not implied by the point bound. (Asserting `=⊤` from
  `rlctAtOn ≤ t` would be the forbidden value-correct-germ-degenerate fill — the trap; NOT done.)
- The flat→chart transcription `monomialIntegrand_lintegral_box_eq_top` (the sharp monomial
  divergence in CHART coords) needs a geometric realization `φ : box → flat` with a
  change-of-variables and a pullback UPPER bound `|routeMCore M ∘ φ| ≤ C · (achiever monomial)`
  (smaller loss ⟹ larger `|·|^{−c'}` ⟹ divergence). The `(2,2,2)` case had such a chart
  (`phiUnit`), but it is a depth-2 miracle that does NOT generalise (the Jacobian tower loses
  triangularity after the first pivot), and the layer atlas (`routeLayerAtlas`) is purely
  COMBINATORIAL exponent data — it carries no geometric chart map.

So the open content is the **general-`M` achiever geometric chart / wedge** (an `F ≤ C·monomial`
bound on a positive-measure box around an achiever curve, with Jacobian control) — the
squeeze-to-box-integral bridge the `RouteMLayerCover` header names. The atom is stated at full
fidelity so the residual is pinned to that obligation; the WIRING into
`routeMLayerCover_of_atoms` is sorry-free.
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

**HONEST RESIDUAL — NOT proven.** This carries the file's single `sorry`, with a CORRECT statement
(validated against the cert + a decorrelated Codex consult, 2026-06-24); see the file header for the
precise sub-blocker. Summary: the banked squeeze delivers only the POINT-RLCT upper bound
`rlctAtOn ≤ ½·minAdm M`, strictly weaker than this BOUNDARY box-divergence; closing the gap needs a
general-`M` achiever geometric chart / wedge (`|routeMCore M ∘ φ| ≤ C · achiever-monomial` on a
positive-measure box, with Jacobian control) that does not exist on the combinatorial layer atlas,
and the `(2,2,2)` chart `phiUnit` does not generalise. -/
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
