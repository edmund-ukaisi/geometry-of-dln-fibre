import DLNFibre.DLN.RLCT.Validate.RouteMSJResolution

/-!
# `DLNFibre.DLN.RLCT.Validate.RouteMSJJointReduce` — the joint-resolution monotonicity reduction

**Thread `genm-sjbuild3`, R1-UPPER.** The clean structural fact that reduces the per-chart joint
resolution `sjJointResolution` (`RouteMSJResolution`, the single named analytic sorry) to the
STANDALONE box-finiteness `RouteMBoxThresholdFinite M` of the SAME chain.

## What lands here

* **`gammaPeelIntegral_le_boxIntegral`** — the EXACT monotonicity bound: the per-`(t,ρ,κ)`-chart peeled
  integral is `≤` the full layer-product box integral,
  `gammaPeelIntegral M t ρ κ c' ≤ routeMLayerBoxIntegral M c' 1`. Immediate from the banked front-split
  `routeMLayerBoxIntegral_front_split` (both are the tail-outer iterated front-factor integral) and the
  domain inclusion `matBox ∩ pivotChart ρ κ ⊆ matBox` (`lintegral_mono_set`). No hypotheses, no analytic
  content — a pure subset-integral bound. Sorry-free.

* **`sjJointResolution_of_boxThresholdFinite`** — the conditional close: GIVEN standalone box-finiteness
  `RouteMBoxThresholdFinite M` of the SAME chain, every per-chart peeled integral is finite below the
  threshold. Two lines (the monotonicity bound + the finiteness of the dominating box integral). This is
  the honest route by which `sjJointResolution` closes once `RouteMBoxThresholdFinite M` is supplied by
  the decorated-recursion route (`RouteMSJDecorated`, `decoratedBoxThresholdFinite_trivial_iff`).

## What this reduction says about the peel spine (fidelity, reported precisely)

The peel spine `sjBoundaryPeel` bounds `routeMLayerBoxIntegral M ≤ ∑ gammaPeelIntegral`; combined with the
monotonicity here (`gammaPeelIntegral ≤ routeMLayerBoxIntegral M`), the two only give the trivial
`routeMLayerBoxIntegral M ≤ (#charts) · routeMLayerBoxIntegral M`. So the monotonicity bound does NOT
reduce `gammaPeelIntegral` to a SHORTER chain — the spine cannot prove `RouteMBoxThresholdFinite M` from
the IH through this bound. Reducing `gammaPeelIntegral` to strictly-shorter chains is the genuine analytic
content (`gammaPeelIntegral_schurShearFree_eq` + the outer `(S,J)` descent, `RouteMSJFreedPeel` header) —
the unbuilt resolution-of-singularities chart-tree. This module supplies only the OTHER direction: given
box-finiteness of the same chain (from the decorated route), the chart integrals are finite. It is the
bridge by which the decorated recursion, once it lands `RouteMBoxThresholdFinite M`, discharges
`sjJointResolution` — NOT itself a proof of box-finiteness.

S2-FREE: pure measure monotonicity over the banked front-split. Axiom-clean
`[propext, Classical.choice, Quot.sound]`.
-/

namespace DLNFibre.DLN.RLCT

open MeasureTheory Set
open scoped ENNReal BigOperators

variable {L : ℕ}

/-- **The per-chart peeled integral is dominated by the full box integral (EQUALITY-free bound).** For
any pivot cut `(t, ρ, κ)` and exponent `c'`,
`gammaPeelIntegral M t ρ κ c' ≤ routeMLayerBoxIntegral M c' 1`. Both are the tail-outer iterated
front-factor integral (`routeMLayerBoxIntegral_front_split`); the chart integral restricts the inner
leading-layer domain to `matBox ∩ pivotChart ρ κ ⊆ matBox`, so `lintegral_mono_set` (per outer `A'`) +
`lintegral_mono` (outer) give the bound. Pure measure theory. -/
theorem gammaPeelIntegral_le_boxIntegral (M : Fin (L + 1 + 1 + 1) → ℕ) (t : ℕ)
    (ρ : Fin t ↪ Fin (M 0)) (κ : Fin t ↪ Fin (M 1)) (c' : ℝ) :
    gammaPeelIntegral M t ρ κ c' ≤ routeMLayerBoxIntegral M c' 1 := by
  rw [gammaPeelIntegral, routeMLayerBoxIntegral_front_split M c']
  exact lintegral_mono (fun _A' => lintegral_mono_set Set.inter_subset_left)

/-- **The conditional close of `sjJointResolution` from standalone box-finiteness.** GIVEN
box-finiteness of the SAME chain `RouteMBoxThresholdFinite M`, the per-`(t,ρ,κ)`-chart peeled integral
is finite for every pivot cut and every `c' < ½·minAdm M`. Immediate from
`gammaPeelIntegral_le_boxIntegral` (the monotonicity bound) and `hM` (finiteness of the dominating
box integral). This is how the decorated recursion, once it supplies `RouteMBoxThresholdFinite M`
(via `decoratedBoxThresholdFinite_trivial_iff`), discharges `sjJointResolution` — NO use of the
per-chart `hIH`, only the box-finiteness of the chain itself. -/
theorem sjJointResolution_of_boxThresholdFinite (M : Fin (L + 1 + 1 + 1) → ℕ)
    (hM : RouteMBoxThresholdFinite M)
    (t : ℕ) (ρ : Fin t ↪ Fin (M 0)) (κ : Fin t ↪ Fin (M 1))
    (c' : NNReal) (hc' : (c' : ℝ) < (minAdm M : ℝ) / 2) :
    gammaPeelIntegral M t ρ κ (c' : ℝ) < ⊤ :=
  lt_of_le_of_lt (gammaPeelIntegral_le_boxIntegral M t ρ κ (c' : ℝ)) (hM c' hc')

end DLNFibre.DLN.RLCT
