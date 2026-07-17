import DLNFibre.DLN.RLCT.Validate.RouteMSJFreedPeel
import DLNFibre.DLN.RLCT.Validate.RouteMSJDecoratedRec

/-!
# `DLNFibre.DLN.RLCT.Validate.RouteMSJDecoratedPeelStep` — the `DecoratedPeelStep` skeleton

**Thread `genm-sj5-schur`, B5-desc PHASE 1 (statements-first skeleton).** The §5 lane's sole
remaining build is `decoratedPeelStep_proof : DecoratedPeelStep` (the open `Prop` at
`RouteMSJDecoratedRec:78`); once sorry-free it closes `(□) = ∀M, RouteMBoxThresholdFinite M` via
the banked driver `routeMBoxThresholdFinite_of_decoratedPeel` and retro-fills `sjJointResolution`.

This module wires the **route-independent** outer skeleton per `peel-buildplan.md` §1.3, isolating
the single remaining analytic content into ONE named `sorry`-hole `innerCorankDescent_lt_top` — the
inner deeper-strata corank-Gram descent, at the level (the freed-`Γ` triple integral) the `(S,J)`
outer descent actually operates on.

## The wiring (what COMPOSES here, sorry-free)

`decoratedPeelStep_proof` reduces `DecoratedBoxThresholdFinite (trivial M)` to per-chart finiteness,
consuming the banked pieces:

1. **π=∅ recovery** — `decoratedBoxThresholdFinite_trivial_iff` reduces the decorated goal to the
   plain `RouteMBoxThresholdFinite M` (thresholds + integrals coincide at the trivial decoration).
2. **Front cover (§1.3-1)** — `sjBoundaryPeel` bounds `routeMLayerBoxIntegral M c' 1` by the finite
   sum over pivot cuts `t ∈ [1, min(M₀,M₁)]` and charts `(ρ,κ)` of `gammaPeelIntegral M t ρ κ c'`
   (`ENNReal.sum_lt_top` reduces the sum to per-term finiteness).
3. **Schur weld + Γ-freeing shear (§1.3-2)** — `gammaPeelIntegral_schurShearFree_eq` (itself the
   banked composition of `chartInner_schurWeld_eq_of_emb` + `chartInner_schurShearFree_eq`) rewrites
   each per-chart `gammaPeelIntegral` into the freed-`Γ` triple integral, `Γ` INDEPENDENT.

## The isolated hole (§1.3-3, `innerCorankDescent_lt_top`)

The finiteness of the freed-`Γ` triple integral at the shifted threshold — the inner deeper-strata
corank-Gram descent. Stated route-independently: it takes the FULL one-shorter strong IH `hIH` (its
eventual fill consumes the PLAIN `RouteMBoxThresholdFinite (redChain t M)`, §1.3-4 — the decoration
is discharged INSIDE this hole, never carried into the IH, which is why the skeleton is route-safe).

## What is NOT wired here (surfaced finding, not a gap in the skeleton)

Steps §1.3-4 (charge shift `carrierThreshold_shift` + the reduced-chain IH) and §1.3-5 (charges-ADD
via the shared terminal `sjLoss_terminal_lintegral_lt_top`) CANNOT be wired OUTSIDE the hole with
the current banked pieces: reducing the freed triple integral to `[redChain box] × [terminal]` IS
the route-dependent outer `(S,J)` descent — i.e. the hole itself. They are the hole's eventual fill
(Phase 2, gated on the genm-sj5-cover de-risk: dominant-minor cover vs pure radial). The banked
CONDITIONAL inner-`Γ` finiteness (`freedSchurLoss_inner_peel_lt_top` / `_bounded_lt_top`,
`RouteMSJFreedPeel`) needs the three interface hypotheses (pivot energy `> 0`, `Q_bQ_bᵀ` PosDef,
`c' > a·b/2`) that FAIL pointwise and must be supplied as a measure statement by that descent.

This module is UNTRACKED and NOT wired into `DLNFibre.lean`/`AxCheck` — the canonical library stays
0-sorry; the ONE `sorry` is the isolated hole. `#print axioms` on the eventual fill is deferred to
Phase 2. S2-FREE: banked measure-preserving CoV compositions; no `monomial_rlct`.
-/

namespace DLNFibre.DLN.RLCT

open MeasureTheory
open scoped ENNReal BigOperators

variable {L : ℕ}

/-- **CITED (Aoyagi §5, box-level) — product-corank / joint-Vandermonde box-finiteness at
`min-corank ≥ 2`** (carried as a `Prop` HYPOTHESIS — the one box-level cite of the plain-route `(□)`).
The freed-`Γ` triple integral (the shear-freed `gammaPeelIntegral`) is finite below `½·minAdm` whenever
the corank `min(M₀−t, M₁−t) ≥ 2`. This is the BOX-LEVEL shadow of `cited_aoyagi_dln` (`rlct = ½·codim`):
morally implied by it, but NOT a Lean corollary — the reduction spans the local→global rlct +
`lossDLN ↔ freedSchurLoss` bridge, which is exactly the research programme native (box) is built to avoid.
Hence carried as its own distinct box-level Aoyagi interface — a second minimal gap alongside the
payoff-level `cited_aoyagi_dln`. IH-conditional (cites ONLY the product-corank step; deeper reduced chains
stay native via `hIH`). `ρ` dropped — the freed-`Γ` integrand uses only `κ` (precision.md 1.1.3). -/
def cited_aoyagi_product_corank : Prop :=
  ∀ {L : ℕ} (M : Fin (L + 1 + 1 + 1) → ℕ) (t : ℕ)
    (_ht : 1 ≤ t) (_ht2 : t ≤ min (M 0) (M 1))
    (_hcork : 2 ≤ min (M 0 - t) (M 1 - t))
    (κ : Fin t ↪ Fin (M 1)) (c' : NNReal)
    (_hc' : (c' : ℝ) < (minAdm M : ℝ) / 2)
    (_hIH : ∀ M' : Fin (L + 1 + 1) → ℕ, RouteMBoxThresholdFinite M'),
    (∫⁻ A' in paramsBoxM (tailChain M) 1,
        ∫⁻ x in outerDom t (M 0 - t) (M 1 - t) 1,
          ∫⁻ Γ in {Γ : Fin (M 0 - t) → Fin (M 1 - t) → ℝ |
              Γ + schurShift x ∈ genBox (Fin (M 0 - t)) (Fin (M 1 - t)) 1},
            ENNReal.ofReal ((freedSchurLoss x Γ
              ((prod (tailChain M) A').submatrix (blockSplitEquiv κ) id)) ^ (-(c' : ℝ)))) < ⊤

/-- **THE HOLE (§1.3-3) — the inner deeper-strata corank-Gram descent.** For a legal pivot cut
`(t, ρ, κ)` (`1 ≤ t ≤ min(M₀,M₁)`) below the geometric threshold (`c' < ½·minAdm M`), GIVEN the
one-shorter strong IH `hIH`, the freed-`Γ` triple integral (the shear-freed form of
`gammaPeelIntegral M t ρ κ c'`, from `gammaPeelIntegral_schurShearFree_eq`) is finite.

This is the SOLE remaining analytic content of the §5 lane. Its Phase-2 fill (gated on the
genm-sj5-cover de-risk — dominant-minor cover vs pure radial) is the `(S,J)` outer descent:
integrate the outer tail `A'`, supply the interface hypotheses of the banked inner-`Γ` finiteness
(`freedSchurLoss_inner_peel_lt_top` / `_bounded_lt_top`, `RouteMSJFreedPeel`) as a MEASURE statement
(they fail pointwise), descend through the `SJLinGenState` carrier to the monomial terminal
(`sjLoss_terminal_lintegral_lt_top`, §1.3-5), and close on the PLAIN reduced-chain IH
`hIH (redChain t M)` at the threshold shifted by `½·peelCharge`
(`half_minAdm_sub_half_peelCharge_le`, §1.3-4). The decoration is discharged HERE, never carried
into the IH — the route-safety of the skeleton. NOT filled in Phase 1. -/
theorem innerCorankDescent_lt_top (M : Fin (L + 1 + 1 + 1) → ℕ) (t : ℕ)
    (ht : 1 ≤ t) (ht2 : t ≤ min (M 0) (M 1))
    (ρ : Fin t ↪ Fin (M 0)) (κ : Fin t ↪ Fin (M 1)) (c' : NNReal)
    (hc' : (c' : ℝ) < (minAdm M : ℝ) / 2)
    (hIH : ∀ M' : Fin (L + 1 + 1) → ℕ, RouteMBoxThresholdFinite M')
    (hcited : cited_aoyagi_product_corank) :
    (∫⁻ A' in paramsBoxM (tailChain M) 1,
        ∫⁻ x in outerDom t (M 0 - t) (M 1 - t) 1,
          ∫⁻ Γ in {Γ : Fin (M 0 - t) → Fin (M 1 - t) → ℝ |
              Γ + schurShift x ∈ genBox (Fin (M 0 - t)) (Fin (M 1 - t)) 1},
            ENNReal.ofReal ((freedSchurLoss x Γ
              ((prod (tailChain M) A').submatrix (blockSplitEquiv κ) id)) ^ (-(c' : ℝ)))) < ⊤ := by
  by_cases hcork : 2 ≤ min (M 0 - t) (M 1 - t)
  · -- min-corank ≥ 2: CITED (Aoyagi §5 product-corank / joint-Vandermonde box-finiteness)
    exact hcited M t ht ht2 hcork κ c' hc' hIH
  · -- min-corank ≤ 1 (¬hcork ⟹ min ≤ 1): NATIVE — satred's d≤1 dispatch. NOT bounded plumbing:
    -- needs THREE native sub-builds, none landed as theorems yet (Lane-1 recon, 2026-07-17) —
    -- 2a generic dominant-minor finite cover + per-chart matrix-space CoV bounded-density → hIH;
    -- 2b corank-one edge cell (fragile split + C-transversality descent + a<u/a≥u dispatch over
    -- gammaAtom/qbox + reduced-chain charge accounting); 2c wings (a=0 wide-product X·Y pushforward
    -- density `deeperFlag_waist_a0`, b=0 tall Wishart qbox `deeperFlag_waist_b0`). The banked ATOMS
    -- exist; the outer (S,J) descent that supplies their a.e. interface hypotheses over the measure
    -- and reduces to hIH at charge `peelCharge` does not. See the Lane-1 wall report.
    sorry

/-- **The per-chart peeled integral is finite (the wired reduction to the hole).** For a legal pivot
cut below threshold, GIVEN the one-shorter strong IH, `gammaPeelIntegral M t ρ κ c' < ⊤`. The banked
Schur-weld + Γ-freeing shear (`gammaPeelIntegral_schurShearFree_eq`, §1.3-2/3) rewrites it into the
freed-`Γ` triple integral, closed by the hole `innerCorankDescent_lt_top`. This is exactly the goal
of `sjJointResolution` (`RouteMSJResolution:803`) — re-expressed with the front-cover and the
weld/shear wired, and the analytic content isolated to the freed-`Γ` descent. -/
theorem gammaPeelIntegral_lt_top_of_descent (M : Fin (L + 1 + 1 + 1) → ℕ) (t : ℕ)
    (ht : 1 ≤ t) (ht2 : t ≤ min (M 0) (M 1))
    (ρ : Fin t ↪ Fin (M 0)) (κ : Fin t ↪ Fin (M 1)) (c' : NNReal)
    (hc' : (c' : ℝ) < (minAdm M : ℝ) / 2)
    (hIH : ∀ M' : Fin (L + 1 + 1) → ℕ, RouteMBoxThresholdFinite M')
    (hcited : cited_aoyagi_product_corank) :
    gammaPeelIntegral M t ρ κ (c' : ℝ) < ⊤ := by
  rw [gammaPeelIntegral_schurShearFree_eq M t ρ κ (c' : ℝ)]
  exact innerCorankDescent_lt_top M t ht ht2 ρ κ c' hc' hIH hcited

/-- **The decorated single-peel step (`decoratedPeelStep_proof`), MODULO the isolated hole.** For
every `≥ 3`-width chain `M`, GIVEN box-finiteness of every one-shorter chain, the trivial decoration
on `M` is finite below `carrierThreshold M = ½·minAdm M`. Wires the route-independent skeleton: π=∅
recovery (`decoratedBoxThresholdFinite_trivial_iff`) → front cover (`sjBoundaryPeel`) → per-term
(`ENNReal.sum_lt_top`) → Schur-weld/shear + the freed-`Γ` descent hole
(`gammaPeelIntegral_lt_top_of_descent`).

Once `innerCorankDescent_lt_top` is filled (Phase 2), this delivers `DecoratedPeelStep`, closing
`(□)` via the banked driver `routeMBoxThresholdFinite_of_decoratedPeel` and retro-filling
`sjJointResolution`. -/
theorem decoratedPeelStep_proof (hcited : cited_aoyagi_product_corank) : DecoratedPeelStep := by
  intro L M hIH
  refine (decoratedBoxThresholdFinite_trivial_iff M).mpr ?_
  intro c' hc'
  refine lt_of_le_of_lt (sjBoundaryPeel M c' hc') ?_
  refine ENNReal.sum_lt_top.mpr (fun t ht => ENNReal.sum_lt_top.mpr
    (fun ρ _ => ENNReal.sum_lt_top.mpr (fun κ _ => ?_)))
  rw [Finset.mem_Icc] at ht
  exact gammaPeelIntegral_lt_top_of_descent M t ht.1 ht.2 ρ κ c' hc' hIH hcited

/-- **The plain-route `(□)`, conditional on the box-level Aoyagi cite.** Composes the banked driver
`routeMBoxThresholdFinite_of_decoratedPeel` with `decoratedPeelStep_proof`: GIVEN the carried box-level
cite `cited_aoyagi_product_corank` (the `min-corank ≥ 2` product-corank box-finiteness — see its
docstring: the box-level shadow of `cited_aoyagi_dln`, a second minimal Aoyagi gap), every width vector
`M` is box-threshold-finite. The cite is a HYPOTHESIS — VISIBLE in the type, NOT a global axiom — so
`#print axioms` stays `[propext, Classical.choice, Quot.sound]`. The `d ≤ 1` native arm of
`innerCorankDescent_lt_top` remains the one tracked hole (satred's dispatch); until it lands, this carries
that `sorryAx`. -/
theorem routeMBoxThresholdFinite_of_prodCorank (hcited : cited_aoyagi_product_corank) :
    ∀ {L : ℕ} (M : Fin (L + 1) → ℕ), RouteMBoxThresholdFinite M :=
  routeMBoxThresholdFinite_of_decoratedPeel (decoratedPeelStep_proof hcited)

end DLNFibre.DLN.RLCT
