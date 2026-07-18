import DLNFibre.DLN.RLCT.Validate.RouteMSJFreedPeel
import DLNFibre.DLN.RLCT.Validate.RouteMSJDecoratedRec

/-!
# `DLNFibre.DLN.RLCT.Validate.RouteMSJDecoratedPeelStep` — the checkpoint box theorem (LATE-158)

**Thread `genm-checkpoint`.** The box theorem `(□) = ∀M, RouteMBoxThresholdFinite M` proved
CONDITIONALLY on TWO neutral corank-descent walls — NO Aoyagi cite anywhere. The two walls are the two
arms of `innerCorankDescent_lt_top` (the inner deeper-strata corank-Gram descent, at the freed-`Γ`
triple integral the `(S,J)` outer descent operates on):

- **WALL 1 — `DeepCorankFinite`** (`min-corank ≥ 2`): the product-corank box-finiteness.
- **WALL 2 — `D1DispatchFinite`** (`min-corank ≤ 1`): the outer `(S,J)` descent arm.

Both are plain mathematical `Prop` hypotheses — VISIBLE in the type, never a global axiom or a cite. The
checkpoint theorem `routeMBoxThresholdFinite_of_walls (hDeep) (hD1)` is `sorry`-FREE: forced
`#print axioms` is exactly `[propext, Classical.choice, Quot.sound]`.

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
4. **Corank dispatch** — `innerCorankDescent_lt_top` splits `by_cases 2 ≤ min(M₀−t, M₁−t)`: the `d ≥ 2`
   arm is `DeepCorankFinite`, the `d ≤ 1` arm is `D1DispatchFinite`.

## The two walls' eventual native fill (banked STANDALONE, off this theorem's path)

`D1DispatchFinite`'s native fill is the outer `(S,J)` descent: reduce the freed-`Γ` socket to the
front-collapse wing cells (a=0/b=0, densities bounded/LOG/POWER — `frontCollapseRankSector_lt_top` with
the `PowerCellFinite` wall, `RouteMSJFrontCollapseDispatch`) and the corank-one edge cells (α-LOW native
/ α-HIGH the `EdgeJointFinite` wall — `frontCollapse_edge_b1_altu_bounded`, `RouteMSJEdgeAltuBounded`).
The reduction WIRING those atoms to this socket is not yet built, so the whole `d ≤ 1` arm is carried as
the single neutral hypothesis `D1DispatchFinite` here. S2-FREE: banked measure-preserving CoV
compositions; no `monomial_rlct`.
-/

namespace DLNFibre.DLN.RLCT

open MeasureTheory
open scoped ENNReal BigOperators

variable {L : ℕ}

/-- **NEUTRAL WALL 1 — `DeepCorankFinite`: the min-corank ≥ 2 product-corank box-finiteness.** A plain
mathematical hypothesis (NOT attributed, NOT a cite): the freed-`Γ` triple integral (the shear-freed
`gammaPeelIntegral`) is finite below `½·minAdm` whenever the corank `min(M₀−t, M₁−t) ≥ 2`. Carried as a
`Prop` HYPOTHESIS — VISIBLE in the type of any result that consumes it, never a global axiom. Discharges
the `d ≥ 2` arm of `innerCorankDescent_lt_top`. IH-conditional (assumes ONLY the product-corank step;
deeper reduced chains stay native via `hIH`). `ρ` dropped — the freed-`Γ` integrand uses only `κ`. -/
def DeepCorankFinite : Prop :=
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

/-- **NEUTRAL WALL 2 — `D1DispatchFinite`: the min-corank ≤ 1 corank-descent box-finiteness.** A plain
mathematical hypothesis (NOT attributed): the freed-`Γ` triple integral is finite below `½·minAdm`
whenever the corank `min(M₀−t, M₁−t) ≤ 1`. Carried as a `Prop` HYPOTHESIS — VISIBLE in the type,
never a global axiom. Discharges the `d ≤ 1` arm of `innerCorankDescent_lt_top`. This is the "outer
`(S,J)` descent" arm: its eventual native fill reduces the freed-`Γ` socket to the front-collapse wing
cells (a=0/b=0, densities bounded/LOG/POWER) and the corank-one edge cells (α-LOW / α-HIGH). Those
fine-grained atoms — `frontCollapseRankSector_lt_top`, `frontCollapse_edge_b1_altu_bounded`, the walls
`PowerCellFinite`/`EdgeJointFinite` — are banked standalone; the reduction wiring them to this socket is
not yet built, so the whole `d ≤ 1` arm is carried here as one neutral hypothesis. `ρ` dropped. -/
def D1DispatchFinite : Prop :=
  ∀ {L : ℕ} (M : Fin (L + 1 + 1 + 1) → ℕ) (t : ℕ)
    (_ht : 1 ≤ t) (_ht2 : t ≤ min (M 0) (M 1))
    (_hcork : min (M 0 - t) (M 1 - t) ≤ 1)
    (κ : Fin t ↪ Fin (M 1)) (c' : NNReal)
    (_hc' : (c' : ℝ) < (minAdm M : ℝ) / 2)
    (_hIH : ∀ M' : Fin (L + 1 + 1) → ℕ, RouteMBoxThresholdFinite M'),
    (∫⁻ A' in paramsBoxM (tailChain M) 1,
        ∫⁻ x in outerDom t (M 0 - t) (M 1 - t) 1,
          ∫⁻ Γ in {Γ : Fin (M 0 - t) → Fin (M 1 - t) → ℝ |
              Γ + schurShift x ∈ genBox (Fin (M 0 - t)) (Fin (M 1 - t)) 1},
            ENNReal.ofReal ((freedSchurLoss x Γ
              ((prod (tailChain M) A').submatrix (blockSplitEquiv κ) id)) ^ (-(c' : ℝ)))) < ⊤

/-- **The inner deeper-strata corank-Gram descent — the two-arm corank dispatch.** For a legal pivot
cut `(t, ρ, κ)` (`1 ≤ t ≤ min(M₀,M₁)`) below the geometric threshold (`c' < ½·minAdm M`), GIVEN the
one-shorter strong IH `hIH` and the two neutral walls, the freed-`Γ` triple integral (the shear-freed
form of `gammaPeelIntegral M t ρ κ c'`, from `gammaPeelIntegral_schurShearFree_eq`) is finite.

`sorry`-FREE by `by_cases 2 ≤ min(M₀−t, M₁−t)`: the `d ≥ 2` arm is `DeepCorankFinite`, the `d ≤ 1` arm
is `D1DispatchFinite`. Both walls are hypotheses (VISIBLE in the type), so this carries NO `sorryAx` and
NO cite; `#print axioms` is `[propext, Classical.choice, Quot.sound]`. The `(S,J)` outer descent that
will eventually DISCHARGE `D1DispatchFinite` — integrate the outer tail `A'`, supply the interface
hypotheses of the banked inner-`Γ` finiteness (`freedSchurLoss_inner_peel_lt_top` / `_bounded_lt_top`,
`RouteMSJFreedPeel`) as a MEASURE statement, descend to the monomial terminal
(`sjLoss_terminal_lintegral_lt_top`) and the reduced-chain IH `hIH (redChain t M)` at the threshold
shifted by `½·peelCharge` — reduces to the front-collapse wing + edge cells; that reduction is not yet
built, so the whole `d ≤ 1` arm is the wall `D1DispatchFinite` for now. -/
theorem innerCorankDescent_lt_top (M : Fin (L + 1 + 1 + 1) → ℕ) (t : ℕ)
    (ht : 1 ≤ t) (ht2 : t ≤ min (M 0) (M 1))
    (ρ : Fin t ↪ Fin (M 0)) (κ : Fin t ↪ Fin (M 1)) (c' : NNReal)
    (hc' : (c' : ℝ) < (minAdm M : ℝ) / 2)
    (hIH : ∀ M' : Fin (L + 1 + 1) → ℕ, RouteMBoxThresholdFinite M')
    (hDeep : DeepCorankFinite) (hD1 : D1DispatchFinite) :
    (∫⁻ A' in paramsBoxM (tailChain M) 1,
        ∫⁻ x in outerDom t (M 0 - t) (M 1 - t) 1,
          ∫⁻ Γ in {Γ : Fin (M 0 - t) → Fin (M 1 - t) → ℝ |
              Γ + schurShift x ∈ genBox (Fin (M 0 - t)) (Fin (M 1 - t)) 1},
            ENNReal.ofReal ((freedSchurLoss x Γ
              ((prod (tailChain M) A').submatrix (blockSplitEquiv κ) id)) ^ (-(c' : ℝ)))) < ⊤ := by
  by_cases hcork : 2 ≤ min (M 0 - t) (M 1 - t)
  · -- min-corank ≥ 2: NEUTRAL WALL 1 (product-corank box-finiteness), consumed as a hypothesis
    exact hDeep M t ht ht2 hcork κ c' hc' hIH
  · -- min-corank ≤ 1 (¬hcork ⟹ min ≤ 1): NEUTRAL WALL 2 (the outer (S,J) descent d≤1 arm), consumed
    -- as a hypothesis. Its eventual native fill dispatches to the front-collapse wing cells + the
    -- corank-one edge cells (banked standalone as `frontCollapseRankSector_lt_top`,
    -- `frontCollapse_edge_b1_altu_bounded`, `PowerCellFinite`, `EdgeJointFinite`); the reduction that
    -- wires those to this freed-`Γ` socket is not yet built, so the whole arm is `hD1` for now.
    exact hD1 M t ht ht2 (by omega) κ c' hc' hIH

/-- **The per-chart peeled integral is finite (the wired reduction to the corank descent).** For a legal
pivot cut below threshold, GIVEN the one-shorter strong IH and the two walls, `gammaPeelIntegral M t ρ κ
c' < ⊤`. The banked Schur-weld + Γ-freeing shear (`gammaPeelIntegral_schurShearFree_eq`, §1.3-2/3)
rewrites it into the freed-`Γ` triple integral, closed by `innerCorankDescent_lt_top` (the two-arm corank
dispatch on `DeepCorankFinite` / `D1DispatchFinite`). This is exactly the goal of `sjJointResolution`
(`RouteMSJResolution:803`) — re-expressed with the front-cover and the weld/shear wired. -/
theorem gammaPeelIntegral_lt_top_of_descent (M : Fin (L + 1 + 1 + 1) → ℕ) (t : ℕ)
    (ht : 1 ≤ t) (ht2 : t ≤ min (M 0) (M 1))
    (ρ : Fin t ↪ Fin (M 0)) (κ : Fin t ↪ Fin (M 1)) (c' : NNReal)
    (hc' : (c' : ℝ) < (minAdm M : ℝ) / 2)
    (hIH : ∀ M' : Fin (L + 1 + 1) → ℕ, RouteMBoxThresholdFinite M')
    (hDeep : DeepCorankFinite) (hD1 : D1DispatchFinite) :
    gammaPeelIntegral M t ρ κ (c' : ℝ) < ⊤ := by
  rw [gammaPeelIntegral_schurShearFree_eq M t ρ κ (c' : ℝ)]
  exact innerCorankDescent_lt_top M t ht ht2 ρ κ c' hc' hIH hDeep hD1

/-- **The decorated single-peel step (`decoratedPeelStep_proof`), conditional on the two walls.** For
every `≥ 3`-width chain `M`, GIVEN box-finiteness of every one-shorter chain and the two neutral walls,
the trivial decoration on `M` is finite below `carrierThreshold M = ½·minAdm M`. Wires the
route-independent skeleton: π=∅ recovery (`decoratedBoxThresholdFinite_trivial_iff`) → front cover
(`sjBoundaryPeel`) → per-term (`ENNReal.sum_lt_top`) → Schur-weld/shear + the freed-`Γ` corank descent
(`gammaPeelIntegral_lt_top_of_descent`, the two-arm dispatch on `DeepCorankFinite` / `D1DispatchFinite`).

`sorry`-FREE: this delivers `DecoratedPeelStep`, closing `(□)` via the banked driver
`routeMBoxThresholdFinite_of_decoratedPeel`. -/
theorem decoratedPeelStep_proof (hDeep : DeepCorankFinite) (hD1 : D1DispatchFinite) :
    DecoratedPeelStep := by
  intro L M hIH
  refine (decoratedBoxThresholdFinite_trivial_iff M).mpr ?_
  intro c' hc'
  refine lt_of_le_of_lt (sjBoundaryPeel M c' hc') ?_
  refine ENNReal.sum_lt_top.mpr (fun t ht => ENNReal.sum_lt_top.mpr
    (fun ρ _ => ENNReal.sum_lt_top.mpr (fun κ _ => ?_)))
  rw [Finset.mem_Icc] at ht
  exact gammaPeelIntegral_lt_top_of_descent M t ht.1 ht.2 ρ κ c' hc' hIH hDeep hD1

/-- **THE CHECKPOINT THEOREM — the plain-route `(□)`, conditional on the two neutral corank-descent
walls, NO cite.** Composes the banked driver `routeMBoxThresholdFinite_of_decoratedPeel` with
`decoratedPeelStep_proof`: GIVEN the two plain mathematical hypotheses
- `DeepCorankFinite` (the `min-corank ≥ 2` product-corank box-finiteness), and
- `D1DispatchFinite` (the `min-corank ≤ 1` corank-descent box-finiteness, the outer `(S,J)` descent arm),

every width vector `M` is box-threshold-finite. Both walls are HYPOTHESES — VISIBLE in the type, NEITHER
a global axiom nor an Aoyagi cite — and they are the ONLY two arms of `innerCorankDescent_lt_top`, so this
composition is `sorry`-FREE: its forced `#print axioms` is exactly `[propext, Classical.choice,
Quot.sound]`. This is the honest clean-three conditional checkpoint: the box theorem is native ABOVE the
two corank-descent finiteness arms. (The fine-grained atoms that will eventually DISCHARGE these walls —
`frontCollapseRankSector_lt_top` with `PowerCellFinite`, `frontCollapse_edge_b1_altu_bounded` with
`EdgeJointFinite`, and the b=0/LOG native cells — are banked STANDALONE, off this theorem's path.) -/
theorem routeMBoxThresholdFinite_of_walls (hDeep : DeepCorankFinite) (hD1 : D1DispatchFinite) :
    ∀ {L : ℕ} (M : Fin (L + 1) → ℕ), RouteMBoxThresholdFinite M :=
  routeMBoxThresholdFinite_of_decoratedPeel (decoratedPeelStep_proof hDeep hD1)

end DLNFibre.DLN.RLCT
