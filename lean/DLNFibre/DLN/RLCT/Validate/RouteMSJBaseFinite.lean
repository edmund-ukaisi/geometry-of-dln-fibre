import DLNFibre.DLN.RLCT.Validate.RouteMSJResolution
import DLNFibre.DLN.RLCT.Validate.RouteMSJDecorated

/-!
# `DLNFibre.DLN.RLCT.Validate.RouteMSJBaseFinite` — the `d = 0` base analytic core (route-independent)

**Thread `genm-sj5-desc3`, Piece #3 (partial): the SHARED `d = 0` base brick.** Both base routes (A =
Rayleigh/`corankLeaf`, B = terminal/`sjLoss_terminal`) split the `DecoratedBaseHyp` leaf into `d = 0`
(no exceptional divisors) and `d ≥ 1`. The `d = 0` part is route-INDEPENDENT: the decorated loss is the
free-block product loss `frobSq (prod M (e z))` (the `trivial`-like carrier at width 2), and the integral
reduces — via the change-of-variables `e` and the banked width-2 free-matrix Morse `sjBase1_freeMatrix` —
to `routeMLayerBoxIntegral M c' 1 < ⊤` below the carrier threshold `½·minAdm M`.

* **`baseBoxCoV_lt_top`** — the analytic core, stated on the pulled-back box integral: for a
  MEASURE-PRESERVING equiv `e : Z ≃ᵐ Params M` (width 2), the deeper integral of
  `frobSq (prod M (e z))^{−c'}` over `e ⁻¹' (paramsBoxM M 1)` is finite below `carrierThreshold M`.
  The measure-preserving change of variables (`MeasurePreserving.setLIntegral_comp_preimage_emb`) sends it
  to `routeMLayerBoxIntegral M c' 1`, closed by the banked width-2 base `sjBase1_freeMatrix`.

**★ Interface note (surfaced to the controller/cover).** This consumes `MeasurePreserving e`, NOT merely a
`MeasurableEquiv e`: the CoV to the box integral REQUIRES `e` to push `Z`'s volume to `Params M`'s volume.
The locked `genuineCarrier` (form (i)) currently carries only `e : D.Z ≃ᵐ Params M` (measurable) — for the
base to consume this brick, `genuineCarrier` must additionally assert `MeasurePreserving e` (an honest
parametrization is a measure-preserving CoV). The `D.integral (d = 0) → this` reduction + the carrier-form
`decLoss = frobSq (prod M (e z))` connection await cover's finalized `genuineCarrier` (the A/B route +
carrier clause), so are NOT built here.

Axiom-clean `[propext, Classical.choice, Quot.sound]` (does not touch `RouteMSJResolution`'s `:797` sorry
— `sjBase1_freeMatrix` is itself sorry-free).
-/

namespace DLNFibre.DLN.RLCT

open MeasureTheory
open scoped ENNReal BigOperators

/-- **The `d = 0` base analytic core (route-independent).** For a width-2 chain `M` and a
MEASURE-PRESERVING equiv `e : Z ≃ᵐ Params M`, the deeper integral of the free-block product loss
`frobSq (prod M (e z))^{−c'}` over the pulled-back box `e ⁻¹' (paramsBoxM M 1)` is finite below the
carrier threshold `½·minAdm M`. Proof: the measure-preserving change of variables identifies it with
`routeMLayerBoxIntegral M c' 1 = ∫_{paramsBoxM M 1} frobSq (prod M A)^{−c'}`, finite by the banked
width-2 free-matrix Morse `sjBase1_freeMatrix`. This is the shared `d = 0` leaf both base routes consume. -/
theorem baseBoxCoV_lt_top {M : Fin (1 + 1) → ℕ} {Z : Type} [MeasureSpace Z]
    (e : Z ≃ᵐ Params M) (hmp : MeasurePreserving e) (c' : NNReal)
    (hc' : (c' : ℝ) < carrierThreshold M) :
    ∫⁻ z in e ⁻¹' (paramsBoxM M 1),
      ENNReal.ofReal ((frobSq (prod M (e z))) ^ (-(c' : ℝ))) < ⊤ := by
  rw [hmp.setLIntegral_comp_preimage_emb e.measurableEmbedding
    (fun A => ENNReal.ofReal ((frobSq (prod M A)) ^ (-(c' : ℝ)))) (paramsBoxM M 1)]
  have hfin := sjBase1_freeMatrix M c' (by rw [carrierThreshold] at hc'; exact hc')
  rwa [routeMLayerBoxIntegral] at hfin

end DLNFibre.DLN.RLCT
