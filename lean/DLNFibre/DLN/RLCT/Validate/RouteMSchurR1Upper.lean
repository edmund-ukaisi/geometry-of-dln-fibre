import DLNFibre.DLN.RLCT.Validate.RouteMSchurFiring
import DLNFibre.DLN.RLCT.Validate.RouteMHfinPremise

/-!
# `DLNFibre.DLN.RLCT.Validate.RouteMSchurR1Upper` — the R1-UPPER wire

The terminal wire of the R1-UPPER (`hfin`, upper-bound) lane: feed the now-DONE per-corank firing
`RouteMSchurFiring.schurRecStep_four` into the threshold-witnessed wrapper
`RouteMSchurGeneral.schurGen_lt_top_modulo_recStep`, and assemble the gated R1-gate headline through
the general-`M` layer cover (`RouteMLayerCover.routeMLayerCover_of_atoms`) +
`RouteMLayerValue.resolution_charts_of_layerCover`.

## What this file delivers

* `schurGenFin` — **the carve realized.** The unconditional `∀r` Schur-core finiteness
  `SchurCore 4 r c' T` (below the genuine threshold `schurLambda r`), obtained by feeding the
  real per-corank firing `schurRecStep_four` into `schurGen_lt_top_modulo_recStep`. This DROPS
  the deferred stub `RouteMSchurGeneral.schurRecStep4_stub` (a `sorry`, out-of-chain — referenced
  by nothing): the `hstep` hypothesis is now discharged by the genuine firing, so the conclusion
  is hypothesis-free and axiom-clean.

* `r1Upper_resolution_charts_of_box` — **the gated R1-gate headline.** For an arbitrary width
  vector `M`, GIVEN (i) `hpos : 1 ≤ minAdm M`, (ii) the named box-finiteness
  `hbox : RouteMBoxThresholdFinite M`, and (iii) the box-divergence field `hdiv` (the R1-LOWER
  atom, threaded here as a hypothesis — its general-`M` discharge is separate, R1.6 geometry),
  the R1 gate is closed: `rlctAtOn (dlnLoss M 0) (deepest) = ⨅ leaf, monomialThreshold`. The
  `hfin` field is discharged by the gated `RouteMHfinPremise.layerCover_hfin_of_box M hpos hbox`
  (sorry-free); the cover assembles via `routeMLayerCover_of_atoms`; the value lane via
  `resolution_charts_of_layerCover`.

## The honest gating (caveats beside the claim)

`hbox : RouteMBoxThresholdFinite M` stays an explicit HYPOTHESIS. The bridge that discharges it
from the Schur-core finiteness `schurGenFin` — i.e. `routeMLayerBoxIntegral M c' 1 < ⊤` from
`SchurCore`-finiteness — is the per-family `(r,r,4)` discharge (`SchurCore` is hardcoded at column
count `4`; the threshold `½·minAdm M` matches only the binding family). That discharge is NOT in
this tree; it folds `schurRecStep_four` into `hbox` separately. So at THIS wire, `schurGenFin` is
the proven analytic ENGINE and `r1Upper_resolution_charts_of_box` is the honest gated headline
with `hbox` explicit — no overclaim.

`hdiv` is likewise a hypothesis: the only in-tree general-`M` `hdiv` discharge
(`RouteMLayerCoverGE.layerCover_hdiv`) rides the open R1-LOWER atom
`routeMCore_box_diverges_achiever` (a `sorry`); routing through it would import that `sorry` into
this headline's axiom footprint. This file deliberately does NOT call it — `hdiv` is threaded,
keeping the R1-UPPER wire axiom-clean.

## Axiom hygiene
Both results are built only from sorry-free upstream (`schurRecStep_four`,
`schurGen_lt_top_modulo_recStep`, `layerCover_hfin_of_box`, `routeMLayerCover_of_atoms`,
`resolution_charts_of_layerCover`) — NO `sorry`/`sorryAx`. Forced `#print axioms`:
* `schurGenFin` → `[propext, Classical.choice, Quot.sound]` (the clean three; a pure finiteness
  statement, no RLCT value).
* `r1Upper_resolution_charts_of_box` → `[propext, Classical.choice, Quot.sound, monomial_rlct]` —
  the clean three plus `monomial_rlct`, the single permitted S2 citation (Aoyagi/Hironaka, the
  monomial-RLCT threshold; `Skeleton.lean`). The citation enters via the **`hfin` LEG**
  (`layerCover_hfin_of_box`, forced `#print axioms` = clean-three + `monomial_rlct`): its premise
  reduction uses the achiever-leaf box-divergence (`monomialThreshold_singleton` +
  `monomialIntegrand_lintegral_box_eq_top`), which rides the cited monomial threshold. The value
  lane `resolution_charts_of_layerCover` is itself **clean-three** (forced-checked), as is the
  cover assembly `routeMLayerCover_of_atoms`. Same NET footprint as `routeM334_box_diverges` —
  expected and named, NOT a hidden gap.
-/

namespace DLNFibre.DLN.RLCT

open MeasureTheory Set
open scoped ENNReal BigOperators

/-! ## The carve realized — unconditional `∀r` Schur-core finiteness -/

/-- **The carve realized: unconditional `∀r` Schur-core finiteness.** Feeding the genuine
per-corank firing `schurRecStep_four : SchurRecStep 4 schurLambda` into the threshold-witnessed
wrapper `schurGen_lt_top_modulo_recStep` discharges its `hstep` hypothesis, yielding
`SchurCore 4 r c' T` for EVERY corank `r` below the genuine threshold `schurLambda r`
(`schurLambda 2 = 2`, `schurLambda 3 = 4`, `schurLambda r = 2r − 2` for `r ≥ 2`). This routes
around the deferred `schurRecStep4_stub` (a `sorry`, out-of-chain), so the conclusion is
hypothesis-free and axiom-clean. -/
theorem schurGenFin :
    ∀ r : ℕ, ∀ c' : ℝ, 0 < c' → c' < schurLambda r →
      ∀ T : ℝ, 0 < T → SchurCore 4 r c' T :=
  schurGen_lt_top_modulo_recStep schurRecStep_four

/-! ## The gated R1-gate headline -/

variable {L : ℕ}

/-- **The gated R1-gate headline (R1-UPPER wired; `hbox`/`hdiv` explicit).** For an arbitrary
width vector `M`, given `hpos : 1 ≤ minAdm M`, the named box-finiteness
`hbox : RouteMBoxThresholdFinite M`, and the box-divergence field `hdiv` (the R1-LOWER atom,
threaded as a hypothesis), the R1 gate is closed: there is a resolution chart family `(ι, d, k, h)`
with `rlctAtOn (dlnLoss M 0) (deepest) = ⨅ leaf, monomialThreshold`. The `hfin` field is the gated
`layerCover_hfin_of_box M hpos hbox` (the R1-UPPER finiteness leg, sorry-free); the cover assembles
via `routeMLayerCover_of_atoms`; the value lane via `resolution_charts_of_layerCover`. No `sorry`
upstream of either supplied field; the axiom footprint is the clean three plus the single cited S2
axiom `monomial_rlct`, which enters via the `hfin` LEG (`layerCover_hfin_of_box`, the achiever-leaf
box-divergence) — the value lane and the cover assembly are themselves clean-three. -/
theorem r1Upper_resolution_charts_of_box (M : Fin (L + 1) → ℕ) (hpos : 1 ≤ minAdm M)
    (hbox : RouteMBoxThresholdFinite M)
    (hdiv : ∀ c' : NNReal,
      (∃ i : (routeLayerAtlas M).ι,
        monomialThreshold (layerD M i) (layerK M i) (layerH M i) ≤ (c' : ℝ≥0∞)) →
      ∀ ε > 0, ∫⁻ x in cubeBox (routeMAmbient M) ε,
        ENNReal.ofReal (|routeMCore M x| ^ (-(c' : ℝ))) = ⊤) :
    ∃ (ι : Type) (_ : Fintype ι) (d : ι → ℕ) (k h : (i : ι) → Fin (d i) → ℕ),
      rlctAtOn (fun A : Params M =>
          dlnLoss M (0 : Matrix (Fin (M 0)) (Fin (M (Fin.last L))) ℝ) A) (fun _ => 0 : Params M)
        = ⨅ i : ι, monomialThreshold (d i) (k i) (h i) :=
  resolution_charts_of_layerCover M
    (routeMLayerCover_of_atoms M (layerCover_hfin_of_box M hpos hbox) hdiv)

end DLNFibre.DLN.RLCT
