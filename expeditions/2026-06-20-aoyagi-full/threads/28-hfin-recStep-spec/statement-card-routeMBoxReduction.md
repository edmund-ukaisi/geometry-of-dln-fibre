# Statement card — `RouteMBoxReduction` + `RouteMBoxReductionWitness` (the ∀M hfin box-reduction)

> **Modules.** `DLNFibre.DLN.RLCT.Validate.RouteMBoxReduction`
> (`lean/DLNFibre/DLN/RLCT/Validate/RouteMBoxReduction.lean`) and
> `DLNFibre.DLN.RLCT.Validate.RouteMBoxReductionWitness`
> (`…/RouteMBoxReductionWitness.lean`). Branch `genm-n4` (base `e2941aa1` on `origin/genm-firing`).
> NOT yet wired into `DLNFibre.lean` (single-writer aggregator — controller adds the imports).
>
> **Scope.** The decision-independent **reduction half** of the N4 hfin upper bound: the generic ∀M
> measure-preserving reduction of the flat-coordinate hfin integral to the layer-product box integral,
> plus the named analytic gap and the `(3,3,4)` witness that the gap is inhabited.

## The category-error finding that scopes this card

A literal ∀M reduction of `routeMCore M` to a `SchurCore 4 r` two-matrix box is **mathematically
impossible** (decorrelated-Codex `xhigh`-confirmed):
1. `prod M A` is an **L-fold** product `A0·…·A_{L-1}`, not a two-matrix product. The r=3 template
   `routeMCore_M334_le_matBox` works only because `M334` has depth `L = 2`.
2. `SchurCore` is hardcoded at column count **`p = 4`**; the generic output width `M (last L)` is
   arbitrary.
3. `schurLambda r` (the p=4 threshold `0,½,2,4,6,…`) is **not** `½·minAdm M` in general (the
   iterated-fibre front-peel caps at `min_s(M s)/2`; the SchurCore radial blow-up is genuinely needed
   to reach `½·minAdm`, and only matches for the specific p=4 binding family).

So the SchurCore chain (`schurGen_lt_top_modulo_recStep`) closes the **specific binding core**, not
arbitrary `M`. The honest ∀M deliverable is the box-reduction below + a **named** analytic gap.

## Proved (axiom-clean `[propext, Classical.choice, Quot.sound]`, FORCED `#print axioms`)

- **`routeMCore_le_matBox (M c')`** — `∫_{routeMBaseNbhd M} |routeMCore M x|^{−c'} ≤
  routeMLayerBoxIntegral M c' 1`. Pure measure-preserving plumbing (open box `(−1,1)^N` ⊆ closed cube
  `[−1,1]^N`; transport through `paramsEquivFlat` MP to `paramsBoxM M 1`; rewrite by the zero-target
  loss identity `dlnLoss M 0 A = frobSq(prod M A)`). Holds for **every** `c'` (no positivity). The
  L-fold ∀M analog of `routeMCore_M334_le_matBox`.
- **`routeMLayerBoxIntegral M c' T`** := `∫_{A∈paramsBoxM M T} frobSq(prod M A)^{−c'}` — the
  layer-product box-integral target (RHS of the reduction).
- **`RouteMBoxThresholdFinite M : Prop`** := `∀ c' : ℝ≥0, c' < ½·minAdm M → routeMLayerBoxIntegral M c'
  1 < ⊤` — the **named analytic gap** (the genuine open content; per-family work).
- **`routeMCore_threshold_lt_top_of_box (M) (hbox) (c') (hc')`** — `∫_{routeMBaseNbhd M} |routeMCore M
  x|^{−c'} < ⊤` for `c' < ½·minAdm M`, GIVEN `hbox : RouteMBoxThresholdFinite M`. (`c' = 0` volume
  bound; `0 < c'` the reduction + `hbox`.) The ∀M analog of `routeMCore_M334_threshold_lt_top`, with
  the analytic finiteness made an explicit hypothesis — the caveat lives beside the claim.
- supporting generic lemmas (all axiom-clean): `dlnLoss_zero_eq_frobSq`, `paramsBoxM`,
  `paramsEquivFlat_decodeM`, `paramsEquivFlat_preimage_paramsBoxM`, `measurableSet_paramsBoxM`,
  `routeMCore_nonneg`.

### The `(3,3,4)` witness (bedrock: the gap is inhabited, shown in-file)

- **`routeMLayerBoxIntegral_M334_eq (c')`** — `routeMLayerBoxIntegral M334 c' 1 = ∫_{A0∈matBox 3 3
  1}∫_{A1∈matBox 3 4 1} frobSq(A0·A1)^{−c'}` (the `eParams334` MP layer split + Tonelli; `paramsBoxM
  M334 1` is `rfl`-equal to `paramsBox334`).
- **`routeMBoxThresholdFinite_M334`** — `RouteMBoxThresholdFinite M334` holds (the closed `(3,3,4)`
  chain `matBox334_blowup_lt_top` discharges it; `c' = 0` volume bound).
- **`routeMCore_threshold_lt_top_M334_via_box`** — feeding the witness into the generic theorem
  reproduces exactly `routeMCore_M334_threshold_lt_top` (the generic form is a faithful generalisation,
  no loss on the validated instance).

## NOT done (deliberate; diff-gated to controller)

- The bare-`sorry` skeleton `routeMCore_threshold_lt_top` in `RouteMSchur.lean:426` is **untouched**.
  Its current signature claims the hfin bound ∀M unconditionally — which is the overclaim (unprovable
  ∀M without the box-finiteness). Re-point options (R1 add `hbox` hyp / R2 leave sorry + pointer / R3
  delete in favour of `…_of_box`) are the controller's call.
- The p=4-family corollary wiring `schurRecStep_four` → `RouteMBoxThresholdFinite` for the binding
  family is downstream of the carve (`schurRatioResidGen_mid`) landing.

## S2-hygiene
Pure MP plumbing + the banked `(3,3,4)` chain; no `monomial_rlct`, no new axiom. Both files
`[propext, Classical.choice, Quot.sound]`.

## Status
- `RouteMBoxReduction.lean` builds green (`scripts/lb`, 2708 jobs); `RouteMBoxReductionWitness.lean`
  green (8290 jobs).
- Zero `sorry`/`axiom`/`native_decide`/`#exit` (the only `sorry`/`axiom` string-hits are docstring
  prose). Forced `#print axioms` (olean-deleted) clean on all named results.
- Name-clash gate: all 10 new top-level names clash-free vs the `DLNFibre/` tree.
- **FIDELITY REVIEW: SURVIVED** (independent `reviewer` seat, decorrelated-Codex-corroborated). All six
  checks pass: the `routeMCore_le_matBox` inequality faithfully encodes the open-box ⊆ box-integral
  domination and is genuinely ∀M; `RouteMBoxThresholdFinite` is the honest non-circular gap (box
  integral over `paramsBoxM`, distinct from the conclusion over `routeMBaseNbhd`); the `c'=0` branch is
  sound; the `(3,3,4)` witness is a REAL discharge (`routeMLayerBoxIntegral_M334_eq` RHS is
  character-for-character the `matBox334_blowup_lt_top` integrand; `paramsBoxM M334 1 = paramsBox334` is
  a true `rfl`; `routeMCore_threshold_lt_top_M334_via_box` is character-for-character
  `routeMCore_M334_threshold_lt_top`); no overclaim (the ∀M-unconditional overclaim is correctly
  quarantined in the untouched `RouteMSchur:426` skeleton); axioms `[propext, Classical.choice,
  Quot.sound]` under FORCED recompile (reviewer deleted the correct oleans, confirmed `Built` not
  `Replayed`). Cosmetic `longLine` style warnings noted, non-blocking (sibling files carry 14–135 each).
