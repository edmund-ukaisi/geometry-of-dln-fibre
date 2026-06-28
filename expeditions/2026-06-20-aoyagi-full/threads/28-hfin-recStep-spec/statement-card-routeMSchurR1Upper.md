# Statement card — `RouteMSchurR1Upper` (the GATED R1-UPPER `resolution_charts` rung)

> **Claim.** The R1-UPPER carve is wired through to the R1-gate value statement: feeding the now-DONE
> per-corank firing `schurRecStep_four` into the threshold-witnessed wrapper yields the unconditional
> `∀r` Schur-core finiteness (`schurGenFin`); and, for an arbitrary width vector `M`, GIVEN the named
> box-finiteness `hbox : RouteMBoxThresholdFinite M`, the achiever box-divergence field `hdiv`, and
> `hpos : 1 ≤ minAdm M`, the R1 gate is closed —
> `rlctAtOn (dlnLoss M 0) (deepest) = ⨅ leaf, monomialThreshold`. This is the **conditional** headline
> rung (`hbox`/`hdiv`/`hpos` explicit), NOT the unconditional headline; the `_of_box` name marks the
> gating.
>
> - **Lean:** `DLNFibre.DLN.RLCT.schurGenFin` and
>   `DLNFibre.DLN.RLCT.r1Upper_resolution_charts_of_box`
>   (`lean/DLNFibre/DLN/RLCT/Validate/RouteMSchurR1Upper.lean` @ `28719ef6`)
> - **Gloss.**
>   - `schurGenFin : ∀ r : ℕ, ∀ c' : ℝ, 0 < c' → c' < schurLambda r → ∀ T : ℝ, 0 < T →
>     SchurCore 4 r c' T`. For every corank `r`, below the genuine threshold `schurLambda r`
>     (`= [0, ½, 2, 4, 6, …]`; `schurLambda 2 = 2`, `schurLambda 3 = 4`, `schurLambda r = 2r−2` for
>     `r ≥ 2`), the free-box Schur core `∫⁻ Δ in matBox r r T, ∫⁻ S in matBox r 4 T,
>     ofReal(frobSq(rmatMul Δ S)^(−c')) < ⊤`. It is exactly `schurGen_lt_top_modulo_recStep` applied
>     to the real firing `schurRecStep_four` — the `hstep` hypothesis discharged, so the conclusion is
>     hypothesis-free.
>   - `r1Upper_resolution_charts_of_box (M : Fin (L+1) → ℕ) (hpos : 1 ≤ minAdm M)
>     (hbox : RouteMBoxThresholdFinite M) (hdiv : <the routeMLayerCover_of_atoms hdiv-field shape>) :
>     ∃ (ι : Type) (_ : Fintype ι) (d : ι → ℕ) (k h : (i : ι) → Fin (d i) → ℕ),
>     rlctAtOn (fun A : Params M => dlnLoss M 0 A) (fun _ => 0) = ⨅ i, monomialThreshold (d i) (k i) (h i)`.
>     Given `1 ≤ minAdm M`, the named box-finiteness `hbox`, and the box-divergence field `hdiv`, there
>     is a resolution chart family `(ι, d, k, h)` for which the RLCT-at-the-deepest-point of the
>     zero-target DLN loss equals the infimum of monomial thresholds over the family. The witness is the
>     layer atlas: `ι = (routeLayerAtlas M).ι`, `d = layerD M`, `k = layerK M`, `h = layerH M` (chosen
>     inside `resolution_charts_of_layerCover`). The proof is one line:
>     `resolution_charts_of_layerCover M (routeMLayerCover_of_atoms M (layerCover_hfin_of_box M hpos hbox) hdiv)`.
> - **Proved.** Unconditionally (no `sorry`, forced `#print axioms` olean-deleted):
>   - `schurGenFin` — the **carve realized**. The full R1-UPPER analytic engine: `∀r` free-box
>     Schur-core finiteness below `schurLambda r`, with the per-corank recStep supplied by the genuine
>     firing `schurRecStep_four` (no stub, no hypothesis). Axiom profile
>     `[propext, Classical.choice, Quot.sound]` — the clean three (a pure finiteness statement, no RLCT
>     value).
>   - `r1Upper_resolution_charts_of_box` — the **composition** of the gated `hfin` leg
>     (`layerCover_hfin_of_box M hpos hbox`, sorry-free given `hbox`), the threaded `hdiv` field, the
>     cover assembly `routeMLayerCover_of_atoms`, and the value lane `resolution_charts_of_layerCover`,
>     into the `resolution_charts` existential (`rlctAtOn = ⨅ monomialThreshold`). What is proved here
>     is the WIRING — that those four pieces compose to the gate statement — not the gated inputs.
>     Axiom profile `[propext, Classical.choice, Quot.sound, monomial_rlct]`.
> - **Assumed.** Three explicit hypotheses of `r1Upper_resolution_charts_of_box`, supplied per family:
>   - `hpos : 1 ≤ minAdm M` — the network has a binding admissible cut (holds for every realistic `M`).
>   - `hbox : RouteMBoxThresholdFinite M` — the layer-product box integral
>     `∫_{A ∈ paramsBoxM M 1} frobSq(prod M A)^(−c') < ⊤` for `c' < ½·minAdm M` (the named analytic gap;
>     `RouteMBoxReduction.lean`). This is the bridge from the matBox/`frobSq(rmatMul Δ S)` world of
>     `schurGenFin` to the routeMCore box world; it is NOT supplied in this file.
>   - `hdiv` — the achiever box-divergence field (the R1-LOWER atom shape:
>     `∀ε>0, ∫_{cubeBox ε} |routeMCore M|^(−c') = ⊤` whenever some leaf threshold `≤ c'`), threaded as a
>     hypothesis. Deliberately NOT taken from the in-tree `RouteMLayerCoverGE.layerCover_hdiv`, which
>     rides the open R1-LOWER `sorry` `routeMCore_box_diverges_achiever` — routing through it would
>     import that `sorry` into the headline's axiom footprint.
> - **Cited.** `monomial_rlct` (`Skeleton.lean`) — the single permitted external citation (S2:
>   Aoyagi p.6 / Hironaka resolution; the monomial-RLCT threshold value + pole order). It enters the
>   headline through the **`hfin` LEG** `layerCover_hfin_of_box` (forced `#print axioms` = clean-three
>   + `monomial_rlct`): the premise reduction `layerCover_leafSum_lt_top_imp_lt_half_minAdm` uses the
>   achiever-leaf box-divergence (`monomialThreshold_singleton` + `monomialIntegrand_lintegral_box_eq_top`),
>   which rides the cited monomial threshold. The value lane `resolution_charts_of_layerCover` and the
>   cover assembly `routeMLayerCover_of_atoms` are themselves **clean-three** (both forced-checked) —
>   NOT the carriers, despite the `rlctAtOn`-equality conclusion. Same NET footprint as the in-tree
>   `routeM334_box_diverges`. `schurGenFin` does NOT cite it (no RLCT value). The matBox / `frobSq` /
>   `rmatMul` primitives, `Nat.strong_induction_on`, and the measure-preserving plumbing are
>   Mathlib v4.29 / proved on our side.
> - **Deferred.** The discharge of the two gating hypotheses (folded in later, NOT in this file):
>   - `hbox` ← the **binding `(r,r,4)` family** discharge `routeMBoxThresholdFinite_rr4_of_schurRecStep
>     (r) (hr : 2 ≤ r) (schurRecStep_four) : RouteMBoxThresholdFinite (![r,r,4])` (genm-n4, on
>     `origin/genm-n4`, NOT yet landed). It is exactly where `schurRecStep_four`/`schurGenFin` folds
>     into `hbox` — via `minAdm_rr4_eq : ½·minAdm(![r,r,4]) = schurLambda r` (the binding-family
>     threshold match) and `routeMLayerBoxIntegral_rr4_eq` (the box ↔ Schur-core reshape). `SchurCore`
>     is hardcoded at column count `4`; this discharge is the `(r,r,4)` family only (the binding family
>     where `½·minAdm M` matches the Schur threshold) — a category error for arbitrary output width
>     (decorrelated-Codex-confirmed), so there is no literal ∀M wiring.
>   - `hdiv` ← the achiever-leaf box-divergence: the worked anchors `(4,4,2,2)` / `(3,3,4)`
>     (sorry-free), and the general-`M` `routeMCore_box_diverges_achiever` (the ∀M-chart programme,
>     `RouteMLayerCoverGE`, currently a `sorry`).
> - **Status.** sorry-free (this module: zero `sorry`/`sorryAx`; the gating inputs are explicit
>   hypotheses, their discharges named above). Green-gate: bare
>   `lake build DLNFibre.DLN.RLCT.Validate.RouteMSchurR1Upper` = 8294 jobs, exit 0. Awaiting fidelity
>   review.

## Axiom profiles (forced `#print axioms`, olean-deleted, @ `28719ef6`)

    'DLNFibre.DLN.RLCT.schurGenFin' depends on axioms:
        [propext, Classical.choice, Quot.sound]
    'DLNFibre.DLN.RLCT.r1Upper_resolution_charts_of_box' depends on axioms:
        [propext, Classical.choice, Quot.sound, monomial_rlct]

`schurGenFin` is the clean three. `r1Upper_resolution_charts_of_box` adds `monomial_rlct` — the single
cited S2 axiom (tier-(ii)), which enters via the `hfin` leg `layerCover_hfin_of_box` (forced-checked
clean-three + `monomial_rlct`, the achiever-leaf box-divergence). The value lane
`resolution_charts_of_layerCover` and the cover assembly `routeMLayerCover_of_atoms` are themselves
forced-checked clean-three. Expected and named, NOT a hidden gap, and NOT a `sorryAx`.

## What this rung banks (the wire, not the discharge)

The carve produced `schurRecStep_four` (the per-corank firing, DONE on genm-capstone). This rung is the
PORT + WIRE that turns it into mathematics consumable by the R1 gate, in two honest steps:

1. **The engine, unconditional.** `schurGenFin` drops the inert `schurRecStep4_stub` (a `sorry`
   referenced by nothing) and feeds the real firing into the threshold-witnessed wrapper, so the
   `∀r` Schur-core finiteness below `schurLambda r` is now hypothesis-free and clean-three.

2. **The gate, conditional.** `r1Upper_resolution_charts_of_box` assembles the layer cover and the
   value lane into the `resolution_charts` existential, with `hbox`/`hdiv`/`hpos` explicit. It is the
   honest CONDITIONAL headline: at the binding `(r,r,4)` family every hypothesis discharges (`hbox` ←
   genm-n4's `routeMBoxThresholdFinite_rr4_of_schurRecStep schurRecStep_four`; `hdiv` ← the achiever
   divergence; `hpos` is arithmetic), so the rung is non-vacuous; but it does NOT claim the
   unconditional ∀M headline — the `(r,r,4)` discharge of `hbox` folds in from genm-n4 separately.

The remaining seam is the Phase-2 dev-aggregator wire-in (controller-sequenced): add the import set
ending with `RouteMSchurR1Upper` to `DLNFibre.lean`, and resolve the `e2` short-name clash
(`RouteMSchurDepth2.e2` vs `RouteM3333Atom.e2`, surfaces only at the full `lake build DLNFibre`).
