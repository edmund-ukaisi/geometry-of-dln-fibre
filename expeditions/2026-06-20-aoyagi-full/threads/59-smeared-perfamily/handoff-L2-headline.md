# Handoff — the L=2 smeared headline continuation (off genm-smeared2 @9e7513d6)

**For:** a fresh hand continuing the L=2 boundary-smeared headline. **From:** genm-smeared2 (this tide).
**Status:** the RATE + DIVERGENCE + INTERFACE + arithmetic are ALL banked axiom-clean; gap #1 (the
`φ=ψ∘R` soundness) is VERIFIED + resolved; the decode slot-layout is VERIFY-REAL'd. The remaining work is
the chart-MAP construction (ψ/R flat maps + the decode) + field A (containment) → the headline.

## What is banked (reuse, do NOT rebuild) — all axiom-clean

- **Rate:** `routeMCore_phiL2` / `prod_chartL2Params` (`RouteMSmearedChartL2`) — `prod M (chartL2Params …)
  = z • (P₁·H̄)` for ANY `Hbar`, deepest factor row-split `r⊕s` via `deepWidthEquiv`. Takes
  `hcancel : P₁·Λ₀ = P₂` (supplied by `prodAux_frontShear_cancel_general` / `frontShear_cancel_general`,
  `RouteMSmearedFrontFactor`).
- **Divergence:** `hSdiv_of_peeled_rate` (`RouteMSmearedHeadlineIface`) — the contract's `hSdiv` from the
  peeled quadratic rate + `U`-positivity, via `smearedSubBox_weighted_diverges` /
  `axisPeel_diverges_of_quadratic_rate`.
- **Headline interface:** `routeMCore_box_diverges_on_smearedSubBox` (`RouteMSmearedHeadlineIface`) — the
  contract on `smearedSubBox p δ`; needs `ψ` MP+embedding, `R` radial (det/injOn/fderiv), `hSpre`
  (containment), `hSdiv`.
- **Arithmetic:** `minAdm_eq_deepRank_mul_last` (`RouteMSmearedMinAdm`) — `minAdm = deepRank·M_L = r·c`
  (so `active.card = minAdm` for the radial det `|z|^{minAdm−1}`).
- **The shear MP:** `measurePreserving_shearM` (`RouteMSmearedPerFamily`); `measurable_lamEntry` (Λ₀
  measurable); `smearedSubBox` + `measurableSet_smearedSubBox`.

## Gap #1 RESOLVED (verified, see `gap1-phiL2-vs-psiR-finding.md`)

`phiL2 ≠ ψ∘R` as maps (phiL2 carries no radial Jacobian; R carries `|z|^{minAdm−1}`). DO NOT prove
`phiL2 = ψ∘R`. Instead DEFINE the chart `φ := ψ∘R` and prove the DECODE:

    (paramsEquivFlat M).symm (ψ (R u)) = chartL2Params M hrs A0 z H̄_unit Sbot Λ₀     (Hbar := H̄_unit)

where `H̄_unit` is the R-blown unit angular block (pivot entry = 1). Then `prod_chartL2Params` gives the
rate immediately. VERIFIED (slot-layout, sympy on (1,3,2) + (2,3,1)): `R (z,h)↦(z,z·h)` reshapes the rc
deepest-top coords to `z•H̄_unit` with `H̄_unit` pivot = 1; `U = ‖P₁·H̄_unit‖²` is a z-free polynomial.

## The remaining construction (the fresh hand's work)

The **L = 2 PRECEDENT is fully worked**: `RouteM231Smeared` does ALL of this for `(2,3,1)` (1125 lines) —
`R231 = pivotBlowupOn {6,7} 6`, `pack231`/`shear231`, `chartParams231_eq_pack_shear_R` (THE decode),
`measurePreserving_psi231`, `measurableEmbedding_psi231`, `subBox231_*` (field A: `subBox231_lam_bound`
the Λ₀-bound, `chartParams231_entry_bound`, `subBox231_subset_preimage` the containment), `D231_abs_det`,
`routeM231sm_box_diverges`. The general L=2 opaque-width version GENERALIZES these:

1. **`deepestTopCoords M`** — a `Finset (Fin (routeMAmbient M))` of the `r·c` flat coords for the deepest
   factor's TOP `r` rows (filter `deepestCoords` to the top-r-rows; FlatIdx bookkeeping — the one new
   `Finset`). `card = r·c = minAdm`.
2. **`R := pivotBlowupOn (deepestTopCoords M) p`** (`p` = the pivot, the deepest-factor `(0,0)` flat coord).
   det/injOn/fderiv are the GENERIC `pivotBlowupOn` lemmas (S1G5Charts); det `= |u p|^{minAdm−1}` via
   `pivotBlowupOnDeriv_det` + `minAdm_eq_deepRank_mul_last`.
3. **`ψ := paramsEquivFlat ∘ packL2 ∘ shearL2`** — `shearL2` the Λ₀-shear (generalize `shear231`, MP via
   `measurePreserving_shearM`); `packL2` the reshape. MP + embedding by composition (generalize
   `measurePreserving_psi231` / `measurableEmbedding_psi231`).
4. **The decode** `(paramsEquivFlat).symm (ψ(R u)) = chartL2Params … H̄_unit` (generalize
   `chartParams231_eq_pack_shear_R`) — the slot-aligned identity (VERIFY-REAL'd). Then
   `prod_chartL2Params` → the rate → `hSdiv_of_peeled_rate` → the contract's `hSdiv`.
5. **Field A — containment** `smearedSubBox p δ ⊆ (ψ∘R)⁻¹(cubeBox ε)` (generalize `subBox231_subset_preimage`
   via the opaque-width Λ₀-bound `subBox231_lam_bound` → a general quantitative bound on `‖Λ₀‖` on the box).
6. Feed `routeMCore_box_diverges_on_smearedSubBox` → `routeMCore_box_diverges_smeared` (L=2).

**The [HIGH]-cast risk is item 1 (the FlatIdx `deepestTopCoords`) + item 4 (the decode slots).** Item 5
(field A) is real-analysis (the Λ₀-bound), not casts. Items 2-3 are mostly banked-generic composition.

## L ≥ 3 (separate sub-tide, controller-scoped)

Swap `prod_two_layer221` → `prodAux_front_peel` (banked) in `prod_chartL2Params`'s analog; the front
product `P = prodAux M A (L−1)` factors through the bottleneck (`prodAux_split_exists` →
`prodAux_frontShear_cancel_general`, banked, general r); `deepBlock_collapse` on the deepest factor is
unchanged. The only new work is the prefix-product front-peel casts.
