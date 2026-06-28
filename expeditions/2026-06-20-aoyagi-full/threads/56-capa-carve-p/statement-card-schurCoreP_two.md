# Statement card — `schurCoreP_two` (the r=2 corank-2 base, closing #146)

**Status:** `sorry-free`, **clean-three** `[propext, Classical.choice, Quot.sound]` (forced `#print
axioms`, oleans force-rebuilt). Closing it makes `routeMBoxThresholdFinite_rrp` (#146) FULLY sorry-free.
Awaiting reviewer fidelity check.

**File:** `lean/DLNFibre/DLN/RLCT/Validate/RouteMSchurCapACarveP.lean` (branch `genm-capa2`, off
`origin/genm-capa`@`105cadfd`; bump on change).

## The headline

```lean
theorem schurCoreP_two (p : ℕ) (hp : 0 < p) (hIH : SchurLowerIH p (schurLambdaP p) 2)
    (c' : ℝ) (hc0 : 0 < c') (hc' : c' < schurLambdaP p 2) (T : ℝ) (hT : 0 < T) :
    SchurCore p 2 c' T
```

— the SOLE remaining open sorry in the R1-UPPER `(r,r,p)` ∀p deliverable. `SchurCore p 2 c' T` asserts
the corank-2 free-box core `∫_{Δ∈matBox 2 2 T} ∫_{S∈matBox 2 p T} frobSq(Δ·S)^{−c'} < ⊤` for
`0 < c' < schurLambdaP p 2` (`= min(4, 1+p, 2p)/2`: p=1→1, p=2→3/2, p=3→2, p≥4→2).

## Dispatch — split on `le_or_gt (p/2) c'`

| regime | range | route | new lemmas |
|---|---|---|---|
| cap-B | `c' < p/2` (all p≥4 + small-p slice) | 4-chart radial cover (NO recursion) | `schurRatioResidP_capB_two_lt_top`, `schur_matBoxGen2_chart_capB_lt_top`, `schurCoreP_two_capB` |
| interior | `p/2 ≤ c' < schurLambdaP p 2` (only p∈{1,2,3}) | the `2≤r` carve (recursion to corank 1 via IH) | `schurRatioResidGen2_mid`/`_2`, `schur_matBoxGen2_chart_capA_lt_top`, `schurCoreP_two_interior` |

## The cap-B half (banked brick wired)

The cover machinery `matBoxGen_outer_flat` / `gFlatGen_cover_sum` is **`r`-general (NOT `hr`-gated)**, so
the 4-chart radial-`Δ` cover fires directly at r=2. Each chart factors (via `chart_integrand_factorGen`,
r-general) into the radial axis `|y|^{r²−1−2c'}` (`radial_aAxis_divisor_lt_top`, `c' < 4/2 = 2`) × the
angular residual `schurRatioResidP_capB_two_lt_top`, supplied per-`z` by the **already-banked**
`frobSq_capB_inner_two_le` (the `z`-uniform N2b→shear→Morse-dominator bound at r=2). The only `3≤r`-gated
brick (`RmatGnorm`) is avoided: at r=2 the pivot-normalised matrix is built **inline** by row/col-permuting
`RmatG` — the `r`-general `RmatG_pivot` / `RmatG_entry_le` give pivot `1` + `|entries| ≤ 1`.

## The interior half (the `2≤r` carve)

The firing's reshape (`RmatGnorm`/`zEG`/`ScCarve`) carries `hr : 3 ≤ r`, an **artefact** — each body works
at `2 ≤ r` (the `omega`s need only `0<r` / `1≤r`, `slotFunR_card`'s `nlinarith` only `1≤r`). Following the
predecessor's KEY option, the reshape is **reproduced once at `hr : 2 ≤ r`** (suffix `2`), reusable for a
future unified `2≤r` carve. The chain:

- **reshape primitives** (verbatim from firing, `3≤r → 2≤r`): `RmatGnorm2` (+`_pivot`/`_offpivot_le`),
  `innerSGenP_eq_norm2`, `slotMatG2`/`cellR2` (+inj/card/bij), `zσG2`/`zEG2` (+MP/symm/fst/snd/slot),
  carve readbacks `RmatGnorm2_carve_M22/g/b`, `ScCarve2_eq`.
- **residual closers** (`3≤r → 2≤r` of CapAP): `schurResidGP2_translate_le`, `coreSchurGenValP2_lt_top`
  (the residual lands at corank `r−1 = 1`, supplied by the abstract IH `hIH` at `j=1` = `SchurCore p 1`).
- **carve heart** `innerSGenCarve2_le` (mirror `innerSGenCarveP_le`): N2b (`j=1`) two-sided bound +
  `ofReal_rpow_le_const_mul` + the **landed `1≤r` shears** `frobSqTopRowP_eq_shearP1`/`stepShearP_r1` +
  `ScCarve2_eq` readback. `resolvedShiftRG2_le` (mirror `resolvedShiftRGP_le`): `T`-peel
  (`core_T_peel_le_aeG`, threshold `p/2`) + shifted residual.
- **assembly** `schurRatioResidGen2_mid` / `schurRatioResidGen2` (subcritical fold) /
  `schur_matBoxGen2_chart_capA_lt_top` (cap-A per-chart) / `schurCoreP_two_interior` (`r²`-chart cover).

## Axiom footprint (forced `#print axioms`, oleans CapACarveP/RecStepP/RRP deleted then rebuilt)

`schurCoreP_two`, `schurCoreP_capA`, `schurRecStep_p`, `routeMBoxThresholdFinite_rrp` are ALL
`[propext, Classical.choice, Quot.sound]` — **clean-three, no `sorryAx`, no `monomial_rlct` (S2-FREE), no
`native_decide`**. `RouteMSchurCapACarveP.lean` has ZERO `sorry`/`axiom`/`native_decide`.

## Fidelity notes (for the reviewer)

- The statement `SchurCore p 2 c' T` is the literal `r=2` instance of the common predicate — matches the
  `(r,r,p)` claim (`½·minAdm(![2,2,p]) = schurLambdaP p 2`). ✓
- The threshold split is exhaustive over `0 < c' < schurLambdaP p 2`: `c' < p/2` (cap-B) ∪ `p/2 ≤ c'`
  (interior); the interior is non-vacuous only when `p/2 < schurLambdaP p 2`, i.e. p∈{1,2,3} (at p≥4,
  `schurLambdaP p 2 = 2 = p/2`-or-below so the interior range is empty). ✓
- The interior recursion lands at corank `r−1 = 1`, supplied by the abstract IH `hIH` (not a hardcoded
  corank-1 result) — `coreSchurGenValP2_lt_top` invokes `hIH 1 _ _` = `SchurCore p 1`. ✓
- The `2≤r` reshape copies are verbatim-from-`RouteMSchurFiring` with `3≤r → 2≤r` — same proof structure,
  no new mathematics (the truth-value was banked at the r≥3 carve; this is its r=2 specialisation). ✓
- NOT separately aggregated — `RouteMSchurCapACarveP` is already imported (sits under `RouteMSchurRecStepP`
  → `RouteMBoxThresholdRRP`). No sibling name clashes (grep over the tree; the `2`-suffixed names appear
  only in this file). Full `lake build DLNFibre` green-gated.
