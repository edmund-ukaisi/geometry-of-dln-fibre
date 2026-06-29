# Handoff — the L=2 OPAQUE-WIDTH chart (discharge the two ∀M hypotheses of the conditioned-box headline)

**For:** a fresh hand making `routeMCore_box_diverges_smearedL2` general-over-widths (the L=2 slice of the
general smeared result). **From:** genm-smeared3 (the conditioned-box headline tide). **Branch base:**
`genm-smeared3` @ `0b9d35ec` (banked on origin).

## Where we are

The L=2 conditioned-box headline ASSEMBLY is banked, sorry-free, axiom-clean, reviewer-PASS:

    routeMCore_box_diverges_smearedL2   (RouteMSmearedHeadlineL2.lean)

It REDUCES the headline `∫⁻_{cubeBox N ε} |routeMCore M x|^{−c'} = ⊤` (c' ≥ ½·minAdm) to NAMED per-family
chart facts on a CONDITIONED box `condBox p box δ`. The `(2,3,1)` instance
`routeM231sm_box_diverges_via_condBox` (RouteMSmearedHeadlineL2Inst.lean) WITNESSES the hypothesis bundle
is jointly satisfiable (non-vacuity). Your job: discharge the TWO genuinely-analytic / cast-heavy
hypotheses GENERICALLY over opaque widths `M : Fin 3 → ℕ`, so the headline holds for the whole L=2 smeared
family (not just (2,3,1)).

The exact hypotheses to discharge (read `routeMCore_box_diverges_smearedL2`'s signature):

1. **The peeled rate** `hRate : routeMCore M (ψ (R (insertNth p z y))) = z²·Uy y` on the conditioned box,
   + `hUmeas`, `hUpos` (Uy measurable + positive there). This is GAP-1 (item 4): the opaque-width
   ψ/R/DECODE. The heavy piece.
2. **Field A** `hSpre : condBox ⊆ (ψ∘R)⁻¹(cubeBox ε)` + `hboxmeas`/`hboxmeasAll`/`hboxpos`. The generic
   conditioned Λ₀-bound (analytic), feeding the per-entry ≤ ε bound.

Plus the chart's MP/embedding/radial facts (`hmp`/`hemb`/`hRderiv`/`hRinj`/`hRdet`) — these are the
BANKED generic bricks (see below), the lightest part.

## The chart, precisely (the gap-1 resolution, verified — DO NOT re-derive the rate)

DEFINE `φ := ψ ∘ R`, prove the DECODE (the false `phiL2 = ψ∘R` is NOT the target — see
`gap1-phiL2-vs-psiR-finding.md`):

    (paramsEquivFlat M).symm (ψ (R u)) = chartL2Params M hrs A0 z H̄_unit Sbot Λ₀     (Hbar := H̄_unit)

where `H̄_unit` is the R-blown unit angular block (pivot entry fixed = 1, others = the h-coords). Then the
BANKED `prod_chartL2Params` / `routeMCore_phiL2` (RouteMSmearedChartL2.lean) give the rate
`z²·‖P₁·H̄_unit‖²` IMMEDIATELY. So the rate is NOT re-derived — the new work is the ψ/R flat maps + the
decode.

- `R := pivotBlowupOn deepestTopCoords p` — the polynomial radial blow-up. Banked generic facts
  (S1G5Charts.lean): `pivotBlowupOn_hasFDerivWithinAt`, `pivotBlowupOn_injOn`, `pivotBlowupOnDeriv_det`
  (det `= (x p)^{active.card−1}`; with `active.card = minAdm = r·c` via `minAdm_eq_deepRank_mul_last`, the
  exponent is `minAdm−1`). `deepestTopCoords M` = the `r·c` flat coords of the deepest factor's TOP r rows
  (the [HIGH]-cast FlatIdx Finset, item 1).
- `ψ := paramsEquivFlat ∘ packM ∘ shearM`. `packM := (flatEquivOf M e).symm` for a slot bijection
  `e : Fin N ≃ FlatIdx M` (MP via banked `measurePreserving_paramsPack_of_flatIdxEquiv`). `shearM` = the
  Λ₀-shear (MP via banked `measurePreserving_shearM` for ANY coreSet + measurable shift; Λ₀ measurability
  via banked `measurable_lamEntry`). MP+embedding of ψ by composition.

## THE PLAN (Codex design-review, items 1-6 — reuse the precedents, generalize to opaque widths)

The L=2 PRECEDENT is fully worked TWICE: `RouteM231Smeared` (r=2,s=1,c=1; 1125 lines) and `RouteM132Smeared`
(r=1,s=2,c=2). Both are hardcoded `Fin 9`. GENERALIZE them to opaque `M 0, M 1, M 2` widths.

1. **`deepestTopCoords M`** — `Finset (Fin (routeMAmbient M))`, the `r·c` flat coords for the deepest
   factor's top r rows. card = `r·c = minAdm`. ([HIGH]-cast FlatIdx bookkeeping — item 1.)
2. **`R := pivotBlowupOn (deepestTopCoords M) p`** (p = the deepest-factor (0,0) flat coord). det/injOn/
   fderiv are the GENERIC banked lemmas.
3. **`ψ := paramsEquivFlat ∘ packM ∘ shearM`** — generalize `pack231`/`shear231`; MP+embedding by
   composition (generalize `measurePreserving_psi231` / `measurableEmbedding_psi231`).
4. **The DECODE** (generalize `chartParams231_eq_pack_shear_R`). ([HIGH]-cast, item 4 — the dominant cost.)
   **Codex's strategy (do NOT fin_cases i/j — opaque widths):** prove it LAYERWISE.
   `ext ℓ i j; fin_cases ℓ` (only `Fin 2` layers is safe) — layer 0 = `A0` (free front), layer 1 =
   `chartL2Deep` (the row-split deep block). Inside each layer, reduce pack/shear/R via their defining
   equations + the slot bijection's symm round-trip, behind NAMED lemmas
   (`deepWidthEquiv_left_apply`/`_right_apply`, `chartL2Deep_top_entry`/`_bottom_entry`,
   `pivotBlowupOn_pivot`/`_active_ne_pivot`/`_inactive`, `packM_layerN_entry`, `shearM_top`/`_bottom`).
   TRAP: do NOT unfold `deepWidthEquiv` globally or let `simp` see raw `hrs` casts early — normalize
   THROUGH the API. NOTE: there is NO banked coordinate-level form of `shearM` (only its MP) — you must
   define shearM's explicit per-coord form (like `shear231`'s `if`) AND connect it to
   `measurePreserving_shearM`'s conjugacy form (the cast-heavy MP bridge). Consider defining shearM
   explicitly per-coord and proving MP by the conjugacy equality, OR pushing harder on the splitOfCoreSet
   coordinate lemmas (`splitOfCoreSet_core`/`_spec`, CoreSplitMP.lean).
5. **Field A** (generalize `subBox231_subset_preimage` / `subBox231_lam_bound`). The generic conditioned
   Λ₀-bound `|Λ₀ i j| ≤ K(δ)` on the conditioned box (analytic). Codex: carry it as a hypothesis OR derive
   from a well-conditioning predicate (`det(P₁ᵀP₁) ≥ κ` on the box). Then each chart-entry ≤ ε by the
   decode (A0 entries are free coords ≤ δ; deep-top entries `z·H̄_unit − Λ₀·S_bot` need the Λ₀-bound;
   bottom = S_bot ≤ δ). The `(2,3,1)` uses an explicit 2×2 cofactor + nlinarith; opaque-r,s needs the
   general inverse-norm bound (`measurable_matrixInv_entry` exists; the BOUND is new analysis).
6. **Assemble** → feed `routeMCore_box_diverges_smearedL2` (banked). The CONDITIONED box is essential
   (NOT the full smearedSubBox — see the soundness finding below).

## CRITICAL: use a CONDITIONED box (the soundness finding — reviewer-corroborated)

The genm-smeared2 `smearedSubBox` (pivot in Ioo 0 δ, ALL other coords in the FULL Icc −δ δ) is VACUOUS for
the rational-shear chart: `axisPeel`'s `hUpos: 0<Uy` over the full box is unsatisfiable because
`U=‖P₁H̄‖²=0` at the rank-block-zero corner. USE the banked `condBox p box δ` (RouteMSmearedHeadlineL2.lean)
with the rank-block diagonal pinned in [δ/2,δ] (keeps `det P₁` away from 0). Your generic `box` must
condition the rank-block coords (the r columns of A0 that form P₁) so `det(P₁ᵀP₁) > 0` on the box.

## REUSE (banked, clean-three, axiom-clean)

- `prod_chartL2Params`, `routeMCore_phiL2`, `chartL2Params`, `chartL2Deep`, `deepWidthEquiv`, `deepBlock`,
  `deepBlock_collapse` (RouteMSmearedChartL2 / RouteMSmearedTelescope) — the RATE core.
- `frontShear_cancel_general` / `prodAux_frontShear_cancel_general` (RouteMSmearedFrontFactor) — supplies
  `hcancel : P₁·Λ₀ = P₂` (general r, off the two poles).
- `minAdm_eq_deepRank_mul_last` (RouteMSmearedMinAdm) — `minAdm = r·c` (the det exponent).
- `measurePreserving_shearM`, `measurable_lamEntry`, `measurable_matrixInv_entry` (RouteMSmearedPerFamily).
- `measurePreserving_paramsPack_of_flatIdxEquiv`, `flatEquivOf`, `flatEquivOf_symm_coord` (ParamsReshapeMP).
- `pivotBlowupOn_*` (S1G5Charts) — R's det/injOn/fderiv.
- `condBox` + `condBox_weighted_diverges` + `hSdiv_of_peeled_rate_onBox` + `routeMCore_box_diverges_smearedL2`
  (RouteMSmearedHeadlineL2, THIS tide) — the conditioned-box engine + the assembly you feed.

## DISCIPLINE

≤4 cast-attempts per [HIGH]-cast sub-piece (items 1, 4) + decorrelated Codex (it may be at-capacity / slow
on the AISI tools update — fall back to empirical `lake env lean` probes) then bank+report the exact stuck
goal. Force `#print axioms` after olean delete (the masking guard — caught a stale-olean sorryAx THIS tide).
Branch-guard (pwd under .claude/worktrees/) before each commit. Green-gate before push (scripts/lb builds
import-closure only; the controller green-gates the full aggregator at the leg-close).

## OUTPUT

The two ∀M-at-L=2 hypotheses discharged generically → `routeMCore_box_diverges_smearedL2` instantiated
over opaque widths (the L=2 slice of the general smeared result), sorry-free + axiom-clean + a statement
card. Non-vacuity already anchored by (2,3,1). The L≥3 generalization (prodAux_front_peel) is a SEPARATE
sub-tide — NOT yours. Aggregator wiring is the controller's (smeared leg-close) — don't touch DLNFibre.lean.
