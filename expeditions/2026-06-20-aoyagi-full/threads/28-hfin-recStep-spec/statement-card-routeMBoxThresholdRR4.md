# Statement card — `RouteMBoxThresholdRR4` (the `(r,r,4)` binding-p=4 `hbox` discharge ∀r)

> **Module.** `DLNFibre.DLN.RLCT.Validate.RouteMBoxThresholdRR4`
> (`lean/DLNFibre/DLN/RLCT/Validate/RouteMBoxThresholdRR4.lean`). Branch `genm-n4` (base `e2941aa1`),
> commit `425fe645`. NOT yet wired into `DLNFibre.lean` (single-writer aggregator — controller).
>
> **Scope.** The carve-based discharge of the named gap `RouteMBoxThresholdFinite M` for the depth-2
> `(r,r,4)` family — generalising the `(3,3,4)` anchor (`r=3`) to ALL `r`. Statement diff-gated +
> APPROVED by the controller before build.

## The honest scope (why only `(r,r,4)`)

The broad "binding-p=4 family" is a **research wall** (decorrelated-Codex `xhigh`, two obstructions:
depth-`≥3` front-peel threshold undershoot `min_s M_s/2 < ½·minAdm`; off-`(r,r,4)` shape mismatch).
The `(r,r,4)` family is the only one reaching `½·minAdm` through the `p=4` SchurCore chain: `prod
(![r,r,4]) A = A0·A1` (depth-2) is ALREADY the `SchurCore 4 r` shape (`Δ = A0` square `r×r`, `S = A1`
free `r×4`) — NO front-peel (Stage-1 empty), NO shape massage. The depth-`≥3` L-fold reduction is the
genuine new math, left as the precisely-named gap `RouteMBoxThresholdFinite` for general `M`.

## Proved (forced `#print axioms`, oleans deleted — all `[propext, Classical.choice, Quot.sound]`)

- **D4 `routeMBoxThresholdFinite_rr4_of_schurRecStep (hstep : SchurRecStep 4 schurLambda) (r : ℕ) :
  RouteMBoxThresholdFinite (![r,r,4])`** — GIVEN the carve `hstep`, the box integral is finite below
  `½·minAdm = schurLambda r` for all `r`. Carries ONLY the `hstep` hypothesis (the carve's content;
  `schurRecStep_four`, landed + certified on the carve branch) — the theorem itself is axiom-clean
  (no `monomial_rlct`: the SchurCore route is S2-free, `RouteMSchurFiring` header). Assembly: `c'=0`
  volume bound; `0<c'` → D1 rewrites `½·minAdm = schurLambda r`, D3 reshapes the box integral to
  `SchurCore 4 r c' 1` (definitional), `schurGen_lt_top_modulo_recStep hstep r` gives `< ⊤`.
- **D1 `minAdm_rr4_eq (r) : (minAdm (![r,r,4]):ℝ)/2 = schurLambda r`** — the threshold match. `r≥2`:
  both `2r−2` (`minAdm = minAdmRec = 4r−4` via `minAdmRec_rr4_ge2`; `schurLambda r = 2r−2`); `r=0,1`:
  the `0, ½` leaves (`decide` on `minAdmRec`). CLEAN-three, pure `ℕ`/`inf'` arithmetic.
  - `minAdmRec_rr4_ge2 (r) (2≤r) : minAdmRec (![r,r,4]) = 4r−4` — `inf'_{t≤r}((r−t)²+4t) = 4r−4` by
    `le_antisymm` (witness `t=r−2`; per-term `rr4_term_ge`). The `(![r,r,4]) 0/1 = r` reductions handled
    in the leaf goals, never rewritten under the `inf'` dependent-nonempty motive.
  - `rr4_term_ge` / `four_mul_le_sq_add_four` — the `4r−4 ≤ (r−t)²+4t` core (`= (s−2)² ≥ 0`).
- **D2 `eParamsRR4 (r) : Params (![r,r,4]) ≃ᵐ (Fin r → Fin r → ℝ) × (Fin r → Fin 4 → ℝ)`** +
  `measurePreserving_eParamsRR4` — the depth-2 layer reshape (literal ∀r generalisation of
  `eParams334`). + `eParamsRR4_preimage_box`, `frobSq_prod_eq_eParamsRR4` (via the local
  `prod_two_layer_rr4`), `measurableSet_paramsBoxM_rr4`.
- **D3 `routeMLayerBoxIntegral_rr4_eq (r c') : routeMLayerBoxIntegral (![r,r,4]) c' 1 = ∫_{A0∈matBox r
  r 1}∫_{A1∈matBox r 4 1} frobSq(A0·A1)^{−c'}`** — the reshape identity (∀r generalisation of
  `routeMLayerBoxIntegral_M334_eq`; `eParamsRR4` MP + Tonelli).

## Threshold match (verified)
`minAdm (![r,r,4]) = 4r−4 = 2·schurLambda r` (the `t`-min of `(r−t)²+4t` over the real `minAdmRec`;
sympy exact r=0..7: `0,1,4,8,12,16,20,24`), so `½·minAdm = schurLambda r` — the gate fires up to
EXACTLY the SchurCore chain's threshold, non-vacuous ∀r.

## What this composes with
- `routeMCore_threshold_lt_top_of_box M (routeMBoxThresholdFinite_rr4_of_schurRecStep hstep r) c' hc'`
  gives the hfin bound `∫_{routeMBaseNbhd (![r,r,4])} |routeMCore|^{−c'} < ⊤` for `c' < ½·minAdm`.
- `layerCover_hfin_of_box (![r,r,4]) hpos (routeMBoxThresholdFinite_rr4_of_schurRecStep hstep r)` feeds
  the cover assembler's `hfin` field. So the FULL R1 cover discharge (`routeMLayerCover_of_atoms`) holds
  for the `(r,r,4)` family modulo only the carve `hstep` (+ the banked `hdiv` atom).

## S2-hygiene
The whole file is `[propext, Classical.choice, Quot.sound]` (forced). The carve's content + `monomial_rlct`
(if any) sit in the `hstep` hypothesis, not the proof. D1 is pure `ℕ`/`inf'` arithmetic. No new axiom.

## Status
- Green (`lake env lean` EXIT 0 + `scripts/lb` 8285 jobs). Forced `#print axioms` clean on all 5 results.
- Zero `sorry`/`axiom`/`native_decide`/`#exit` (only docstring string-hits). 13 new top-level names
  clash-free vs the `DLNFibre/` tree.
- **FIDELITY REVIEW: pending** (reviewer requested).
