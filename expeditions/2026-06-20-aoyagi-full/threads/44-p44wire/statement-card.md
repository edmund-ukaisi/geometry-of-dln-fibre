# Statement card — #44 L2 deepest-point normal form (front-aligned B)

> **Claim.** At depth `L = 2`, for a rank-`r` target `B` whose pivot columns are front-aligned
> (`hJfront`, #100) and whose top `r` rows have full rank (`htop`, #154), with strictly positive
> reduced widths (`hpos : ∀ s, r < H s`), and GIVEN the R1 reduced-core value
> `hcore : rlctAtOn (dlnLoss (H−r) 0) 0 = ofReal(lambdaCore (H−r))`, the local RLCT of the
> square-Frobenius loss `dlnLoss H B` at the deepest singular point equals the regular gauge shift
> `r(H⁰+Hᴸ−r)/2` plus the closed-form singular core `ofReal(lambdaCore (H−r))` — the exact
> `deepest_regular_core_normal_form` (Skeleton #44) conclusion.
>
> - **Lean:** `DLNFibre.DLN.RLCT.deepest_regular_core_normal_form_frontAligned`
>   (`lean/DLNFibre/DLN/RLCT/Validate/DeepestL2NormalFormFrontAligned.lean` @ `2daee3e4`)
> - **Gloss.** Specialises Skeleton #44 to `L = 2` and to a front-aligned `B`. The conclusion is
>   `rlctAt H (dlnLoss H B) (deepestPoint H r B hB hr hL) = (r·(H 0 + H (last) − r) : ℕ)/2
>   + ENNReal.ofReal (lambdaCore (fun s => H s − r))`, identical to #44's. The extra hypotheses over
>   #44 are: `hLlt : L < 3` (pins `L = 2`), `hJfront`/`htop` (front-alignment of `B`), and `hcore`
>   (the R1 reduced-core value).
> - **Proved.** The reduction chain unconditionally, at `L = 2`, for front-aligned `B`:
>   germ-nonvanishing `hGne` (from `hpos`, via banked `dlnLoss_deepest_core_ae_ne_zero`); the gauge
>   chart `Γ : DeepestGaugeChart` (clean-three, from `deepest_gauge_construction_L2`); the value-free
>   reduction `rlctAt(dlnLoss B)(deepest) = nReg/2 + rlctAtOn(dlnLoss (H−r) 0) 0` (`deepest_squeeze_
>   transport` ▸ `deepest_regular_smooth_split`); then `▸ hcore` to the closed form. Axiom-clean
>   `[propext, Classical.choice, Quot.sound]`.
> - **Assumed.** `hJfront` (#100, B's pivot columns at front) and `htop` (#154, B's top-r rows full
>   rank) — both carried as explicit hypotheses (front-aligned scope), NOT discharged here. `hpos`
>   (strict reduced-width positivity, the headline carries it). `hLlt : L < 3` (depth exactly 2).
> - **Cited.** none reproved here; the banked clean-three pieces consumed are `deepest_gauge_
>   construction_L2`, `deepest_squeeze_transport`, `deepest_regular_smooth_split`,
>   `dlnLoss_deepest_core_ae_ne_zero` (all sorry-free on canonical).
> - **Deferred.** `hcore` — the R1 reduced-core value `rlctAtOn (dlnLoss (H−r) 0) 0 =
>   ofReal(lambdaCore (H−r))` (R1/resolution_charts lane, in flight). Left as an explicit hypothesis,
>   NOT a sorry. AND: the closure for an ARBITRARY (not front-aligned) `B` at its own arbitrary
>   `deepestPoint` — see "Findings", route (a) downstream ⨅-WLOG (bounded) or route (b) gauge-orbit
>   invariance (NEW MATH).
> - **Route.** Build the `DeepestGaugeChart` from the hoisted clean-three `deepest_gauge_construction_L2`
>   (NOT the general `deepest_gauge_chart_construct`, whose term carries the L≥3 #120 sorries and so is
>   not axiom-clean even at L=2 — a green build masked the persisted `sorryAx`, exposed by `#print
>   axioms`). Then replicate `deepest_regular_core_reduces`'s two-rewrite body
>   (`deepest_squeeze_transport` ▸ `deepest_regular_smooth_split`) with the constructed chart so the
>   proof does NOT ride on the bare `deepest_gauge_squeeze_exists` stub; finish `▸ hcore`.
> - **Status.** sorry-free (clean-three, hcore an explicit hypothesis); reviewer fidelity check pending.

## Findings (verify-first gate, genm-p44wire)

1. **The general `deepest_gauge_chart_construct` is not axiom-clean at L=2.** Its term carries the
   L≥3 `#120` interior/grouped-diffeo sorries (`DeepestL2Wiring.lean:844,847,989`), which `hL2 : 2 ≤ L`
   does not eliminate. The green build masked the persisted `sorryAx`; `#print axioms` exposed it.
   The brief's premise "clean-three at L=2 via `deepest_gauge_chart_construct`" was false. Routed
   around via the hoisted clean-three `deepest_gauge_construction_L2` (UPDATE-375, rung 1/5 at L=2).

2. **Arbitrary-B closure at its own `deepestPoint` is NEW MATH, not bounded perm-transfer wiring.**
   The banked WLOG transports RLCT between matched points
   (`rlctAt(dlnLoss Bpr)(τ(deepestPoint B)) = rlctAt(dlnLoss B)(deepestPoint B)`), but
   `τ(deepestPoint B)` ≠ the arbitrary `Classical.choice` `deepestPoint Bpr` the chart computes at;
   stitching needs local-RLCT gauge-orbit invariance at the deepest stratum (decorrelated Codex
   xhigh, `codex/p44-route-answer.md`). So hJfront/htop stay as hypotheses; the perm-WLOG belongs
   DOWNSTREAM at the `⨅ optimalSet` level (`Set.BijOn.iInf_congr`, `rlct_infimum_{row,col}Perm_eq`),
   where point-matching is global — the D1 headline consumer's natural shape.
