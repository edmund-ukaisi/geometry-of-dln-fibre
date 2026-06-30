# Statement card — #44 L2 deepest-point normal form (front-aligned B) + headline ⨅-WLOG (ROUTE a)

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

3. **The front-pivot-FRAME identity `hJfront` is not derivable from the WLOG's front-COLUMN rank.**
   `headline_frontRowColPivot_exists` gives the permuted target `Bpr`'s front-`r`-COLUMNS rank `r`,
   but `hJfront` is about `deepestPoint_frame_pivot_exists(Bpr).choose = frontEmbed` — the column
   pivot of the deepest-point MATRIX `deepestPoint Bpr (lastLayer)`, an arbitrary `Classical.choice`
   witness's structure, NOT `Bpr`'s columns. No bridge "front-col rank ⟹ frame pivot = frontEmbed" is
   banked (`hJfront` is consumed everywhere, produced nowhere). Carried as an explicit hypothesis in
   ROUTE (a) until built/adjudicated. (`htop` IS supplied directly by the WLOG — `hBpr_top` matches.)

## ROUTE (a) — the headline ⨅-WLOG (controller-decided, genm-p44wire)

> **Claim (aligned).** At `L = 2`, for a front+row-aligned rank-`r` `B'`, the headline infimum
> `⨅ v ∈ optimalSet B', rlctAt (dlnLoss B') v = ofReal (aoyagiLambda H r)`, GIVEN the D1 reduction
> `hD1` for `B'`, the front-pivot frame `hJfront`, the top-row rank `htop`, and the R1 value `hcore`.
>
> - **Lean:** `DLNFibre.DLN.RLCT.headline_infimum_eq_aoyagiLambda_aligned`
>   (`lean/DLNFibre/DLN/RLCT/Validate/HeadlineL2InfimumWLOG.lean` @ HEAD)
> - **Gloss.** `hD1` (`⨅ = rlctAt deepest`) ▸ front-aligned #44 (`= nReg/2 + ofReal(lambdaCore)`) ▸
>   `reg_shift_add_core_eq_aoyagiLambda` (`= ofReal(aoyagiLambda)`).
> - **Proved.** the three-step chain unconditionally given the hyps; axiom-clean.
> - **Assumed.** `hJfront`, `htop`, `hpos`, `hLlt` (the front-aligned #44's hyps).
> - **Deferred.** `hD1` (D1 ≥-leg, genm-d1ladder), `hcore` (R1). Named hyps, not sorries.

> **Claim (arbitrary B).** At `L = 2`, for ANY rank-`r` `B`, the headline infimum `= ofReal
> (aoyagiLambda H r)`, GIVEN the aligned value for the WLOG-produced `B.submatrix R P`.
>
> - **Lean:** `DLNFibre.DLN.RLCT.headline_infimum_eq_aoyagiLambda`
>   (`lean/DLNFibre/DLN/RLCT/Validate/HeadlineL2InfimumWLOG.lean` @ HEAD)
> - **Gloss.** `headline_frontRowColPivot_exists` produces `P, R` + the infimum invariance
>   `⨅(B) = ⨅(B.submatrix R P)`; the aligned value (the hypothesis `haligned`, keyed to that exact
>   target) closes it. `aoyagiLambda` depends only on `(H,r)`, so no value transfer is needed.
> - **Proved.** the WLOG transport unconditionally; axiom-clean.
> - **Assumed.** `haligned` (the aligned-target value — discharged by the aligned lemma above, which
>   carries {D1, R1, front-pivot bridge}).
> - **Status.** both sorry-free, clean-three; reviewer fidelity check pending.
