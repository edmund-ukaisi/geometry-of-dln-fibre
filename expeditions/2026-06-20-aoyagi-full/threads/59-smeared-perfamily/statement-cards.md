# Statement cards — thread 59 (smeared per-family, genm-smeared2)

The R1-LOWER boundary-SMEARED achiever box-divergence (#159). The genuinely-new algebraic core (the
projection cancellation that the rate `F = z²·U` rests on) + the cast-free rate chain, banked
sorry-free + axiom-clean. Reviewer fidelity-PASS on the projection core (decorrelated + Codex xhigh,
in-Lean negative control). **The remaining gap is the opaque-width chart construction** (see the
"Reachable ceiling" section at the end) — the algebra and the routeMCore rate-from-collapsed-product
are bedrock; discharging the chart-eval hypothesis is the next (multi-tide) leg.

## Modules banked (@8576f861)

| module | theorems | role |
|---|---|---|
| `RouteMSmearedProjCancel` | `gram_routing_eq_factor`, `proj_cancel_of_factorsThrough` | general projection cancellation (any tall P₁) |
| `RouteMSmearedFrontFactor` | `front_factorsThrough_general`, `frontShear_cancel_general`, `prodAux_frontShear_cancel_general` | col(P₂)⊆col(P₁) bridge + the wired `prodAux` bottleneck bridge |
| `RouteMSmearedTelescope` | `telescope_collapse`, `frobeniusSq_smul`, `smeared_rate_of_cancel`, `frobeniusSq_nonneg` | abstract `F = z²·U` (cast-free) |
| `RouteMSmearedRateBridge` | `routeMCore_eq_frobeniusSq_prod`, `routeMCore_rate_of_prod_collapsed` | the `routeMCore` rate from a collapsed deep product |

All axiom-clean `[propext, Classical.choice, Quot.sound]`. NEED aggregator wiring (`DLNFibre.lean`,
single-writer — DEFERRED to the smeared leg-close per controller).

---

> **Claim (the general projection cancellation).** For a (possibly TALL) `P₁ : rows × r` and a residual
> `P₂ : rows × s` with `col(P₂) ⊆ col(P₁)` in the factoring form `P₂ = P₁·K`, off the pole
> `det(P₁ᵀP₁) ≠ 0`, the normal-equations routing `Λ₀ = (P₁ᵀP₁)⁻¹·P₁ᵀ·P₂` satisfies `P₁·Λ₀ = P₂`.
>
> - **Lean:** `DLNFibre.DLN.RLCT.proj_cancel_of_factorsThrough`
>   (`lean/DLNFibre/DLN/RLCT/Validate/RouteMSmearedProjCancel.lean` @ `8576f861`)
> - **Gloss.** If `P₂` factors through `P₁` (`P₂ = P₁·K`) and the `r×r` Gram is invertible, then
>   left-multiplying `P₂` by the projection `P₁(P₁ᵀP₁)⁻¹P₁ᵀ` returns `P₂` — because the routing
>   collapses to the factor (`Λ₀ = K`, helper `gram_routing_eq_factor`, via `Matrix.nonsing_inv_mul`).
> - **Proved.** The identity, unconditionally on `rows`/`s` (any `Fintype rows`, any `s`), for `r` a
>   `Fintype` with `DecidableEq`. Weakest hypotheses: only `P₂ = P₁·K` and `det(P₁ᵀP₁) ≠ 0` — no
>   left-invertibility of `P₁`, no rank-one / square restriction. In-file non-vacuity witness at a
>   genuinely-tall `P₁ = !![1;0;0]` (`3×1`).
> - **Assumed.** none (both hypotheses are explicit and load-bearing — negative control confirms).
> - **Cited.** none (`Matrix.nonsing_inv_mul` is core Mathlib, not an external interface).
> - **Deferred.** none for this lemma.
> - **Structure & ideas observed.** The honest content the `(2,3,1)` square `P₁` hid: a square invertible
>   `P₁` gives the FULL projection `P₁(P₁ᵀP₁)⁻¹P₁ᵀ = I` (fixes ANY `P₂`); a tall `P₁` gives the projection
>   onto `col(P₁)` only, so the identity is load-bearing on `col(P₂) ⊆ col(P₁)`. The clean route is the
>   FACTORING form `P₂ = P₁·K` (avoids the left-inverse), collapsing `Λ₀` to `K` in one step.
> - **Route.** VERIFY-REAL first (the κ_bare lesson, controller spec-gate): decorrelated sympy across all
>   26 tall-P₁ smeared `M` (5 shapes incl `3×2`), 0 fails; negative control (generic `P₂ ∉ col(P₁)`)
>   fails. Then build via `Matrix.nonsing_inv_mul`.
> - **Status.** sorry-free, axiom-clean `[propext, Classical.choice, Quot.sound]`.

---

> **Claim (the general-`r` front factoring + wired shear cancellation).** When the front product factors
> `P = U·V` (inner width `r`), the rank-block `P₁ = P[:,ρ]` and residual `P₂ = P[:,σ]` satisfy
> `col(P₂) ⊆ col(P₁)` off `{det Vρ ≠ 0}` (`Vρ` the selected `r×r` block of `V`); composing with the
> projection cancellation gives `P₁·Λ₀ = P₂` for ANY `r ≥ 1`.
>
> - **Lean:** `DLNFibre.DLN.RLCT.front_factorsThrough_general`,
>   `DLNFibre.DLN.RLCT.frontShear_cancel_general`
>   (`lean/DLNFibre/DLN/RLCT/Validate/RouteMSmearedFrontFactor.lean` @ `8576f861`)
> - **Gloss.** `front_factorsThrough_general`: from `P = U·V` and `det Vρ ≠ 0`, exhibit `K = Vρ⁻¹·Vσ`
>   with `P₂ = P₁·K`. `frontShear_cancel_general`: feed that `K` into `proj_cancel_of_factorsThrough`
>   (needs additionally `det(P₁ᵀP₁) ≠ 0`) to get `P₁·Λ₀ = P₂`.
> - **Proved.** Both, for general `r ≥ 1`. The `r = 1` case recovers `RouteMFrontBottleneck`'s rank-one
>   route as a special case (same `U·V` outer product).
> - **Assumed.** none beyond the two named poles `{det Vρ ≠ 0}` (factoring, `P₁` full column rank) and
>   `{det(P₁ᵀP₁) ≠ 0}` (projection) — both null sets; the box-divergence lower bound is unaffected.
> - **Cited.** none.
> - **Deferred.** The remaining smeared chart pieces are NOT in these lemmas (see thread status): the
>   opaque-width chart `phi_sm_M`, the rate `routeMCore (phi_sm_M u) = (u_p)²·U` (this is the lemma's
>   consumer), the rational `cov`, the `NodeAchieverChart` instance, and the headline
>   `routeMCore_box_diverges_smeared`. The structural fact that the smeared front product genuinely
>   factors through the width-`r` bottleneck layer (`certificate-genM-smeared.md` §1) is the bridge that
>   supplies `P = U·V` to these lemmas. `prodAux_frontShear_cancel_general` (below) DOES that wiring.
> - **Route.** Numerically VERIFY-REAL'd (decorrelated): `K = Vρ⁻¹·Vσ` makes `P₂ = P₁·K` AND the proj
>   routing returns `P₂`, 0/40 fails on `r ≥ 2` tall cases.
> - **Status.** sorry-free, axiom-clean `[propext, Classical.choice, Quot.sound]`.

---

> **Claim (the wired `prodAux` bottleneck bridge).** The smeared front product
> `P = prodAux M A (L−1)` splits at any earlier layer `p` (`prodAux_split_exists`, `P = U·Y`); with the
> bottleneck block `Y∘ρ` invertible and the Gram off its pole, `P₁·Λ₀ = P₂`.
>
> - **Lean:** `DLNFibre.DLN.RLCT.prodAux_frontShear_cancel_general`
>   (`lean/DLNFibre/DLN/RLCT/Validate/RouteMSmearedFrontFactor.lean` @ `8576f861`)
> - **Gloss.** Instantiates `frontShear_cancel_general` with `U = prodAux M A p`, `V = Y` from the prefix
>   split, for column selectors `ρ`/`σ` into the deepest width `Fin (M⟨k⟩)`. The general-`r` analog of
>   `RouteMFrontBottleneck`'s `prodAux_frontScalarShear_cancel` (which is the `M⟨p⟩ = 1` rank-one case).
> - **Proved.** The cancellation, for any split point `p ≤ k = L−1`, any selectors, off the two poles.
> - **Assumed.** `hVρ` (the bottleneck block `Y∘ρ` invertible, off its null pole) + `det(P₁ᵀP₁) ≠ 0`,
>   both as named hypotheses — the chart supplies them at the width-`r` bottleneck layer (where
>   `M⟨p⟩ = r`, the front-bottleneck `= r` structural fact, `certificate-genM-smeared.md` §1).
> - **Cited.** none. **Deferred.** the chart that picks `p` = the bottleneck + discharges `hVρ`.
> - **Status.** sorry-free, axiom-clean `[propext, Classical.choice, Quot.sound]`.

---

> **Claim (the cast-free `F = z²·U` rate).** Given the shear cancellation `P₁·Λ₀ = P₂`, the
> square-Frobenius loss of the shear-absorbed deep product collapses: `∑ᵢⱼ Dᵢⱼ² = z²·‖P₁·H̄‖²_F`, with
> `D = P₁·(z·H̄ − Λ₀·S_bot) + P₂·S_bot`; and the `routeMCore` rate `routeMCore M (φ u) = z²·‖X‖²` from a
> collapsed product `prod M (chart) = z·X`.
>
> - **Lean:** `DLNFibre.DLN.RLCT.telescope_collapse`, `smeared_rate_of_cancel`
>   (`…/RouteMSmearedTelescope.lean`); `routeMCore_eq_frobeniusSq_prod`,
>   `routeMCore_rate_of_prod_collapsed` (`…/RouteMSmearedRateBridge.lean`) @ `8576f861`
> - **Gloss.** `telescope_collapse`: `P₁·Λ₀ = P₂ ⟹ D = z•(P₁·H̄)` (the `S_bot` term cancels).
>   `smeared_rate_of_cancel`: `∑ᵢⱼ Dᵢⱼ² = z²·∑ᵢⱼ(P₁H̄)ᵢⱼ²`. `routeMCore_eq_frobeniusSq_prod`:
>   `routeMCore M x = ∑ᵢⱼ (prod M (symm x))ᵢⱼ²`. `routeMCore_rate_of_prod_collapsed`:
>   `prod M (symm (φ u)) = z•X ⟹ routeMCore M (φ u) = z²·∑ᵢⱼ Xᵢⱼ²`.
> - **Proved.** All four, cast-free over abstract matrices (`telescope`) and at the genuine `routeMCore`
>   loss level (`rate bridge`). `U = ‖P₁·H̄‖²_F` is `≥ 0` (`frobeniusSq_nonneg`) and `z`-free (`Λ₀`
>   cancels) — a genuine polynomial, riding the existing polynomial-zero-set `Ubound` route.
> - **Assumed.** the cancellation `P₁·Λ₀ = P₂` (supplied by `prodAux_frontShear_cancel_general`) and the
>   chart-eval `prod M (chart) = z·X` (the named gap — see "Reachable ceiling").
> - **Cited.** none. **Deferred.** the chart-eval `prod M (chart) = z·(P₁·H̄)` (the opaque-width chart).
> - **Route.** Codex (`scope-answer` §2): state the rate over abstract matrices, push the dependent-`Fin`
>   casts into the chart bridge only — this is that abstraction.
> - **Status.** sorry-free, axiom-clean `[propext, Classical.choice, Quot.sound]`.

---

## Reachable ceiling (this tide) + the named gap

**Banked bedrock (this tide):** the complete cast-free **algebra + rate chain** for the smeared rate
`F = z²·U`, 9 theorems across 4 modules, all sorry-free + axiom-clean, projection core reviewer-PASS:

    prodAux_split_exists (banked)
      → prodAux_frontShear_cancel_general   (P₁·Λ₀ = P₂, the shear cancellation, general r)
        → frontShear_cancel_general → proj_cancel_of_factorsThrough
    telescope_collapse (P₁·Λ₀=P₂ ⟹ D = z•(P₁H̄)) → smeared_rate_of_cancel (∑Dᵢⱼ² = z²·‖P₁H̄‖²)
    routeMCore_eq_frobeniusSq_prod → routeMCore_rate_of_prod_collapsed (the routeMCore rate)

**The one named gap (the next leg, multi-tide, [HIGH] cast-risk):** the **opaque-width chart-eval**

    prod M ((paramsEquivFlat M).symm (phi_sm_M u)) = (u p) • (P₁ · H̄)

i.e. construct `phi_sm_M = (radial pivotBlowupOn = R) ∘ (the Λ₀-shear = ψ, banked
`measurePreserving_shearM`) + the opaque-width pack/reshape, and show the deepest product collapses to
the pure radial. This is the dependent-`Fin` block-split of the deepest factor into `Fin r ⊕ Fin s` rows
(the [HIGH] cast). Once discharged, `routeMCore_rate_of_prod_collapsed` gives the rate immediately, and
the headline `routeMCore_box_diverges_smeared` follows by the banked contract
`routeMCore_box_diverges_smearedContract` (ψ MP-embedding via `measurePreserving_shearM` + R radial +
the weighted divergence — the `(2,3,1)` `routeM231sm_box_diverges` is the concrete template, 1125 lines
for the single instance). The chart's rational `cov` (det `|z|^{minAdm−1}` off the `{det P₁ᵀP₁ = 0}` null
pole) is the other piece, via `S1.1 weightedThreshold_transport` (cited).

**Why stop here (not a spike):** the chart-eval is genuine new opaque-width cast work, not algebra. Banked
is the hole-free interior (everything provable from the abstract pieces); the boundary (the chart) is named,
not papered over with a `sorry`. The rate consumer (`routeMCore_rate_of_prod_collapsed`) takes the chart-eval
as an explicit hypothesis, so there is no `sorry` anywhere — the gap is an honest interface, dispatchable.
