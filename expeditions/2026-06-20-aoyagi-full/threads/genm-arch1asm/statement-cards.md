# genm-arch1asm — statement cards

Tide `genm-arch1asm`, branched off `origin/genm-arch1build @6e0ee0f31` (base build GREEN, 8406 jobs).
Target: the arity-3 (L=0) ANCHOR of `deeperFlag_shell_le` — reassembly of `∫_p frontChargeIntegrand` onto
`cornerComparator (u, M₂) ![1] ![u·M₂−1] .integral(q)` (reassembly-cert §3.1, commit `a25091d35`).

> **STOOD DOWN (controller re-scoping, 2026-07-16).** The arity-3 (□) is ALREADY BANKED on canonical:
> `routeMBoxThresholdFinite_mnp (m n p) : RouteMBoxThresholdFinite (![m,n,p])` (RouteMSchurRectCapB.lean:453,
> via the rectangular Schur core, NOT the charge form; AxCheck clean-three). The mint consumes
> `RouteMBoxThresholdFinite` DIRECTLY (`RouteMSJMint.aoyagi_learning_coefficient_gen`), and
> `shellSpineIntegrand_le_layerBox` (banked) + `routeMBoxThresholdFinite_mnp` give the shell-restricted
> finiteness trivially (shell ⊆ box, nonneg integrand). So **the charge-form recursion base built here is
> REDUNDANT** — the architecture is direct, no charge-form base needed. The two cards below are clean,
> general-`L`, sorry-free computations of `cornerComparator.integral`, but they serve the
> `DecoratedDescent`/comparator route (L≥1-unsound per the re-scoping), so their reusability is LIMITED.
> Banked here for preservation, not on the live arity≥4 path (which is the (3a) deep-stratum gate). No
> general matrix-space CoV / spectral lemma was landed — the coupled resolution was HELD, never entered.

Module: `lean/DLNFibre/DLN/RLCT/Validate/RouteMSJArity3Anchor.lean` (NOT wired into the aggregator —
controller wires). Uncommitted on the tide-branch working tree pending controller integration; SHA pins to
the base `6e0ee0f31` until committed.

---

## Card 1 — `cornerComparator_integral_eq` (piece (6) RHS, LANDED)

> **Claim.** The reduced comparator's decorated box integral, at the single-radial choice `k ≡ ![1]`,
> `jac = ![jc]`, is the double integral over the reduced params `z` (box `paramsBoxM M' 1`) and the radial
> coordinate `u₀ ∈ [0,1]` (`unitBox 1`) of `|u₀|^{jc} · (|u₀|² · frobSq (prod M' z))^{−q}`.
>
> - **Lean:** `DLNFibre.DLN.RLCT.cornerComparator_integral_eq`
>   (`lean/DLNFibre/DLN/RLCT/Validate/RouteMSJArity3Anchor.lean` @ `6e0ee0f31` + tide diff)
> - **Signature.**
>   ```
>   theorem cornerComparator_integral_eq (M' : Fin (L + 1 + 1) → ℕ) (jc : ℕ) (q : ℝ)
>       (i₀ : Fin (M' 0) × Fin (M' (Fin.last (L + 1)))) :
>       (cornerComparator M' ![1] ![jc]).integral q
>         = ∫⁻ z in paramsBoxM M' 1, ∫⁻ u in unitBox 1,
>             ENNReal.ofReal (|u 0| ^ jc * (|u 0| ^ 2 * frobSq (prod M' z)) ^ (-q))
>   ```
> - **Gloss.** Unfolds `SJDecoration.integral` for the corner comparator, substitutes
>   `cornerComparator_decLoss` (loss `= commonDivisor² · frobSq (prod M')`) and the uniform-support common
>   divisor `commonDivisor (≡![1]) u = |u 0|`, and collapses the `Fin 1` Jacobian product
>   `∏ ℓ, |u ℓ|^{![jc] ℓ} = |u 0|^{jc}`. This is the exact RHS shape piece (6) reassembles onto.
> - **Proved.** The exact equality (no side conditions beyond an inhabited endpoint index `i₀`).
> - **Assumed.** `i₀` (a generator index — the comparator's `ι` is inhabited).
> - **Cited.** none.
> - **Deferred.** none (this card is the comparator-side computation only; the reassembly BOUND is HELD).
> - **Status.** sorry-free, axiom-clean `[propext, Classical.choice, Quot.sound]` (forced `#print axioms`).

## Card 2 — `cornerComparator_integral_eq_single` (piece (6) RHS, single-exponent form, LANDED)

> **Claim.** The same integral in the cert §1 SINGLE-exponent form: `|v₀|^{jc}` and the `|v₀|²` inside the
> loss combine (a.e. off the null slice `v₀ = 0`) into one radial monomial `|v₀|^{jc − 2q}` times the honest
> reduced-product loss `frobSq(prod M')^{−q}`.
>
> - **Lean:** `DLNFibre.DLN.RLCT.cornerComparator_integral_eq_single`
>   (`lean/DLNFibre/DLN/RLCT/Validate/RouteMSJArity3Anchor.lean` @ `6e0ee0f31` + tide diff)
> - **Signature.**
>   ```
>   theorem cornerComparator_integral_eq_single (M' : Fin (L + 1 + 1) → ℕ) (jc : ℕ) (q : ℝ)
>       (i₀ : Fin (M' 0) × Fin (M' (Fin.last (L + 1)))) :
>       (cornerComparator M' ![1] ![jc]).integral q
>         = ∫⁻ z in paramsBoxM M' 1, ∫⁻ u in unitBox 1,
>             ENNReal.ofReal (|u 0| ^ ((jc : ℝ) - 2 * q) * frobSq (prod M' z) ^ (-q))
>   ```
> - **Gloss.** The cert §1 `|v₀|^{minAdm(M')−1−2q}` shape (at `jc = minAdm(M')−1`): the `v₀`-radial
>   converges iff `jc − 2q > −1`, i.e. `q < (jc+1)/2 = carrierThreshold M'` — the clean IH threshold. The
>   power combination `|v₀|^{jc}·(|v₀|²·F)^{−q} = |v₀|^{jc−2q}·F^{−q}` is `Real.rpow_add` on `|v₀| > 0`; the
>   origin `v₀ = 0` is a `volume`-null singleton of `unitBox 1`, dropped by `lintegral_congr_ae`.
> - **Proved.** The exact equality (a.e. combination, origin null).
> - **Assumed.** `i₀`.
> - **Cited.** none.
> - **Deferred.** none.
> - **Status.** sorry-free, axiom-clean `[propext, Classical.choice, Quot.sound]` (forced `#print axioms`).

---

## HELD — the coupled incidence-chart resolution (the anchor's core, pieces (2)/(3')/(5)/(6))

> **Obligation (the anchor GOAL, TRUE for L=0 per reassembly-cert §Verdict A, 332/332 in-scope cuts).** For
> `M : Fin (0+1+1+1)`, `u ≤ min(M₀,M₁)`, scope `(M₀−u)+(M₁−u) ≤ M₂`, and `c' < carrierThreshold M`:
>
>     ∫_p frontChargeIntegrand M u c' p < ⊤     (p ∈ paramsBoxM (redChain u M) 1 ×ˢ matBox (M₁−u) M₂ 1),
>
> equivalently (piece 6) `≤ K · cornerComparator (redChain u M) ![1] ![minAdm(redChain u M)−1] .integral(c'−ab/2)`
> with `K < ⊤` (`K ~ 1/(T1−c')`).
>
> - **Proof route.** The coupled `(A'₀, A_cor, x)`-integral change-of-variables (the [pending] steps 3/4/5
>   of `RouteMSJIncidenceAssembly`). At L=0, `deeperFlagZdeep M u = I_{M₂}`, so `Q_b = A_cor` free,
>   `Q_p = A'₀`.
> - **(2) A_cor b-minor CoV atlas + shear chain** — charge `det_chartGram` → `Q_p`-shear `W = Q_p·N` →
>   front `B`-shear → `H̃`-completion; net `|det D|^{M₂−b−a−u}`, integrable ⟺ `a+b ≤ M₂`. BANKED core:
>   `detGram_lintegral_box_lt_top`, `strongBlock_lintegral_lt_top`, `det_chartGram`, `transverseSchurGram`,
>   `lintegral_comp_mulLeftₚ`, `chart5_bigcell_cov`. OPEN: the connective CoV chain resolving the coupled
>   front loss (the largest piece).
> - **(3') ℓ=0 two-block corner** — `twoBlock_radial_le` BANKED. OPEN + HIGH-FRICTION: the SVD spectral
>   bound `‖YW‖² ≥ (‖W‖²/min(u,d))·‖Y e₁‖²` (top singular value/vector of W). **NEEDS A SPECTRAL SPECIALIST.**
> - **(5) finite-cover gluing** — `lintegral_lt_top_of_finite_cover` / `_finset_cover` BANKED. OPEN: the
>   atlas-specific `(ℓ,s,b-minor)` coverage-up-to-null.
> - **(6) reassembly onto comparator** — RHS computed by Cards 1/2 above; per-stratum radial finiteness
>   BANKED (`single_block_stratum_lt_top` / `stratum_corner_lt_top`); descent gate `minAdm_le_ab_add_uM2`
>   BANKED. OPEN: the top-level assembly (depends on (2),(3'),(5)).
> - **Status.** HELD — a coupled multi-tide CoV mountain (the analytic core of the arity-3 anchor). Not
>   stated as a Lean `sorry` (kept off the module to leave Cards 1/2 integration-ready / sorry-free); the
>   exact obligation + hypotheses are pinned above.
