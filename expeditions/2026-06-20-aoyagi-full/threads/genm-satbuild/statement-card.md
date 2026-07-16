# Statement card — `genm-satbuild` (j=r saturated shell brick, a=0)

The saturated boundary hole of the arity-≥4 `(□)` closure: the `hbdryShell` slot at `j = r` of
`RouteMSJArity4Assembly`'s coupled-incidence assembly. Design cert: `genm-satred/satred-cert.md`
(satred, with the §4 `A > 2Δ` correction @ `571214cbc`). Interface confirmed with `arch1build`.

> **Claim.** At the saturated shell `j = r = min(M₀−t, M₁−t)` with `M₀ ≤ M₁` (so the cut `u = t + ↑j`
> gives `a = M₀ − u = 0`), the shell-spine integrand is finite, given the arity induction hypothesis
> `RouteMBoxThresholdFinite (redChain (t+↑j) M)` and the matrix-product pushforward-density domination.
>
> - **Lean:** `DLNFibre.DLN.RLCT.saturatedShell_lt_top`
>   (`lean/DLNFibre/DLN/RLCT/Validate/RouteMSJSaturatedShell.lean` @ `e7f715bcb`)
>   — supporting: `freedSchurLoss_of_isEmpty_a`, `satFrontIntegrand`, `shellSpine_le_satFront`.
> - **Gloss.** For a `≥ 4`-width chain `M`, cut `t`, saturated shell `j` (`↑j = min(M₀−t, M₁−t)`),
>   pivot embedding `κ`, floor `ε`, exponent `c'`, with `M₀ ≤ M₁`: if the reduced (one-shorter) chain
>   `redChain (t+↑j) M` has finite box integral below its threshold `½·minAdm`, AND there exist an
>   exponent `q < ½·minAdm(redChain (t+↑j) M)` and a finite `K` with
>   `satFrontIntegrand ≤ K · routeMLayerBoxIntegral (redChain (t+↑j) M) q 1`, THEN
>   `shellSpineIntegrand M (t+↑j) κ ε (min(M₀−t, M₁−t)) j c' < ⊤`.
> - **Proved.** (sorry-free, axiom-clean `[propext, Classical.choice, Quot.sound]`, NO `sorryAx`, NO
>   `cited_aoyagi_dln`):
>   - `freedSchurLoss_of_isEmpty_a` — at `a = 0` (`IsEmpty (Fin a)`) the second (corank-energy) `frobSq`
>     is a sum over empty rows, so it vanishes and `freedSchurLoss` equals its first (pivot-energy) term
>     `frobSq(P·(Q_inl + P⁻¹·B₁₂·Q_inr))`, independent of the freed block `Γ`.
>   - `shellSpine_le_satFront` — the a=0 collapse: the `∫⁻ Γ` runs over the empty-domain space
>     `Fin (M₀−u) → Fin (M₁−u) → ℝ`, which is a singleton with `volume = dirac`
>     (`Measure.volume_pi_eq_dirac`), hence a probability measure (mass `≤ 1`); the (now Γ-independent)
>     integrand pulls out and `shellSpineIntegrand ≤ satFrontIntegrand`.
>   - `saturatedShell_lt_top` — the reduction skeleton: `a = 0` from `hjeq + hab` by `omega`; then
>     `shellSpine ≤ satFront ≤ K·box(redChain) q < ⊤`, the box finite by `hIH` at `q`.
> - **Assumed (named hypotheses in the statement).**
>   - `hIH : RouteMBoxThresholdFinite (redChain (t+↑j) M)` — the arity induction hypothesis, threaded by
>     the capstone (`sjStepHyp_of_coupled` supplies `∀ M', RMBTF M'`); banked/wrapper content.
>   - `hdensity` (existential) — the genuinely-new analytic content: the fused
>     `(P, B₁₂, A₀, z_deep) ↦ (z̃₀ = [P|B₁₂]·A₀, z_deep)` change-of-variables domination. Carried as a
>     hypothesis (like `hG1`/`hfin` in the capstone), NOT a `sorry`.
>   - `hab : M₀ ≤ M₁` — the a=0 case gate (the transpose `M₁ < M₀` mirror, `b = 0`, is a separate brick).
> - **Cited.** none in this module. (`hdensity`'s eventual discharge rests on the DLN pushforward-density
>   analysis, satred's cert; the finiteness value `λ_H = ½·minAdm M` is Aoyagi-consistent but is NOT
>   re-derived here — this brick works at the per-shell finiteness level, not the RLCT equality.)
> - **Deferred.** The discharge of `hdensity` (proving it sorry-free, removing it from the hypothesis
>   list). It is always TRUE for `c' < ½·minAdm M` (finiteness holds unconditionally), so the reduction
>   is sound; the PROOF splits by `A = max_{1≤j≤min(u,M₂)} j(M₂−b−j)` vs `2Δ = minAdm(redChain u M) − minAdm M`:
>   - `A ≤ 2Δ` (sufficient `b ≥ M₂−1`, bounded/log density): the clean bounded/log measure-domination,
>     folds at `q = c' + ε`. Tractable — the "b≥M₂ first" target.
>   - `A > 2Δ` (small `b`, incl. the `b = 0` corner `M₀ = M₁` this brick covers): the naive pointwise
>     `‖z̃₀‖^{−A}` fold undershoots; needs the joint determinantal rank-sector resolution (hard). Open.
>   Also deferred: the `b = 0` MIRROR `M₁ < M₀` (separate transpose brick; `RouteMBoxThresholdFinite` is
>   proved for arbitrary unsorted `M`, so the mirror genuinely arises).
> - **Structure & ideas observed (satred).** `u + b = M₁` at saturation makes the leading layer the
>   matrix PRODUCT `z̃₀ = [P|B₁₂]·A₀` (X·Y, X full row rank `M₀`); `det P → 0` is compensated by the
>   corank cross-block `B₁₂`, so NO RLCT drop (`λ_H = ½·minAdm M`). The naive per-`P` Jacobian
>   `|det P|^{−M₂}` is a domain-enlargement artifact — do NOT use it. `Cresid(0) = 1` and the second
>   `frobSq` vanishing are the a=0 collapse; `Cresid` does NOT appear in `shellSpineIntegrand` (it lives
>   downstream in `frontChargeIntegrand`).
> - **Route (satbuild, confirmed with arch1build).** (b) — bundle the whole pushforward into `hdensity`
>   (nothing banked does the reverse two-full-layer reconstruction); prove the a=0 collapse natively
>   (`IsEmpty (Fin (M₀−u))` avoids dependent-type rewrites); consume `hIH` at the shifted exponent. The
>   capstone's post-re-route `hbdryShell` is `j = r` only = this conclusion verbatim (wires by `exact`).
> - **Status.** sorry-free (awaiting fidelity review).
