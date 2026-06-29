# Statement cards — thread 59 (smeared per-family, genm-smeared2)

The R1-LOWER boundary-SMEARED achiever box-divergence (#159). The genuinely-new algebraic core (the
projection cancellation that the rate `F = z²·U` rests on), banked sorry-free + axiom-clean.

---

> **Claim (the general projection cancellation).** For a (possibly TALL) `P₁ : rows × r` and a residual
> `P₂ : rows × s` with `col(P₂) ⊆ col(P₁)` in the factoring form `P₂ = P₁·K`, off the pole
> `det(P₁ᵀP₁) ≠ 0`, the normal-equations routing `Λ₀ = (P₁ᵀP₁)⁻¹·P₁ᵀ·P₂` satisfies `P₁·Λ₀ = P₂`.
>
> - **Lean:** `DLNFibre.DLN.RLCT.proj_cancel_of_factorsThrough`
>   (`lean/DLNFibre/DLN/RLCT/Validate/RouteMSmearedProjCancel.lean` @ `e1f7cde5`)
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
>   (`lean/DLNFibre/DLN/RLCT/Validate/RouteMSmearedFrontFactor.lean` @ `e1f7cde5`)
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
>   supplies `P = U·V` to these lemmas — `prodAux_split_exists` (banked) provides the `U·V` split; pinning
>   `det Vρ ≠ 0` from the bottleneck is the next wiring step.
> - **Route.** Numerically VERIFY-REAL'd (decorrelated): `K = Vρ⁻¹·Vσ` makes `P₂ = P₁·K` AND the proj
>   routing returns `P₂`, 0/40 fails on `r ≥ 2` tall cases.
> - **Status.** sorry-free, axiom-clean `[propext, Classical.choice, Quot.sound]`.
