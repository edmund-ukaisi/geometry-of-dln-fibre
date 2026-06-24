# Statement cards — thread 26 (H4 fibre-dimension count)

> **Claim (brick 2).** The coordinate ring of the rank-`≤ r` determinantal variety `Mat^{≤r}_{m×n}`
> has Krull dimension `δ = r(n + m − r)` (`k` alg-closed, char 0, `r ≤ n`, `r ≤ m`).
>
> - **Lean:** `DLNFibre.Core.ringKrullDim_quotient_vanishingIdeal_stratum_eq_delta`
>   (`lean/DLNFibre/Core/FibreDimFibration.lean` @ `3b9341d1`)
> - **Gloss.** `ringKrullDim (MvPolynomial (RepCoord (dStratum n m)) k ⧸ vanishingIdeal(canonicalCoord
>   '' productRankLocusLE (dStratum n m) r)) = (r*(n+m−r) : ℕ)`.
> - **Proved.** The genuine `WithBot ℕ∞` Krull dimension `= δ`, lifting the LANDED thermometer
>   `varietyDim = δ` (an `unbotD`-of-`ringKrullDim`) using primality (`ringKrullDim ≠ ⊥`).
> - **Assumed.** `[IsAlgClosed k] [CharZero k]`, `r ≤ n`, `r ≤ m` (the thermometer's scope).
> - **Cited.** none.
> - **Deferred.** none (this is the base dimension, complete).
> - **Status.** sorry-free, axiom-clean `[propext, Classical.choice, Quot.sound]`.

> **Claim (brick 3).** Every maximal ideal of the base ring `O(Mat^{≤r})` has height `δ`.
>
> - **Lean:** `DLNFibre.Core.height_maximal_quotient_vanishingIdeal_stratum_eq_delta`
>   (`lean/DLNFibre/Core/FibreDimFibration.lean` @ `3b9341d1`)
> - **Gloss.** for any maximal `𝔪` of `O(Mat^{≤r})`, `(𝔪.height : WithBot ℕ∞) = (r*(n+m−r) : ℕ)`.
> - **Proved.** equidimensionality at a closed point (`height_eq_ringKrullDim_of_isMaximal_fintype`) +
>   brick 2.
> - **Assumed.** `[IsAlgClosed k] [CharZero k]`, `r ≤ n`, `r ≤ m`.
> - **Cited.** none.
> - **Deferred.** none.
> - **Status.** sorry-free, axiom-clean.

> **Claim (the headline — NOT proved here).** `codimRepCanonical (mult⁻¹ E) = C + δ`.
>
> - **Lean:** — (not stated as a theorem; would overclaim).
> - **Proved.** `codim(fibre B) ≥ C` (LANDED `FibreCodim`); the base-side `+δ` dimension facts
>   (bricks 2,3); the descended comorphism (`sigmaQuotComap`); the H1 retarget.
> - **Deferred (the residual, certified TRUE pen-and-paper, thread 25).** the **easy** direction
>   `codim ≤ C+δ` (flatness-free via 00OM, ~3–5 further lemmas: a `Fintype`-indexed affine-domain
>   equidim, the nested catenary `height P = C + height(P/Q)`, the descended-to-component lies-over,
>   the 00OM application + `fibreGenIdeal ⊆ P`); the **hard** direction `codim ≥ C+δ` (the no-jump
>   residual — generic flatness, absent from Mathlib v4.29, or the multi-rung generic-smoothness
>   uniform-Jacobian-rank route B). The full identity is expedition-scale.
> - **Status.** the headline is **NOT** discharged; `DLN.BundleShiftInterface.cited_bundle_shift`
>   remains Cited. Nothing named claims otherwise.
