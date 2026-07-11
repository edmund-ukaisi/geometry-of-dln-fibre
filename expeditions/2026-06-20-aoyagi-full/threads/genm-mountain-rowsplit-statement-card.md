# Statement card — `gammaPeelIntegral_rowSplit_eq` (mountain gap 1, transport a+b)

> **Claim.** `gammaPeelIntegral M t ρ κ c'` (the per-cut peel integral of the (S,J) CoV mountain)
> equals the same nested integral with the leading tail layer's rows *split*, by the pivot embedding
> `κ`, into its `t` κ-pivot rows and its `M₁−t` corank rows, the front factor reassembled as
> `Matrix.of (Sum.elim (pivot rows) (corank rows))`.
>
> - **Lean:** `DLNFibre.DLN.RLCT.gammaPeelIntegral_rowSplit_eq`
>   (`lean/DLNFibre/DLN/RLCT/Validate/RouteMSJRowSplitCompose.lean`, new untracked module — pending
>   bank; built against `expedition/aoyagi-full` @ `7be169da`)
> - **Gloss.** For a dimension vector `M : Fin (L+3) → ℕ`, a cut size `t`, and pivot embeddings
>   `ρ : Fin t ↪ Fin (M 0)`, `κ : Fin t ↪ Fin (M 1)`, and any real exponent `c'`:
>   `gammaPeelIntegral M t ρ κ c'` equals the integral over `q` in the product box
>   `(matBox t M₂ 1 ×ˢ matBox (M₁−t) M₂ 1) ×ˢ D` — `q.1.1` the pivot-row block `t × M₂`, `q.1.2` the
>   corank-row block `(M₁−t) × M₂`, `q.2` the deeper layers in the `[−1,1]` box `D` — then over the
>   outer domain `x ∈ outerDom t (M₀−t) (M₁−t) 1`, then over the shear-image box for `Γ`, of
>   `ENNReal.ofReal ((sjGoodChartLoss x Γ (Matrix.of (Sum.elim q.1.1 q.1.2)) (sjDeepFactorCore M q.2))^(−c'))`.
>   Here `M₁ = tailChain M (0.castSucc)`, `M₂ = tailChain M (0.succ)`.
> - **Proved.** The equality, unconditionally (no hypotheses beyond the pivot embeddings the integrand
>   already carries; no finiteness, no invertibility). Composes the banked entry point
>   `gammaPeelIntegral_piSplit_eq` (step a) with the banked measure-preserving row split
>   `rowSplitEquiv κ` (step b), lifted over the deeper factor by `MeasurableEquiv.prodCongr` and
>   transported by `setLIntegral_comp_preimage_emb` — no integrand measurability required (the transport
>   is measure-preserving). Axiom footprint `[propext, Classical.choice, Quot.sound]` (forced
>   `#print axioms`, olean deleted first). Sorry-free.
> - **Assumed.** none (the good-chart shear `(of x.1.1)⁻¹` sits inside `sjGoodChartLoss`; the pivot `P`
>   is constrained to a unit only inside `outerDom`, and this identity does not read that).
> - **Cited.** none.
> - **Deferred.** The v-exposure (transport step c, `sjGoodChartLoss_pivotRows_translate_eq`): exposing
>   the pivot rows `Upiv` as the free boundary variable `v = Upiv + P⁻¹B₁₂W` over the shifted box
>   `{v | v − P⁻¹B₁₂W ∈ matBox}`. Step (c) requires `Upiv` innermost, which requires a Tonelli reorder
>   past `W, deeper, x, Γ`. That reorder is a genuine Fubini swap whose side-conditions need joint
>   measurability of the pre-translation integrand — which carries the matrix inverse `(of x.1.1)⁻¹` —
>   NOT banked. It is a separate measurability rung, not part of this identity.
> - **Route.** (controller-attributed, from the mountain recon-map §3 gap 1 + the `RouteMSJTransport`
>   docstring C3.) Compose the banked row-split atom onto `gammaPeelIntegral_piSplit_eq`. Landed via the
>   product-lifted measure-preserving transport rather than a Tonelli split (avoids all integrand
>   measurability): `e := (rowSplitEquiv κ n).prodCongr (refl deeper)`,
>   `MeasurePreserving.prod`, `setLIntegral_comp_preimage_emb`, box factorization
>   `rowSplitEquiv_preimage_box`, integrand match by `rowSplitEquiv_reindex`.
> - **Status.** sorry-free (fidelity review pending).

## Note on the target ambiguity (surfaced for the controller)

The task spec asked for the *v-exposed* 5-fold form (steps a+b+**c**). The `RouteMSJTransport` docstring,
by contrast, names `gammaPeelIntegral_rowSplit_eq` as the *row-split* form (a+b only), with step (c)
"remaining". I delivered the a+b form under that name (name = content: "rowSplit" = the row split, not
the v-exposure), because step (c) is **not** the pure-plumbing composition the spec assumed: it requires
a Fubini reorder whose measurability side-conditions carry the matrix inverse and are unbanked. That is a
distinct measurability build (est. matrix-inverse global measurability + joint integrand measurability +
a 4-swap Tonelli reorder), recommended as its own scoped rung. The a+b identity here is the prerequisite
the reorder + step (c) will consume.
