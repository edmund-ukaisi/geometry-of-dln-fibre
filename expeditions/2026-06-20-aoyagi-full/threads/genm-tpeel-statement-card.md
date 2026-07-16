# Statement card — G1, the T-peel: box → ∑-shell decomposition (arity ≥ 4)

First step of the arity≥4 (3a) discharge of (□), thread `genm-tpeel` (off `genm-3abase @00a47fd03`).
Chain: **G1 (box ≤ ∑ shellSpine)** → LINK (`shellSpine_le_frontCharge_binding`, landed @00a47fd03)
→ G2 (∫ front-charge < ⊤) ⟹ box < ⊤ = (□) for arity ≥ 4.

> **Claim.** For a chain `M : Fin (L+1+1+1) → ℕ` (arity ≥ 3, i.e. `L ≥ 0`), a base cut `t` with
> `1 ≤ t ≤ min(M₀,M₁)`, a threshold `ε`, and an exponent `c'`, the full-chain layer-product box loss
> integral `routeMLayerBoxIntegral M c' 1` is bounded by the finite sum, over singular-value shells
> `j ≤ r = min(M₀−t, M₁−t)` and pivot charts `(ρ, κ)` at the deeper cut `u = t+j`, of the
> shell-`j`-restricted cut-`u` spine integrand `shellSpineIntegrand M (t+j) κ ε r j c'`.
>
> - **Lean:** `DLNFibre.DLN.RLCT.routeMLayerBox_le_sum_shellSpine`
>   (`lean/DLNFibre/DLN/RLCT/Validate/RouteMSJTPeel.lean` @ `d4c356011`, on `origin/genm-tpeel`).
>   Supporting: `ae_rank_ge` (determinantal co-null), `frontBox_pivotCover_le_gen` (general-`u`
>   product-level pivot cover), `chartBox_eq_freedInner` (ρ-generic chart = freed-inner equality).
> - **Gloss.** `routeMLayerBoxIntegral M c' 1 ≤ ∑ (j : Fin (min(M₀−t,M₁−t)+1)), ∑ (ρ : Fin (t+j) ↪ Fin M₀),
>   ∑ (κ : Fin (t+j) ↪ Fin M₁), shellSpineIntegrand M (t+j) κ ε (min(M₀−t,M₁−t)) j c'`. The shell index
>   `jf = j : Fin (r+1)`, the cut `u = t+↑j`, and the embedding `κ : Fin (t+↑j) ↪ Fin M₁` match the landed
>   LINK's arguments verbatim (`⟨↑j, _⟩ = j` by `Fin.eta`), so G1 + LINK + G2 compose per `(j,κ)`.
> - **Proved.** The full inequality, unconditionally in `ε`, `c'` (no threshold/positivity hypotheses on the
>   integrand). Axiom-clean `[propext, Classical.choice, Quot.sound]` (native — no `sorryAx`, no
>   `cited_aoyagi_dln`). Ladder: (1) `routeMLayerBoxIntegral_front_split` (banked) → tail-outer / front-inner
>   iterated integral; (2) singular-value shell cover of the tail parameter `A'` (`lintegral_le_sum_finCover`
>   + `singularShell_iUnion`); (3) per shell, product-level pivot-chart cover at cut `u = t+j`
>   (`frontBox_pivotCover_le_gen`), whose co-null step is the determinantal null fact `matBox ∩ {rank A₀ < u}`
>   null (`ae_rank_ge`, `u ≤ min(M₀,M₁)` from `ht`); (4) each chart integral = freed inner
>   (`chartBox_eq_freedInner`), reassembling to `shellSpineIntegrand` via `setLIntegral_prod_symm` + a
>   per-`A'` `lintegral_congr`.
> - **Assumed (named hypotheses).** `ht : t ≤ min(M₀,M₁)` and `ht1 : 1 ≤ t` — the base cut is a legal,
>   nonzero binding cut. `ht` gives `u = t+j ≤ min(M₀,M₁)` for every shell `j ≤ r` (so the low-rank front
>   locus is a proper determinantal — hence null — set); `ht1` gives `u ≥ 1` (the cover's `1 ≤ u`). Both are
>   present downstream (the LINK and `deeperFlag_shell_le` carry `ht1`; `htb : t+1 ≤ min` there implies `ht`).
> - **Cited.** none.
> - **Deferred.** none for G1 itself. The next rungs are separate: the LINK (landed) bounds each
>   `shellSpineIntegrand ≤ ∫ front-charge` (per `(j,κ)`, with two a.e.-genericity hypotheses discharged at a
>   binding cut); G2 (`∫ front-charge < ⊤`) is the remaining unbuilt piece. G1 does NOT assert finiteness —
>   it is the measure-theoretic decomposition only.
> - **Structure & ideas observed.** The direction `box ≤ ∑ shellSpine` runs OPPOSITE to the banked
>   `shellSpine_inner_le_matBox` (which drops the pivot chart, giving a SINGLE freed-inner ≤ box). The right
>   fact is the EQUALITY buried inside that proof (`freed(κ) = ∫_{matBox ∩ pivotChart ρ κ}`, ρ-free) combined
>   with subadditivity over the CO-NULL cut-`u` pivot-chart cover — extract the equality, do not invert the
>   monotone drop. The over-counting that makes `≤` (not `≥`) hold is the pivot-chart cover's `∑` over `(ρ,κ)`
>   (the summand is ρ-free, so the ρ-sum is `#ρ ·` the κ-sum — an honest, finite over-estimate). Box↔shell
>   wiring + the exact RHS index set adjudicated with `arch1build` (holds the chain-map, built the LINK).
> - **Route (formaliser).** New module `RouteMSJTPeel.lean` reusing banked plumbing: `routeMLayerBoxIntegral_
>   front_split`, `lintegral_le_sum_finCover` + `singularShell_iUnion`, `pivotLocus_eq_iUnion`,
>   `measurable_frontIntegrand`, `setLIntegral_prod_symm`, and the internal `key` of `shellSpine_inner_le_matBox`
>   (re-proved ρ-generic). The one genuinely-new sub-lemma is `ae_rank_ge` (determinantal a.e.-full-rank),
>   reusing the a.e.-nonzero-polynomial engine `ae_matrix_eval_ne_zero` (parallels `corank_survival_ae`,
>   simpler — no deep factor). ~200 lines.
> - **Status.** sorry-free + reviewed (fidelity SURVIVED all 5 checks; kernel-verified verbatim
>   composition with the LINK `box ≤ ∑ shellSpine ≤ ∑ frontCharge`; decorrelated Codex-confirmed).

## Fidelity note (why the RHS sums over `(ρ, κ)`, not just `j`)

The LINK is stated `∀ κ` for a single `κ : Fin (t+j) ↪ Fin M₁`; G1 supplies a whole `∑_{ρ,κ}`. The compose is
`box ≤ ∑_j ∑_{ρ,κ} shellSpine(κ) ≤ ∑_j ∑_{ρ,κ} (LINK RHS) < ⊤` (a finite sum of finite terms is finite). The
`∑_ρ` is redundant at the level of value (each summand is ρ-free) but is exactly what the pivot-chart cover
`pivotLocus_eq_iUnion u : {u ≤ rank} = ⋃_{ρ,κ} pivotChart ρ κ` produces — the low-rank front factors
(`rank A₀ < u`, positive-measure only if `u > min(M₀,M₁)`) are excluded as a determinantal null set, valid
because `u = t+j ≤ min(M₀,M₁)`.
