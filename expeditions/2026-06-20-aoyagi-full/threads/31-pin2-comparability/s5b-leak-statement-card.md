# Statement card — S5b leak: the eventual Schur-leak bound (`hproducer` conjunct (c), thread 31)

> **Claim.** Near the deepest point `w0 := paramsEquivFlat (deepestPoint …)`, for the conjugated
> residual `M w := reindex e₁ e₂ (P0·(prod((paramsEquivFlat).symm w) − B)·QL)` with producer blocks
> `P00 := M.toBlocks₁₁ + 1`, `P01 := M.toBlocks₁₂`, `P10 := M.toBlocks₂₁`, the Schur leak
> `P10·(P00)⁻¹·P01` has squared-Frobenius energy `≤ 1²·Sreg` on a neighborhood of `w0`, where
> `Sreg := (frobSq M₁₁ + frobSq M₁₂) + frobSq M₂₁` (= `(∑(P00−1)² + ∑P01²) + ∑P10²`).
>
> - **Lean:** `DLNFibre.DLN.RLCT.eventually_leak` (`private`)
>   (`lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeConstruction.lean`, @ uncommitted — controller to
>   integrate; base merge `55193c4e`).
>
> - **Statement (`∀ᶠ w in 𝓝 w0`; `e₁ : Fin (H 0) ≃ Fin r ⊕ Fin (H 0 − r)`,
>   `e₂ : Fin (H (last L)) ≃ Fin r ⊕ Fin (H (last L) − r)`, `P0, QL` arbitrary):**
>   `∑ᵢⱼ ((M₂₁ · (M₁₁+1)⁻¹ · M₁₂) i j)² ≤ 1² · ((∑ M₁₁² + ∑ M₁₂²) + ∑ M₂₁²)`.
>
> - **Gloss.** At `w0`, `prod = B` so `M w0 = 0`: `P01 = P10 = 0`, `P00 = 1`, `(P00)⁻¹·P01 = 0`. The
>   functional `g w := ∑((P00 w)⁻¹·P01 w)²` is `ContinuousAt w0` (matrix inverse continuous at the unit
>   `P00 w0 = 1` via `continuousAt_matrix_inv` + `continuousAt_inv₀` on the scalar `det`, composed with
>   `continuous_Mw`) with `g w0 = 0 < 1`, so `g w ≤ 1` eventually. On that neighborhood,
>   `leak_frobenius_bound` gives `∑(P10·N·P01)² ≤ (∑P10²)·(∑(N·P01)²) ≤ Sreg · 1` (since `∑P10² ≤ Sreg`
>   and `∑(N·P01)² = g w ≤ 1`). Charge constant `t = 1` is uniform; `U` is the smallness neighborhood.
>
> - **Proved (unconditionally).** The bound above, pivot-agnostic (no `hfront` needed) — sorry-free,
>   axiom-clean (verified via the producer's `#print axioms`: `eventually_leak`'s supporting helpers
>   `continuous_prodAux_loc` / `continuous_prod_symm` / `continuous_Mw` are local copies, sorry-free).
>   Wired into `framedParams_split_eq_frame_raw`'s `hproducer` conjunct (c) at `t = 1`, with the
>   coupled neighborhood `U := {S5a IsUnit set} ∩ {S5b leak set}` (`Filter.inter_mem` of the banked
>   `eventually_P00_invertible` + this `eventually_leak`).
>
> - **Assumed.** none beyond the producer's standing hypotheses (`hB : B.rank = r`, `hr`, `hL`).
>
> - **Cited.** none (pure Mathlib continuity/Frobenius algebra + banked `leak_frobenius_bound`).
>
> - **Deferred.** none for the leak itself. (The producer's REMAINING gaps are the folded core
>   conjuncts (d')/(e'), a SEPARATE obligation — see `hproducer-decomp-cert.md` Part 2 (iv).)
>
> - **Status.** sorry-free + reviewed (full `DLNFibre` aggregator green, 8370 jobs; fidelity review
>   PASS on all 4 points incl. the adversarial goal-not-weakened check + decorrelated Codex, 2026-06-25).

## What this closes

The leak (c) was one of the 3 remaining `hproducer` sorries after the (b)-EXACT front-pivot landing.
With (c) closed, the producer `framedParams_split_eq_frame_raw` (and hence `deepest_gauge_construction`,
`deepest_loss_squeeze`) now depend on `sorryAx` ONLY through:
- the folded core (d')/(e') (2 sorries) — the per-layer↔global Schur charge, blocked on the UNBUILT
  structural bridge `Rcore = P11 − P10·⅟P00·P01 ↔ deepestCoreF (deepestCoreAbsorb (split w)).2.1`;
- the 2 L≥3-interior frame sorries (vacuous at L = 2).

PIN1 `deepestEPivot_regSlice_fderiv` stays axiom-clean (`[propext, Classical.choice, Quot.sound]`, no
`sorryAx`).

## The (d')/(e') blocker (precisely named)

Closing (d')/(e') needs, IN LEAN, the structural identity tying the producer's `Mw`-Schur complement
`Rcore = P11 − P10·⅟P00·P01` to the absorbed-core energy `coreΦ := deepestCoreF (deepestCoreAbsorb
(split w)).2.1 = ‖∏(reduced core layers)‖²`. The cert (`s5c-r2-cert.md`) gives the block-LDU
`Rcore = (∏ core)·(1 − K)·(…)` with `∏S = S0·S1` the per-layer core product; the banked
`schur_core_germ_comparability` then yields the additive charge `|frobSq Rcore − coreΦ| ≤ C·Sreg`, from
which the folded multiplicative form closes at `γ₁ = γ₂ = 1 + C` by pure arithmetic (positivity of
`Sreg, coreΦ, frobSq Rcore`). The MISSING piece is the Lean-level `Mw`-blocks ↔ `deepestCoreAbsorb`-core
identity — `coreΦ` is defined via `deepestCoreAbsorb`'s core slot, a SEPARATE construction from the
`Mw`-Schur; only the block-LDU ties them. Decorrelated Codex (`high`, 2026-06-25): arithmetic alone
cannot substitute for the missing geometric identity. Several-hundred-LoC of new block-LDU geometry on
the `deepestSplit` apparatus — beyond a single leaf tide.
