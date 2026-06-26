# Thread 22 — the per-pivot conjugation skeleton (B3-5) — statement card

**Status: sorry-free (pending reviewer fidelity).** Module
`lean/DLNFibre/Core/FibreChartConjugation.lean`. Whole library green (3790 jobs); all headlines
axiom-clean `[propext, Classical.choice, Quot.sound]` (gated via `#print axioms`). Route taken: the
**conjugation skeleton** (Codex xhigh, decorrelated, option a), NOT the per-pivot re-derivation.

**Scope verdict (honest, per brief): PARTIAL — the per-pivot trivialization family, NOT yet
`locallyTrivial`.** The conjugation skeleton is built end-to-end: the deep-chart trivialization `e_β`
transports along the endpoint-permutation gauge to a genuine `LocalTrivializationDatum` at **every**
pivot `(s, t)`. What is **NOT** built (the genuinely new rung Codex flagged): the identification of
the ambient transition cocycle with the composite `e_{s,t} ∘ e_{s',t'}⁻¹` on chart overlaps. So this
is **NOT** named `locallyTrivial`.

---

## Card 1 — the conjugation seam (the load-bearing determinant identity)

> **Claim.** The endpoint-permutation gauge `pivotGauge σ τ`, applied through the coordinate-change
> `AlgEquiv` `gaugeEquiv`, carries the **top-left** deep pivot minor `ΔPdeep` to the **`(s, t)`**
> deep minor `ΔPdeepAt s t`, when `σ`/`τ` carry the first `r` rows/columns to the selected ones.
>
> - **Lean:** `DLNFibre.Core.gaugeEquiv_ΔPdeep_eq_ΔPdeepAt` (+ the matrix lemma
>   `map_gaugeEquiv_multPoly`) (`lean/DLNFibre/Core/FibreChartConjugation.lean`)
> - **Gloss.** `gaugeEquiv d (pivotGauge d σ τ) (ΔPdeep d r hp hq) = ΔPdeepAt d r s t`, given
>   `hN : Fin.last N ≠ 0`, `hσ : ∀ i, σ (castLE i) = s i`, `hτ : ∀ j, τ (castLE j) = t j`. The genuine
>   determinant identity: `gaugeEquiv` sends the generic product `M = of (multPoly d)` to its endpoint
>   conjugation `σ.permMatrix · M · τ⁻¹.permMatrix = M.submatrix σ τ` (`gaugeEquiv_multPoly` +
>   `PEquiv.toMatrix_toPEquiv_mul`), whose top-left `r × r` block is the `(s, t)` minor; det commutes
>   with the algebra map.
> - **Proved.** unconditional over a field `k` (universe `u`); `N ≥ 1`.
> - **Assumed.** `r ≤ d (last N)`, `r ≤ d 0`; the selector/permutation match `hσ`, `hτ`; `hN`.
> - **Cited.** none.
> - **Status.** sorry-free, axiom-clean.

## Card 2 — the descent to the chart-closure quotient + the chart-element carry

> **Claim.** `gaugeEquiv P` preserves `vanishingIdeal (sweepSigma)` (the rank-`r` locus is
> `G_d`-stable) and descends to a `k`-algebra automorphism `gaugeEquivSigma P` of the chart-closure
> ring `sweepSigmaRing`, carrying the top-left chart element `chartDsig` to the `(s, t)` element
> `chartDsigAt s t`.
>
> - **Lean:** `DLNFibre.Core.gaugeEquivSigma` + `DLNFibre.Core.gaugeEquivSigma_chartDsig`
>   (supporting: `eval_gaugeEquiv`, `productRankLocus_smul_stable`,
>   `gaugeEquiv_mem_vanishingIdeal_sweepSigma`, `vanishingIdeal_sweepSigma_map_gaugeEquiv`,
>   `gaugeEquiv_eq_baseChangePullback`, `gaugeEquiv_symm_eq_inv`)
> - **Gloss.** `gaugeEquivSigma : sweepSigmaRing ≃ₐ[k] sweepSigmaRing` (via `Ideal.quotientEquivAlg`),
>   and `gaugeEquivSigma d r (pivotGauge d σ τ) (chartDsig …) = chartDsigAt d r s t`. The descent
>   uses: `gaugeEquiv P` = the banked `baseChangePullback P` (`gaugeSub = baseChangeSub`), so it
>   evaluates as the `G_d`-shift (`eval_baseChangePullback`); `mult (P • A) = P_last · mult A · P_0⁻¹`
>   + endpoint-unit rank invariance give `G_d`-stability of `productRankLocus`.
> - **Proved.** over `[Field k] [Infinite k]`, dimension vector `Fin (N + 2) → ℕ` (the chart index).
> - **Assumed.** `r ≤ d (last (N+1))`, `r ≤ d 0`; `hσ`, `hτ`.
> - **Cited.** none.
> - **Status.** sorry-free, axiom-clean.

## Card 3 — the per-pivot trivialization `e_{s,t}` + the per-pivot datum

> **Claim.** For **every** pivot `(s, t)` (with `σ, τ`), the localized `(s, t)` chart total ring
> `Away (chartDsigAt s t)` is identified with the schur-side ring `Away chartGfib` and with the
> product `SchurLoc ⊗_k sweepFibreRing` — the SAME standard fibre+schur ring the top-left chart uses —
> yielding a genuine `LocalTrivializationDatum` at the pivot.
>
> - **Lean:** `DLNFibre.Core.chartLocalizedAlgEquivAt`, `DLNFibre.Core.chartDsigAt_tensorEquiv`,
>   `DLNFibre.Core.perPivotLocalTrivializationDatum` (abstract bridge: `DLNFibre.Core.awayCongr`)
> - **Gloss.** `chartLocalizedAlgEquivAt : Away (chartDsigAt s t) ≃ₐ[k] Away (chartGfib)` is
>   `(awayCongr (gaugeEquivSigma P) chartDsig (chartDsigAt s t)).symm` then `e_β`. The datum's
>   `chartElt = chartDsigAt s t`, `trivialization = chartDsigAt_tensorEquiv` (the `(s,t)` analogue of
>   thread-11's `reducedFibre_chartDsig_tensorEquiv_reducedVariety`). `awayCongr` is the localization
>   transport of an `AlgEquiv` carrying `a` to `b` (`IsLocalization.Away.mapₐ` both directions,
>   round-trips by `IsLocalization.ringHom_ext`). The identity gauge recovers the top-left datum
>   (`perPivotLocalTrivializationDatum_topLeft`).
> - **Proved.** over `[Field k] [Infinite k]`, `Fin (N + 2) → ℕ`.
> - **Assumed.** as Card 2.
> - **Cited.** none.
> - **Deferred (the remaining rung to `locallyTrivial`).** the transition cocycle on the
>   trivializations: restricting the per-pivot charts to the double overlap
>   `D(chartDsigAt s t · chartDsigAt s' t')` and identifying the restricted composite
>   (`e_{s,t} ∘ e_{s',t'}⁻¹` *on that overlap* — the unrestricted composite does not type-check, the
>   sources differ) with the ambient cocycle `Core.FibreBundleTransition.awayOverlapTransition`. Same
>   target ring is a uniform normal form, NOT the cocycle. A denominator-bookkeeping comparison of two
>   localization presentations; honestly NOT built.
> - **Status.** sorry-free, axiom-clean.

---

## What this earns and does NOT earn

- **EARNED:** the conjugation skeleton + a genuine per-pivot `LocalTrivializationDatum` at every
  pivot of the per-minor cover, all sharing the standard fibre. This closes the rung the prior
  threads flagged as "plausible-but-not-automatic": the whole deep chart at `(s, t)` IS the
  gauge-conjugate of the top-left one (seam + descent + per-pivot `e_{s,t}`).
- **NOT EARNED:** `locallyTrivial`. The cover (#18) + ambient cocycle (#19) + per-pivot
  trivializations (#22, here) are all present, but the transition cocycle has NOT been transported
  onto the per-pivot trivializations (the comparison of the ambient `awayOverlapTransition` with the
  restricted double-overlap composite `e_{s,t} ∘ e_{s',t'}⁻¹`). That is the precise, named remaining
  cost.

## Net B3 state (controller synthesis)

single-chart triviality (#11) + per-minor open cover + chart family (#18) + the ambient transition
cocycle (#19) + the top-left `LocalTrivializationDatum` (#21) + **the conjugation skeleton: per-pivot
trivializations + per-pivot `LocalTrivializationDatum` at EVERY pivot (#22)**. The one remaining rung
to the EARNED `locallyTrivial` name is the **cocycle transport** — identifying the ambient cocycle
with the per-pivot transition `e_{s,t} ∘ e_{s',t'}⁻¹` on overlaps.
