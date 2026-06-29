# Statement card — the opaque-width L=2 smeared chart + DECODE (general-over-widths)

The opaque-width generalization of the `(2,3,1)` chart (`RouteM231Smeared`), discharging the CHART side of
`routeMCore_box_diverges_smearedL2`'s two per-family hypotheses for ALL L=2 widths `M : Fin 3 → ℕ` with the
front-bottleneck split `r + s = M 1`, `0 < r`, `0 < M 2`. The dominant [HIGH]-cast piece (the DECODE) is
landed; what remains is the genuinely-analytic conditioned input (field A + the off-pole cancellation).

---

> **Claim (the DECODE + rate, ∀ L=2 widths).** For `M : Fin 3 → ℕ`, `hrs : r + s = M 1`, `0 < r`, `0 < M 2`,
> the chart `ψ := paramsEquivFlat ∘ packM ∘ shearMBody`, `R := pivotBlowupOn (deepest-top coords) pivot`
> satisfies `routeMCore M (ψ (R u)) = (zu u)²·Uunit u` off the shear pole (`P₁·Λ₀ = P₂`), with `Uunit`
> the z-free unit `‖P₁·H̄_unit‖²`.
>
> - **Lean:** `DLNFibre.DLN.RLCT.routeMCore_psiMap_Rmap` (`…/Validate/RouteMSmearedDecodeL2.lean`),
>   built on `decode_params` (the Params-level `packM (shearMBody (R u)) = chartL2Params M hrs (A0u u) …`).
> - **Proved.** The full opaque-width DECODE + rate, sorry-free, axiom-clean
>   `[propext, Classical.choice, Quot.sound]` (force-checked after olean delete). The DECODE is layerwise
>   (`fin_cases` over the `Fin 2` LAYERS only — never the opaque `i`/`j`): front layer = `A0u` identity;
>   deep TOP row = `z·H̄_unit − Λ₀·S_bot` (`Rmap_topSlot` + the shear-shift collapse `shiftCore_at_topSlot`);
>   deep BOTTOM row = the free residual `S_bot`.
> - **Key bricks banked** (`RouteMSmearedChartOpaque.lean`, `RouteMSmearedDecodeL2.lean`):
>   - `shearMBody_core`/`_spec` + `_apply_of_mem`/`_of_not_mem` — the shearM COORDINATE readback (the
>     prior tide's "dominant cost"; Codex `decode-arch`-confirmed: through `splitOfCoreSet_core/_spec`, NOT
>     an explicit `if`-form). The flagged biggest risk (slot-bijection alignment), de-risked.
>   - `shearMBodyME` / `measurableEmbedding_shearMBody` — shearMBody as a `MeasurableEquiv` (the inverse
>     subtracts the shift).
>   - `shiftFull` + `shiftFull_topSlot` — the `−Λ₀·S_bot` correction as an INJECTIVE single-term sum
>     (`coordOf (topSlot ·)` injective), sidestepping the dependent slot-extraction the `equivFin` route
>     needs. This is what cracked the deep-top shift index.
>   - `coordOf` injectivity + `topSlot`/`botSlot`/`frontSlot` distinctness (the dependent-`Sigma` casts via
>     `congrArg` on `.val`/the non-dependent `.1.1`, never `rw` on the dependent index).
> - **Generic chart certificates.** `measurePreserving_psiMap` + `measurableEmbedding_psiMap` (ψ); `Dmap` +
>   `Rmap_hasFDerivWithinAt`/`Rmap_injOn`/`Dmap_abs_det` (`|det| = |u pivot|^(r·M2−1)`, `topCoords_card =
>   r·M2`). All sorry-free, axiom-clean.

---

> **Claim (the headline, reduced to the analytic inputs).** For any L=2 widths the achiever box integral
> `∫⁻_{cubeBox N ε} |routeMCore M x|^{−c'} = ⊤` HOLDS, given ONLY the genuinely-analytic per-family inputs:
> the shear cancellation `P₁·Λ₀ = P₂` on each peeled point, FIELD-A containment `condBox ⊆ (ψ∘R)⁻¹(cubeBox ε)`,
> `U`-positivity, the box measurability/positivity, and the exponent `(r·M2−1) − 2c' ≤ −1`.
>
> - **Lean:** `DLNFibre.DLN.RLCT.routeMCore_smearedL2` (tightened) / `routeMCore_smearedL2_chart`
>   (`…/RouteMSmearedDecodeL2.lean`). Wires the generic chart into the banked
>   `routeMCore_box_diverges_smearedL2`. Axiom-clean `[propext, Classical.choice, Quot.sound]`.
> - **Proved (discharged generically).** The headline's CHART facts: ψ MP + measurable embedding; `R` C¹ /
>   injOn / `|det| = |u p|^h` with `h = r·M2 − 1`; the peeled rate's `z²·Uunit` form; the mechanical `z`/`U`
>   peel (`zu = z`, `Uy := Uunit(…0…)` z-free, via `zu_hN_insertNth` / `Uunit_hN_insertNth` and the
>   `hN`-cast cancellation `hN_cast_apply`).
> - **Assumed (the precisely-isolated remaining inputs, carried as named hypotheses).**
>   1. **The off-pole cancellation** `P₁·Λ₀ = P₂` on each peeled point. Reduces (banked
>      `Lam0u_cancel_of_factoring` = `proj_cancel_of_factorsThrough`) to the STRUCTURAL factoring
>      `P₂ = P₁·K` (`col(P₂) ⊆ col(P₁)`) + `det(P₁ᵀP₁) ≠ 0`. **The off-pole `det(P₁ᵀP₁) ≠ 0` forces `P₁`
>      full COLUMN rank ⟹ `r ≤ M 0`.** So for a FREE `A⁰` (the chart's front), UNIVERSAL cancellation
>      (every `A⁰` off the pole) holds exactly in the SQUARE case `r = M 0` (P₁ square-invertible ⟹
>      `col(P₁) = ℝ^{M0} ⊇ col(P₂)`, `K := P₁⁻¹·P₂`) — the verified precedents `(2,3,1)`/`(1,2,1)` are this
>      case. For tall `P₁` (`r < M 0`) it is FALSE for generic free `A⁰` (`s > 0`); the `r > M 0` regime is
>      EMPTY off the pole. Outside the square case the cancellation needs the conditioned structural
>      factoring `P₂ = P₁·K` (the achiever's front-bottleneck `col(P₂) ⊆ col(P₁)`). **Genuinely-new for
>      general `r`.**
>   2. **Field A** — the containment `condBox ⊆ (ψ∘R)⁻¹(cubeBox ε)` via the conditioned `Λ₀`-bound. The
>      `(2,3,1)` uses an explicit `2×2`-cofactor `nlinarith`; opaque `r,s` needs the general inverse-norm
>      bound (the handoff's "new analysis"). `U`-positivity (`U ≥ bound > 0` on the conditioned box) is the
>      same conditioning.
> - **Status.** sorry-free, axiom-clean (awaiting reviewer fidelity check).

---

## What this delivers vs the mission

The mission: discharge ∀ widths at L=2 the two hypotheses of `routeMCore_box_diverges_smearedL2`.
- **Hypothesis 1 (the peeled rate / the opaque-width ψ/R/DECODE — the [HIGH], multi-day piece): DONE
  generically.** The chart, the decode, the rate, ψ MP+embedding, the R certificates — all opaque-width,
  sorry-free, axiom-clean.
- **Hypothesis 2 (field A / the conditioned `Λ₀`-bound): carried as a named hypothesis.** Plus the off-pole
  cancellation reduces to the structural factoring (`M 0 ≤ r`).

So the headline is now **unconditional-over-widths EXCEPT** for the two genuinely-analytic facts
(field A + the cancellation factoring), precisely isolated. The chart machinery (the bulk + the cast swamp)
is general. The remaining gap is honest analysis, not chart plumbing.
