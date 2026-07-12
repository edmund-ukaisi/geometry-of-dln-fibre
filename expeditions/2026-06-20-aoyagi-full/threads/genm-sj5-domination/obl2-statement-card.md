# Statement card — Obl-2 (off-sector, `b>1` corank-integrability, convergent regime)

**Thread `genm-sj5-domination`, Obligation 2.** The `b>1` generalisation of Obl-1
(`corankOffSector_b1_le`). Base branch `expedition/aoyagi-full` @ `286065ed`; the module
`RouteMSJOffSectorBPos.lean` is added on top (uncommitted — the controller integrates + wires
`DLNFibre.lean`/`AxCheck.lean`; pin the SHA at integration).

---

> **Claim.** For a corank block of `b` rows, a fixed pivot energy `w > 0`, cross-shift `Ccross`, and a
> deeper product `Z` on the full-rank tail chart (`Z.rank = M₂`, `b ≤ M₂`), in the CONVERGENT regime
> `a < M₂ − b + 1` and above the block Morse threshold `c' > ab/2`, the corank-block integral (the freed
> inner `Γ`-integral over any domain `sΓ`, integrated over the free corank block `A_cor ∈ [−1,1]^{b×M₂}`)
> is bounded by a finite, `w`-independent constant times a single shifted power of `w`:
>
> $$\int_{A_{\mathrm{cor}}\in[-1,1]^{b\times M_2}}\!\Big[\int_{\Gamma\in s_\Gamma}(w+\lVert C_{\mathrm{cross}}+\Gamma\,(A_{\mathrm{cor}}Z)\rVert_F^2)^{-c'}\,d\Gamma\Big]\,dA_{\mathrm{cor}}\ \le\ C_1\cdot w^{-(c'-ab/2)}.$$
>
> - **Lean:** `DLNFibre.DLN.RLCT.corankOffSector_bpos_le`
>   (`lean/DLNFibre/DLN/RLCT/Validate/RouteMSJOffSectorBPos.lean`; base @ `286065ed`, module uncommitted)
>   - supporting: `corankWeight_bpos_lt_top` (corank weight `< ⊤`), `detGram_lintegral_box_lt_top`
>     (box-clipped determinant integral at general side length `T`).
> - **Gloss.** With `A_cor : Fin b → Fin M₂ → ℝ` the free corank block, `Q_b := A_cor·Z` the corank block,
>   `Γ : Fin a → Fin b → ℝ` the freed corner: the double `lintegral` (over `A_cor ∈ matBox b M₂ 1`, then
>   `Γ ∈ sΓ`) of `(w + frobSq(Ccross + Γ·Q_b))^{−c'}` is `≤ C₁ · w^{−(c'−ab/2)}` for a finite
>   `C₁ = ofReal(Cresid(ab) c') · Wenn`, where `Wenn = ∫_{matBox} det(Q_bQ_bᵀ)^{−a/2}`.
> - **Proved.** The bound, unconditionally within the stated hypotheses. Mechanism: a.e. `A_cor` gives
>   full row rank `Q_b` (`corank_survival_ae`), so `Q_bQ_bᵀ` is PosDef (`posDef_gram_of_rank_eq`) and the
>   banked corank atom (`corankBlock_morsePeel_setLE`, `Apiv := 0`) applies pointwise, dropping the shifted
>   core to `w^{−(c'−ab/2)}`; the rank-drop locus is Lebesgue-null (contributes `0`); the corank weight
>   `Wenn` is finite by normalising `ZZᵀ = L Lᵀ` (`exists_gram_normalizer`), the linear change of variables
>   `A ↦ A·L` (`lintegral_comp_rightMulₚ`), and the box-clipped determinant integral
>   (`detGram_lintegral_box_lt_top`, `r = b ≤ M₂`, threshold `a < M₂ − b + 1`). Axiom-clean
>   `[propext, Classical.choice, Quot.sound]` (`#print axioms`, force-recompiled).
> - **Assumed** (hypotheses the statement carries). `w > 0`; `b ≤ M₂`; the CONVERGENT bound
>   `a < M₂ − b + 1` (strict); the full-rank tail `Z.rank = M₂`; `c' > ab/2`. The charge in the conclusion
>   is `ab = peelCharge` — the design's level-0 FREED contribution (NOT `C₀ = ab + minAdm(redChain) =
>   minAdm(M)`); fed to the level-0 reduced IH it needs `c' − ab/2 < ½·minAdm(redChain@t)`, i.e.
>   `c' < ½·minAdm(M) = carrierThreshold(M)` — the exact threshold.
> - **Cited.** None external. All supporting facts are banked, axiom-clean, in-repo:
>   `corankBlock_morsePeel_setLE` (`RouteMSJCorankPeel`), `corank_survival_ae` (`RouteMSJCorankSurvival`,
>   the polynomial-null rank-drop deletion), `posDef_gram_of_rank_eq` (`RouteMSJUnitsBridge`),
>   `exists_gram_normalizer` (`RouteMSJGramSqrt`, CFC square root), `lintegral_comp_rightMulₚ`
>   (`RouteMSJGammaAtom`, the raw-pi CoV avoiding the measure diamond), `qbox_lintegral_lt_top` /
>   `rowsEquiv` / `measurable_detGram` (`RouteMSJProductTube`, `RouteMSJQBoxCore`). No `monomial_rlct`.
> - **Deferred** (named, not omitted).
>   1. **The borderline `a = M₂ − b + 1`** — the atom weight `Wenn` diverges (log) there. This is the
>      `(3,3,3)@t=1` case (`a=b=2`, `M₂=3`, `M₂−b+1 = 2 = a`). It mirrors Obl-1's `a = M₂` log follow-up
>      and is reachable by a θ-interpolation of the atom/bounded bricks (Codex Q5); NOT built here.
>   2. **The tail-collapse (Obl-3).** `Z.rank = M₂` is fixed; where `Z` itself degenerates (coercivity
>      constant becoming non-uniform) is a deeper flag level — Obl-3's uniform adapted-chart job.
>   3. **The sector-compose** (good sector × off-sector → `DecoratedStepHyp`) and the arity IH — controller.
>   The multi-level singular-FLAG stratification the design cert §2b describes is NOT needed for this
>   convergent regime: the level-0 atom charge `ab` already closes it. (`a > M₂ − b + 1` never occurs at a
>   genuine `b>1` binding cut — see Structure below — so the multi-level flag is only latent at the
>   borderline.)
> - **Structure & ideas observed** (the reshaping, decorrelated-Codex-confirmed —
>   `codex/obl2-scoping-{prompt,answer}.md`, `codex/obl2-scoping-answer.md` re-derives each independently).
>   - **`a ≤ M₂ − b + 1` at every genuine (`a ≥ 1`) `b>1` binding cut** (a theorem, not a sweep artefact):
>     convexity `R_{t+1} − R_t ≥ a + b − 1` (banked `RouteMSJTransversality`) + incidence
>     `R_{t+1} − R_t ≤ M₂` give `a + b − 1 ≤ M₂`. Sweep (arity ≤5, widths ≤6): 250 strict-convergent, 70
>     borderline, **0** above. So the convergent-regime lemma covers all genuine `b>1` binding cuts bar the
>     borderline.
>   - **"The flag" = use `det(Q_bQ_bᵀ) = ∏τ_k²`, not `σ_min(Q_b)² = τ_min²`.** The design cert's
>     "`σ_min`-only UNDERSHOOTS `(3,3,3)`: `5/2 < 7/2`" is a criticism of the smallest-singular-value weight;
>     the full determinant retains the anisotropy, and `detGram_lintegral_lt_top` already integrates across
>     the rank-drop locus up to the codimension threshold `a < M₂ − b + 1`. The multi-level flag is a bookkeeping
>     device for the charge, unnecessary once the det weight converges.
>   - **Null-set deletion is legitimate here.** The rank-drop locus `{det(Q_bQ_bᵀ)=0} = {rank A < b}` is
>     Lebesgue-null; any nonneg integrand integrates to `0` on it (no `w`-fixed argument needed). The design
>     cert's "NO null-set deletion" warning is about the OUTER tail integral (where the reduced loss → 0),
>     not this inner corank block over the free box at fixed `w > 0`.
> - **Route.** R-CoV (Codex-ranked cheapest): Gram normaliser `L = (ZZᵀ)^{1/2}` + linear CoV `A ↦ A·L`
>   (Jacobian `(det L)^b`, banked `lintegral_comp_rightMulₚ`) + indicator transport of the box + box
>   enclosure `matBox·L ⊆ matBox b M₂ (∑ₖⱼ|L k j|)` + `detGram_lintegral_box_lt_top`. Chosen over R-mono
>   (PSD Löwner det-monotonicity, absent from Mathlib v4.29, source-checked).
> - **Reviewer note (Z-uniformity).** The finite constant is `C₁ = ofReal(Cresid(ab) c') · Wenn`, and
>   `Wenn = ∫_{matBox} det((A·Z)(A·Z)ᵀ)^{−a/2}` DEPENDS on the specific `Z` (through its singular values,
>   via the Jacobian `(det L)^{−b} = (det ZZᵀ)^{−b/2}` and the transformed box). The conclusion asserts only
>   `w`-independence (true) — it does NOT overclaim `Z`-uniformity. This is a genuine WEAKENING relative to
>   the b=1 predecessor `corankOffSector_b1_le`, whose constants were uniform over a `c₀`-coercivity class of
>   `Z`. Consistent with the declared "fixed full-rank tail" scope; the Z-uniform version (uniform adapted
>   charts across the tail) is the deferred Obl-3, which the sector-compose must supply (or fix `Z` per fibre).
> - **Status.** sorry-free; axiom-clean `[propext, Classical.choice, Quot.sound]`. Fidelity review: PASS
>   (independent `reviewer` + its own decorrelated Codex red-team, 2026-07-12): FIDELITY PASS, NON-VACUITY /
>   NO-LAUNDERING PASS, SOUNDNESS vs design cert §2b PASS-WITH-NOTE, BUILD/AXIOM PASS — "fit to integrate +
>   checkpoint."
