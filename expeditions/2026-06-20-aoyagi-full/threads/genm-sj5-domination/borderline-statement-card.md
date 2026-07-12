# Statement card — off-sector BORDERLINE θ-interpolation (Obl-1/Obl-2 borderline)

**Thread `genm-sj5-domination`, borderline of Obligations 1 & 2.** Closes the borderline cut the two
convergent lemmas EXCLUDE: `a = M₂` (b=1, `corankOffSector_b1_le`) and `a = M₂ − b + 1` (b>1,
`corankOffSector_bpos_le`), where the convergent corank weight `∫ det^{−a/2}` LOG-diverges. Base branch
`expedition/aoyagi-full` @ `772d438f`; the module `RouteMSJOffSectorBorderline.lean` is added on top, and
`RouteMSJOffSectorBPos.lean`'s helper `corankWeight_bpos_lt_top` is generalised to a real exponent
(uncommitted — the controller integrates + wires `DLNFibre.lean`/`AxCheck.lean`; pin the SHA at integration).

---

> **Claim.** For a corank block of `b` rows, pivot energy `w > 0`, cross-shift `Ccross`, deeper product
> `Z` on the full-rank tail chart (`Z.rank = M₂`, `b ≤ M₂`), above the block Morse threshold `c' > ab/2`,
> and an interpolation weight `θ ∈ [0,1)` with the θ-scaled weight integrable (`θ·a < M₂ − b + 1`), the
> corank-block integral (freed inner `Γ`-integral over a finite-measure domain `sΓ`, integrated over the
> free corank block `A_cor ∈ [−1,1]^{b×M₂}`) is bounded by a finite, `w`-independent constant times the
> θ-reduced power of `w`:
>
> $$\int_{A_{\mathrm{cor}}\in[-1,1]^{b\times M_2}}\!\Big[\int_{\Gamma\in s_\Gamma}(w+\lVert C_{\mathrm{cross}}+\Gamma\,(A_{\mathrm{cor}}Z)\rVert_F^2)^{-c'}\,d\Gamma\Big]\,dA_{\mathrm{cor}}\ \le\ C_1\cdot w^{-(c'-\theta\,ab/2)}.$$
>
> At the borderline (`a = M₂` for b=1, `a = M₂ − b + 1` for b>1) the integrability condition
> `θ·a < M₂ − b + 1` is exactly `θ < 1`, so any `θ < 1` gives a LOG-FREE bound.
>
> - **Lean:** `DLNFibre.DLN.RLCT.corankOffSector_borderline_le` (general `b`, `θ ∈ [0,1)` with
>   `θ·a < M₂ − b + 1`), and `DLNFibre.DLN.RLCT.corankOffSector_borderline_atBorder_le` (specialised to
>   the borderline `a = M₂ − b + 1`, covering both b=1 and b>1)
>   (`lean/DLNFibre/DLN/RLCT/Validate/RouteMSJOffSectorBorderline.lean`; base @ `772d438f`, module uncommitted).
>   - supporting (new, same module): `enn_geom_interp` (ℝ≥0∞ weighted-geometric-mean of two upper bounds),
>     `borderline_real_identity` (the ℝ exponent collapse `(ATOM)^θ·(BOUNDED)^{1−θ} =
>     det^{−θa/2}·Cr^θ·w^{−(c'−θab/2)}`), `corankBlock_boundedGen_le` (the `Fin b` bounded brick).
>   - supporting (generalised): `corankWeight_bpos_lt_top` now takes a REAL exponent `s₀ < M₂ − b + 1`
>     (was the nat `a`); the θ-scaled weight is the `s₀ = θ·a` instance.
> - **Gloss.** With `A_cor : Fin b → Fin M₂ → ℝ` the free corank block, `Q_b := A_cor·Z`,
>   `Γ : Fin a → Fin b → ℝ` the freed corner: the double `lintegral` (over `A_cor ∈ matBox b M₂ 1`, then
>   `Γ ∈ sΓ`) of `(w + frobSq(Ccross + Γ·Q_b))^{−c'}` is `≤ C₁ · w^{−(c'−θ·ab/2)}` for a finite
>   `C₁ = Wθ · ofReal(Cresid(ab) c' ^ θ) · (volume sΓ)^{1−θ}`, where `Wθ = ∫_{matBox} det(Q_bQ_bᵀ)^{−θa/2}`.
> - **Proved.** The bound, unconditionally within the stated hypotheses. Mechanism: on the a.e. full-row-rank
>   set (`corank_survival_ae`; rank-drop locus null) both the banked ATOM
>   (`corankBlock_morsePeel_setLE`, `Apiv := 0`, core `≥ w` ⟹ `F A ≤ det(Q_bQ_bᵀ)^{−a/2}·Cresid(ab)·w^{−(c'−ab/2)}`)
>   and the BOUNDED brick (`corankBlock_boundedGen_le` ⟹ `F A ≤ w^{−c'}·vol(sΓ)`) hold pointwise; since
>   `F A ≥ 0` lies below both, `enn_geom_interp` gives `F A ≤ (ATOM)^θ·(BOUNDED)^{1−θ}`, which
>   `borderline_real_identity` collapses to `det(Q_bQ_bᵀ)^{−θa/2}·[Cresid(ab)^θ·vol(sΓ)^{1−θ}]·w^{−(c'−θab/2)}`.
>   Integrating over `A_cor`, the θ-scaled weight `Wθ = ∫ det^{−θa/2} < ⊤` (`corankWeight_bpos_lt_top` at
>   `s₀ = θ·a < M₂ − b + 1`). Axiom-clean `[propext, Classical.choice, Quot.sound]` (`#print axioms`,
>   force-recompiled).
> - **Assumed** (hypotheses the statement carries). `w > 0`; `b ≤ M₂`; the full-rank tail `Z.rank = M₂`;
>   `c' > ab/2` (atom applicability); `θ ∈ [0,1)`; the θ-scaled integrability `θ·a < M₂ − b + 1`; a
>   finite-measure domain `volume sΓ < ⊤`. The conclusion exposes the θ-REDUCED charge `θ·ab/2` on `w`
>   (not `ab/2`) — this is the price of backing off the divergent atom weight.
> - **Cited.** None external. All supporting facts banked, axiom-clean, in-repo:
>   `corankBlock_morsePeel_setLE` (`RouteMSJCorankPeel`), `corank_survival_ae` (`RouteMSJCorankSurvival`),
>   `posDef_gram_of_rank_eq` (`RouteMSJUnitsBridge`), `corankWeight_bpos_lt_top` /
>   `detGram_lintegral_box_lt_top` (`RouteMSJOffSectorBPos`), the ℝ≥0∞ rpow API
>   (`ENNReal.rpow_add_of_nonneg`, `mul_rpow_of_nonneg`, `ofReal_rpow_of_nonneg`, `rpow_le_rpow`,
>   `rpow_lt_top_of_nonneg`), the ℝ rpow API (`Real.mul_rpow`, `rpow_mul`, `rpow_add`). No `monomial_rlct`.
> - **Deferred** (named, not omitted).
>   1. **The threshold comparison `c' − θ·ab/2 < carrierThreshold(redChain)`.** This lemma exposes the
>      log-free bound with the reduced `w`-charge `θ·ab/2`; it does NOT itself assert the charge lands below
>      `carrierThreshold(M)`. That discharge is the DOWNSTREAM consumer's (it knows `minAdm(redChain)`): given
>      the strict margin `c' < carrierThreshold(M) = ½(ab + minAdm(redChain))`, one has `c' − ab/2 <
>      ½·minAdm(redChain)` already, so any `θ ∈ ((2c' − minAdm(redChain))/ab, 1)` makes `c' − θ·ab/2 <
>      ½·minAdm(redChain) = carrierThreshold(redChain)`, and this interval is nonempty. The OffSector level
>      cannot state this — `minAdm(redChain)` is a QIP quantity absent here. (Documented in the module
>      docstring, "Landing below carrierThreshold".)
>   2. **Obl-3 (Z-uniformity / tail-collapse)** and **the sector-compose** (good × off-sector →
>      `DecoratedStepHyp` → (□)) — controller/sibling threads, as for Obl-2.
> - **Structure & ideas observed** (design cert §2a/§2b + `codex/obl2-scoping-answer.md` Q5).
>   - **The interpolation is Codex Q5 verbatim:** `(ATOM)^θ·(BOUNDED)^{1−θ} = D^{−θa/2}·w^{−(c'−θab/2)}`,
>     `D = det(Q_bQ_bᵀ)`. The convex combination is between the atom (`det`-weight exponent `−a/2`, `w`-charge
>     `ab/2`) and the RAW bounded brick (`det`-weight exponent `0`, `w`-charge `0`, i.e. `w^{−c'}`) — NOT the
>     b=1-specific "`M₂/2`-bounded region" of Obl-1's two-region split. Interpolating the det-weight exponent
>     directly is cleaner and yields the tight `θ·ab/2` reduced charge.
>   - **Why θ<1 suffices:** the weight `∫ det^{−θa/2}` is finite for `θa < M₂ − b + 1` (the codimension of the
>     rank-drop locus). At the borderline `a = M₂ − b + 1` the convergent `θ = 1` sits exactly on the
>     divergence boundary (2-D radial `∫ r^{1−2s}dr`, log at `s = 1`); backing off to `θ < 1` gives a genuine
>     finite constant, growing like `1/(1−θ)` as `θ → 1` — the "log" reappearing as `C₁ → ∞`. Numeric check
>     (`M₂=2, a=2, Z=I`): weight `7.05 (θ=.5) → 63.5 (θ=.95) → 314 (θ=.99) → ∞ (θ=1)`.
>   - **Unified b=1/b>1:** using `Z.rank = M₂` (not Obl-1's coercivity `hZ`+`c₀`) collapses both borderlines
>     into ONE lemma, since `det((A·Z)(A·Z)ᵀ)` handles `b=1` (`= frobSq(A·Z)`) and `b>1` uniformly, with
>     `M₂ − 1 + 1 = M₂` giving the b=1 threshold.
> - **Route.** Real-exponent generalisation of `corankWeight_bpos_lt_top` (single call at `s₀ = θ·a`) +
>   the a.e. atom/bounded pointwise pair + `enn_geom_interp` (ℝ≥0∞ geometric mean via `rpow_add_of_nonneg`)
>   + `borderline_real_identity` (ℝ exponent bookkeeping, `ring`) + `lintegral_mul_const'` to pull the
>   constant out and box-clip the weight.
> - **Reviewer note (hypothesis change vs Obl-1).** The b=1 convergent predecessor `corankOffSector_b1_le`
>   used the coercivity hypothesis `∀A, c₀²·frobSq A ≤ frobSq(A·Z)` (+ `c₀ > 0`); this borderline lemma uses
>   `Z.rank = M₂` for BOTH b=1 and b>1 (matching Obl-2). The two are equivalent (coercivity ⟺ full row rank),
>   but the downstream b=1 chart must supply `Z.rank = M₂` (or a coercivity→rank bridge). Flagged for the
>   controller's wiring. Also, `C₁` depends on the specific `Z` (as in Obl-2) — the conclusion asserts only
>   `w`-independence, not `Z`-uniformity (that is Obl-3).
> - **Status.** sorry-free; axiom-clean `[propext, Classical.choice, Quot.sound]`. Fidelity review: PENDING
>   (controller to spawn independent `reviewer`).
