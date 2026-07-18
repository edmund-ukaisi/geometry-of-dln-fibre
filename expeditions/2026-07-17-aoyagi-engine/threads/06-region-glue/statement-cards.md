# Statement cards — thread 06 (region-glue)

The per-leaf finiteness read + cover assembly that discharges `region_glue`'s analytic
hole **from `ChartBridge`** (the CoV bridge is a hypothesis here; its *construction* is a
separate obligation). All three headline results are axiom-clean
`[propext, Classical.choice, Quot.sound]` — verified by forced `#print axioms`, no `sorryAx`
despite importing the (sorried) obligation file, confirming genuine assembly rather than
laundering the construction hole.

SHA pinned: `dbeddad0a8d1385e89363ecc4c6ea2993ec4a744`.

---

> **Claim (headline).** Given the change-of-variables bridge `ChartBridge M t` for a
> resolution tree `t`, and `c'` below half of every terminal exponent of `t`, the unit-box
> layer-product integral `∫_{paramsBoxM M 1} frobSq(prod M ·)^{-c'}` is finite. (This is the
> box-finiteness ingredient of the RLCT *upper* bound; it is NOT the `rlct = ½·codim`
> equality.)
>
> - **Lean:** `DLNFibre.DLN.RLCT.Engine.region_glue_of_chartBridge`
>   (`lean/DLNFibre/DLN/RLCT/Engine/RegionGlueAssembly.lean` @ `dbeddad0a`)
> - **Gloss.** For `t : ResolutionTree M`, `hbridge : ChartBridge M t`, `c' : ℝ`, and
>   `hrat : ∀ e ∈ terminalExponents t, c' < e/2`, we get `routeMLayerBoxIntegral M c' 1 < ⊤`
>   (i.e. `∫⁻ A in paramsBoxM M 1, ofReal (frobSq (prod M A) ^ (-c')) < ⊤`).
> - **Proved.** The finiteness, unconditionally in `c'` and `L`, from the bridge + ratio
>   hypotheses. Three branches: `c' ≤ 0` (no singularity, banked compact corner); `L = 0`
>   (`prod M A` is the constant empty product `1`, so a constant integrand on the finite-measure
>   box); `c' > 0, L ≥ 1` (`0` in the zero-locus `⊆` the atlas neighbourhood `U`, a small box
>   `paramsBoxM M ε ⊆ U ⊆ ⋃ leaves chartMap '' srcBox`, finite-cover bound, then the homogeneity
>   scaling-bridge globalization to the unit box).
> - **Assumed.** `ChartBridge M t` (the full CoV bridge: an upstairs-open box-neighbourhood
>   covered by chart images; per-leaf measurable+bounded `srcBox`, injective/disjoint
>   `divCoord`/`resCoord`, a.e.-injectivity off a null set, `LeafPullback`, `LeafJacobian`; edge
>   coherence) and the ratio `c' < e/2` for every terminal exponent. Both are hypotheses,
>   consumed as stated — nothing relocated to fresh holes.
> - **Cited.** None. Pure Mathlib (area formula, Haar CoV, AM-GM) + banked engine foundations
>   (`paramsEquivFlatCLE`, `flatNodeLoss_smul` homogeneity, the 1-D radial/monomial reads).
> - **Deferred.** The *construction* of a `ChartBridge` for `resolutionOf M` (i.e.
>   `coverage_theorem` / `monomialization_terminates`) is NOT part of this result — it is the
>   coverage-design / rung-3–4 burden. This card certifies **provability from** the bridge only.
> - **Route.** Elder-ratified fork-8 area-formula revision: per-leaf area formula (Module B) →
>   flat monomial model read (Module A), glued over the finite leaf cover with the scaling-bridge
>   local→global step. No dependence on the `rlct = c*` / `cited_aoyagi_dln` interface.
> - **Status.** sorry-free (pending rev-glue fidelity verdict).

---

> **Claim (per-leaf read).** For a single leaf `l` satisfying the per-leaf `ChartBridge`
> tuple, with `c' > 0` below half its divisor exponents and (if positive) its residual rank,
> the box integral over the chart IMAGE `∫_{chartMap '' srcBox} frobSq(prod M ·)^{-c'}` is finite.
>
> - **Lean:** `DLNFibre.DLN.RLCT.Engine.leaf_chart_image_lintegral_lt_top`
>   (`lean/DLNFibre/DLN/RLCT/Engine/RegionGluePerLeaf.lean` @ `dbeddad0a`)
> - **Gloss.** Given `l`'s measurable bounded `srcBox`, injective/disjoint `divCoord`/`resCoord`,
>   an a.e.-injectivity witness (`InjOn chartMap (srcBox \ N)`, `volume N = 0`), `LeafPullback l`,
>   `LeafJacobian l`, and `hdivExp : ∀ k, c' < divExp k / 2`, `hres : 0 < resRank → c' < resRank/2`,
>   the image integral is `< ⊤`.
> - **Proved.** The finiteness. Empty `srcBox` is trivial; else the Mathlib area formula runs on
>   `Params M` (its `volume` supplied as an additive Haar measure via the banked linear
>   `paramsEquivFlatCLE`), the null exceptional fibre is discarded
>   (`addHaar_image_eq_zero_of_differentiableOn…`), the integrand is bounded pointwise
>   (`|det Dφ| = |det Dψ|·|det Dβ| ≤ hi·∏|u|^{divExp−1}` + `LeafPullback` squeeze + antitone
>   `t ↦ t^{-c'}`; a `frobSq = 0` vs `> 0` case split keeps the positive branch singularity-free),
>   transported to the flat cube and closed by the Module-A model read.
> - **Assumed.** The per-leaf `ChartBridge` tuple + the two ratio bounds, exactly as they appear
>   in `ChartBridge`. A faithful (not gap) subtlety: `LeafJacobian`'s `|det Dβ| = ∏ |u|^{divExp k − 1}`
>   is ℕ-power; `divExp k ≥ 1` is derived from `hdivExp` + `c' > 0` (a `0`-exponent divisor would
>   force `c' < 0`), so the ℕ→ℝ exponent cast is honest.
> - **Cited.** None.
> - **Deferred.** That the *construction* satisfies `LeafPullback`/`LeafJacobian`'s monomial
>   assertions (`F ∘ chartMap = (∏ u²)·residualCore`, the det factorization) — rung-3–4's burden,
>   per the elder field-pass scope caveat; a gap there surfaces there, not here.
> - **Status.** sorry-free (pending rev-glue fidelity verdict).

---

> **Claim (flat model read).** The monomialised leaf integrand
> `(∏ₖ |x_{dc k}|^{eₖ}) · (∑ᵢ x_{rc i}²)^{-c'}` has finite `∫⁻` over the closed flat cube
> `[−R,R]^d`, for divisor exponents `eₖ > −1`, `0 < c'`, residual rank `nr ≥ 1`, `c' < nr/2`.
>
> - **Lean:** `DLNFibre.DLN.RLCT.model_read_lt_top`
>   (`lean/DLNFibre/DLN/RLCT/Validate/RegionGlueModelRead.lean` @ `dbeddad0a`)
> - **Gloss.** For injective `dc`, `rc` with disjoint ranges into `Fin d`, `∀ k, -1 < e k`,
>   `0 < c'`, `hnr : c' < nr/2` (with `0 < nr`), the flat model integral is `< ⊤`.
> - **Proved.** The finiteness, engine-independent (flat coordinates only). Route: AM-GM
>   domination of the Morse factor `(∑ yᵢ²)^{-c'} ≤ nr^{-c'}·∏|yᵢ|^{-2c'/nr}` — **a.e.**, off the
>   coordinate hyperplanes `{x_{rc i}=0}` (each null via `Measure.pi_hyperplane`), NOT pointwise —
>   plus the injective/disjoint two-family reindex to a single all-axis product with every axis
>   exponent `> −1`, closed by `prod_abs_rpow_cube_lt_top`.
> - **Assumed.** `eₖ > −1`, `0 < c' < nr/2`, `nr ≥ 1`, injectivity/disjointness of the coord maps.
> - **Cited.** None (Mathlib AM-GM + `rpow` reads).
> - **Deferred.** None.
> - **Status.** sorry-free (pending rev-glue fidelity verdict).
