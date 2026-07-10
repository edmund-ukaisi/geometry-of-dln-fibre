# Statement card — `genm-resmap` (CoV resolution-map tide): the good-chart endpoint in matrix coords

Thread `genm-resmap`. Branch `genm-resmap` @ `91189dea` (based on `origin/genm-l2prod` @ `4d8e45a7`).
File: `lean/DLNFibre/DLN/RLCT/Validate/RouteMSJGoodChart.lean` (new module — NOT yet wired into the
`DLNFibre.lean` aggregator; controller to add the import).

These bricks are the **`→ endpoint` tail** of the pinned jbassembly pipeline
(`threads/genm-jbassembly/cert.md`): the good-chart resolved cross-coupled loss `g_cc`, flattened to
`Fin (dim) → ℝ`, fed to the banked corner endpoint. They do NOT close `sjJointResolution` — the
change-of-variables connecting `gammaPeelIntegral` to `g_cc` remains the mountain (see "Not closed").

All results **sorry-free, axiom clean-three** `[propext, Classical.choice, Quot.sound]` (force-recompiled
`#print axioms`).

---

> **Brick 1 — the flatten transport lemma (E hypothesised).** Given a measure-preserving flatten
> `E : ((Fin p → Fin q → ℝ) × (Fin r → Fin s → ℝ)) ≃ᵐ (Fin n → ℝ)` carrying the matrix-product box onto
> the flat cube, and an injective linear `L : (Fin n → ℝ) →ₗ (Fin m → ℝ)`, the matrix-box integral of
> `(∑ⱼ (L (E x))ⱼ²)^{−c'}` is finite for `c' < n/2`.
>
> - **Lean:** `DLNFibre.DLN.RLCT.twoMatBox_injectiveLinear_lintegral_lt_top`.
> - **Proved.** Pure transport onto the banked `corner_block_cube_lintegral_lt_top_of_injective`.
> - **Assumed.** `E` MP + box-preimage identity `hbox`; `L` injective; `0 ≤ c' < n/2`; `[NeZero n]`.

> **Brick 2 — the linear + measure-preserving matrix flatten.** `matFlatL p q : (Fin p → Fin q → ℝ)
> ≃ₗ[ℝ] (Fin (p*q) → ℝ)` (coe = the banked `eMatFlat`, so MP transfers) and the product flatten
> `twoMatFlatL p q r s : ((Fin p → Fin q → ℝ) × (Fin r → Fin s → ℝ)) ≃ₗ[ℝ] (Fin (p*q + r*s) → ℝ)`, with
> `measurePreserving_twoMatFlatL` and the box-preimage `twoMatFlatL_box_preimage`.
>
> - **Lean:** `matFlatL`, `coe_matFlatL`, `measurePreserving_matFlatL`, `twoMatFlatL`,
>   `twoMatFlatL_apply`, `measurePreserving_twoMatFlatL`, `twoMatFlatL_box_preimage`.
> - **Gloss.** The reusable "flatten of `E_T` to `Fin (Mval) → ℝ`" the recon-map (item 1) / l2prod
>   statement-card explicitly defer. MP via the banked `eMatFlat` / `sumPiEquivProdPi` / `arrowCongr'`
>   composite; linearity via `LinearEquiv.curry` + `funCongrLeft` + `sumArrowLequivProdArrow`.
> - **Proved.** Fully (LinearEquiv + measure-preservation + box-preimage).

> **Brick 3 — the good-chart cross-coupled loss endpoint (matrix coordinates).** For the good-chart data
> (pivot `P` left-invertible: `LP·P = 1`; deep factor `A₂` and resolved map `W` right-invertible:
> `A₂·RA = 1`, `W·RW = 1`) and `c' < (p*q + t*h)/2`,
>
>     ∫⁻ x in matBox p q 1 ×ˢ matBox t h 1,
>       ofReal ((frobSq (sjGoodMap P C W A2 x).1 + frobSq (sjGoodMap P C W A2 x).2) ^ (−c')) < ⊤.
>
> - **Lean:** `DLNFibre.DLN.RLCT.sjGoodMap_loss_matBox_lt_top` (helpers `sjGoodMapₗ`, `continuous_frobSq`).
> - **Gloss.** The resolved cross-coupled loss `g_cc(Γ, v) = frobSq(P·v·A₂) + frobSq((C·v + Γ·W)·A₂)`
>   (vslice §4a / jbassembly §1b) over the joint-block box is finite below the joint threshold. Packages
>   `sjGoodMap` (banked, `RouteMSJGoodLoss`) as an ℝ-linear map, flattens `(Γ, v)` (Brick 2), transports
>   the box to the flat cube, and feeds the banked `corner_block_cube_lintegral_lt_top_of_pos`; positivity
>   is the banked `sjGoodMap_loss_pos`.
> - **Proved.** Finiteness below `c' < (p*q + t*h)/2`.
> - **Assumed.** the three good-chart inverses; `0 ≤ c' < (p*q + t*h)/2`; `[NeZero (p*q + t*h)]`.
> - **Scope.** The TWO-block corner model (vslice §4a / `(3,3,3,4)` / L=3 binding branch), OPAQUE-WIDTH in
>   `p, q, t, h, o` (not `(3,3,3,4)`-specific). General `L ≥ 4` `E_T = ⊕Γᵢ` (more summands) is reached by
>   the same flatten+endpoint over a longer product — deferred to the recursion.

---

## Not closed (the remaining mountain — the CoV, recon-map item 1, ~65–75% new)

`sjJointResolution` (`RouteMSJResolution.lean:797/803`, `gammaPeelIntegral M t ρ κ c' < ⊤`) is
UNCHANGED. Brick 3 is its `→ endpoint` tail. The connecting **change-of-variables** transporting
`gammaPeelIntegral = ∫_{A'} ∫_{A0 ∈ matBox ∩ pivotChart} frobSq(rmatMul A0 (prod (tailChain M) A'))^{−c'}`
to a `g_cc`-box integral is the mountain. Its INGREDIENTS are largely banked; the ASSEMBLY is new:

1. **Block reindex of `A₀`** `Fin (M₀) ≃ Fin t ⊕ Fin (M₀−t)` matching `(ρ,κ)` — banked
   `matReindexEquiv` / `measurePreserving_matReindexEquiv` / `matReindexEquiv_preimage_chart`
   (`RouteMSJBlockReindex`), turning `A₀` on the chart into `fromBlocks A B C D` with `A` invertible.
2. **Schur split of the integrand** — banked `frobSq_schur_block_split` (`RouteMSJChartAlgebra`), exact:
   `frobSq(A₀·Q) = frobSq(A·Q̃_p) + frobSq(C·Q̃_p + Γ·Q_b)`.
3. **The shear `D ↦ Γ` as MP** — banked `measurePreserving_shearSub` (`RouteMSJPivotChart`), `blockSplitD`
   / `schurShift` (`RouteMSJChartShear`).
4. **DEPTH REDUCTION (genuinely-new)** — factor the sheared row-blocks of the tail product as
   `Q̃_p = v·A₂`, `Q_b = W·A₂` (for the two-block tail `A₁·A₂`: `W = (A₁)_b`, `v = (A₁)_p + A⁻¹B(A₁)_b`).
   Then the Schur split output equals `g_cc(Γ, v)` EXACTLY (verified on paper:
   `A·Q̃_p = P·v·A₂`, `C·Q̃_p + Γ·Q_b = (C·v + Γ·W)·A₂`). This pointwise bridge is reachable but is only one
   ingredient — the MEASURE transport of the `(A0, A')`-integral to the `(Γ, v)`-box is the labour.
5. **The refined cover** `matBox ∩ pivotChart = good {|det pivot minor| ≥ δ·scale} ∪ deeper` — the set
   split is trivial (`lintegral_union_le`); the VALUE is (a) on `good`, the pivot is bounded below so
   `A` is left-invertible + `A₂`, `W` right-invertible (feeding Brick 3's hypotheses), and (b) on
   `deeper` (small-pivot + `A_{L-1}`-rank-drop), non-binding by the banked charge inequality
   `sjChargeBudget_le` (`RouteMSJResolution:203`).
6. **The L-recursion over the rank flag** + deeper-branch termination (banked charge; flag well-founded).

**Handoff:** the next tide builds the CoV assembly (items 1–6). Brick 3 is the terminal chart it lands
on (with `n = dim E_T = Mval(branch)`). The one genuinely-new algebraic piece is item 4 (depth
reduction); the measure plumbing (items 1–3, 5) is banked-ingredient assembly; item 6 is the recursion.

## Fidelity note

The bricks are named for exactly what they prove (flatten transport / linear+MP flatten / good-chart
endpoint finiteness). `sjGoodMap_loss_matBox_lt_top` asserts finiteness of the `g_cc`-box integral GIVEN
the good-chart inverses — it does NOT assert that `g_cc = frobSq(A₀·Q)` after a CoV (that is item 4/the
mountain, deferred). The three inverse hypotheses are the good-chart hypotheses (pivot bounded below,
deep factor generic), minimal-and-necessary (cf. the reviewed `sjGoodMap_injective`).
