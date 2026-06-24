# Statement card — the HONEST genuine-diffeo `(3,3,4)` chart (replaces degenerate `phi334`)

The `b = a·β` chart that fixes the `phi334` slip (dropped `u₂,u₃` → `det ≡ 0` → null image →
false `cov = ⊤`). Lean file `lean/DLNFibre/DLN/RLCT/Validate/RouteMLayerCoverGEL2.lean`
@ `289616a666e7aabbf26193229b8262bd2778c5ec` (the working SHA; bump on change).

## The chart

`chartParams334 u` realises `A = [[a, a·β],[c, c·β + u₀·Δ]]`, `C = [[u₀·(1,τ) − β·S],[S]]`
(pivot `u₀`, `a = u₁`, `β = (u₂,u₃)`, `c = (u₄,u₅)`, `Δ = (u₆..u₉)`, `τ = (u₁₀..u₁₂)`,
`S = (u₁₃..u₂₀)`); `phi334 u = paramsEquivFlat M334 (chartParams334 u)`.

> **Claim (factorization).** `routeMCore M334 (phi334 u) = u₀² · Uval334(...)` — the SAME unit as
> the degenerate chart, on a chart now reading all 21 coords.
>
> - **Lean:** `routeMCore_phi334` (and `dlnLoss_chartParams334`).
> - **Gloss.** The squared-Frobenius loss pulled back through the honest chart factors as `u₀²`
>   times the `u₀`-free `Uval334`. Proved via `loss_schur_blowup_factor` (reused unchanged — the
>   product entries are `u₀·(linear)`).
> - **Proved.** The exact `F∘φ = u₀²·U` identity. **Status.** sorry-free, `[propext, Classical.choice, Quot.sound]`.

> **Claim (genuine diffeo — the anti-`phi334` gate).** The chart reads all 21 coords, reaches the
> origin, is continuous, and is `InjOn` off the null center `{u₀=0}∪{u₁=0}`.
>
> - **Lean:** `chartA334_reads_u2` (reads `u₂`, the dropped coord), `phi334_zero` (`phi334 0 = 0`),
>   `continuous_phi334`, `chartParams334_injOn` / `phi334_injOn` (InjOn off `{u₀=0}∪{u₁=0}`),
>   `phi334_image_subset_cubeBox` (image into every cube).
> - **Gloss.** Every `phi334` Jacobian column is live (no zero column ⟹ no `det ≡ 0` slip); the
>   chart is a bijection on a positive-measure set (all 21 coords recovered from the flat image);
>   it sends the deepest point to the cube centre.
> - **Proved.** All five facts, sorry-free, `[propext, Classical.choice, Quot.sound]` (no `sorryAx`).
> - **Cited.** none.

> **Claim (threshold).** The leaf monomial threshold is `≤ 4 = ½·minAdm M334`, with the genuine
> two-axis Jacobian `|u₀|⁷·|u₁|²` (`leafH334 = [7 at 0, 2 at 1]`, `leafK334 = [1 at 0]`).
>
> - **Lean:** `leafMonomialThreshold334_le`, `leafH334_prod_eq`, `monomialIntegrand_leaf334_eq`.
> - **Gloss.** The pivot axis `u₀` has `(k,h)=(1,7)` ⟹ ratio `8/2 = 4`; the `a²` factor is on a
>   `k=0` spectator axis (`u₁`) so it does NOT lower the threshold. minAdm = 8 (`minAdm_M334'`).
> - **Proved.** `≤ 4`. **Cited.** `monomial_rlct` (S2, at the leaf — the single permitted citation).

> **Claim (box-divergence capstone).** `∫⁻_{cubeBox 21 ε} |routeMCore M334|^{−c'} = ⊤` for `c'≥4`.
>
> - **Lean:** `routeM334_box_diverges` (and `routeM334_box_diverges_at_four`).
> - **Proved.** The divergence ASSEMBLY (`routeM334_box_diverges_of_chart`) is sorry-free and
>   consumes the bundle; the factorization/threshold/leaf-integrand/image are sorry-free.
> - **Deferred (ONE honest `sorry`, no longer FALSE).** The `cov` change-of-variables (the genuine
>   Jacobian c-o-v, Mathlib `lintegral_image_eq_lintegral_abs_det_fderiv_mul`). The determinant
>   value `det Dφ = −u₀⁷·u₁²` is verified-exact on the ACTUAL Lean `chartA334`/`chartC334` entries
>   (independent sympy recomputation in the tide-25 fidelity review; Codex `xhigh`; the structural
>   `b=aβ` det-`a²` ∘ shear det-`1` ∘ `pivotBlowup8` det-`u₀⁷`), matching `leafH334`. **Provenance
>   caveat:** the exploratory `genuine_chart_334c.py`/`334h.py` predate the `b=aβ` chart and give
>   `−u₀⁷` / `u₀¹⁰` respectively — they are STALE; trust the recomputation on the Lean entries.
>   `routeM334_box_diverges` axioms: `[propext, sorryAx, Classical.choice, Quot.sound, monomial_rlct]`.
> - **Status.** sorry-free EXCEPT the single `cov` residual; awaiting reviewer fidelity check.

## The `paramsEquivFlat`-as-linear-iso atom (BANKED this tide; the prior `cov` blocker, CLOSED)

The prior `cov` obstruction was named precisely: **`paramsEquivFlat M334` is a `piCurry`/`arrowCongr'`
reindex through the OPAQUE `Fintype.equivFin (FlatIdx M334)`, with no `ContinuousLinearEquiv`/fderiv/
det lemma** — so `phi334`'s fderiv could not be factored through it. This tide closes that blocker.

> **Claim (linear-iso atom).** `paramsEquivFlat H` is packaged as an honest ℝ-linear / continuous-linear
> iso, with the constant fderiv of the flattening and the sup-norm structure on `Params H`.
>
> - **Lean (`Foundations/ParamsFlatLinear.lean`, fully general in `H`/`L`, axiom-clean
>   `[propext, Classical.choice, Quot.sound]`):**
>   - `paramsEquivFlatLinear H : Params H ≃ₗ[ℝ] (Fin (flatDim H) → ℝ)` (the `LinearEquiv`, from
>     `LinearEquiv.piCurry` ×2 + `LinearEquiv.funCongrLeft`);
>   - `paramsEquivFlatCLE H : Params H ≃L[ℝ] (Fin (flatDim H) → ℝ)` (its `ContinuousLinearEquiv`, via
>     `LinearEquiv.toContinuousLinearEquiv`);
>   - `paramsEquivFlatLinear_coe` / `paramsEquivFlatCLE_coe`: SAME underlying function as
>     `paramsEquivFlat H` — both by `rfl` (the linear pieces share the `Equiv` of the measurable ones);
>   - `hasFDerivAt_paramsEquivFlat H P`: `HasFDerivAt (paramsEquivFlat H) (paramsEquivFlatCLE H).toCLM P`
>     (the reindex CLM is the flattening's constant fderiv);
>   - `instNormedAddCommGroupParams`/`instNormedSpaceParams`/`instFiniteDimensionalParams` on `Params H`
>     (the sup-norm via the unfolded `Pi`-of-`Pi`-of-`ℝ`), with `instTopologicalSpaceParams_eq_norm`:
>     the norm-topology is the existing product topology by `rfl` (NO diamond — Codex flagged this as
>     the suspected wall; it is `rfl`-compatible because `Matrix` is definitionally a function space).
> - **Reusable for general `M`** — the per-node SHARED `hfin` measure-plumbing atom (cost driver 2),
>   built once for any `H`.

## What remains for `cov` (the NARROWED residual)

With the reindex closed, the genuine c-o-v reduces to the self-map `Ψ := chartParams334 ∘
(paramsEquivFlat M334).symm : Params M334 → Params M334` (peel the outer reindex by
`MeasurePreserving.setLIntegral_comp_emb`; `Ψ` operates in matrix-entry coordinates, OFF the reindex):
the inner polynomial chart's `HasFDerivWithinAt`/`InjOn` (each entry a monomial; `hasFDerivAt_pi` +
`HasFDerivAt.mul`), the structural det `|det DΨ| = |u₀|⁷·|u₁|²` (reusing BANKED `pivotBlowupOnDeriv_det`
`= u₀⁷`, `det(shear)=1`, `det(b-subst)=u₁²` — NOT a 21×21 `Matrix.det`), and the `{u₁=0}` two-sided
null slice. Codex `xhigh` estimate: ~400–600 lines, the structural-det c-o-v.

## What changed vs the prior degenerate state

- 3 sorries (one a FALSE `cov = ⊤`) → 1 honest `sorry` (`cov`, a TRUE statement awaiting plumbing).
- `image_subset` and `Ubound` a.e.-positivity: were sorries, now PROVED (the honest chart reaches
  the origin and `Uval334 ≥ a² > 0` off the null `{u₁=0}`).
- The degenerate `chartA334`/`chartC334` (pinned `A(0,1)=A(0,2)=0`) replaced by the `b = a·β`
  forms reading all 21 coords; `loss_schur_blowup_factor` and the assembly reused unchanged.
- The bundle `L2AchieverChart` generalised to carry the genuine two-axis Jacobian `|u₀|⁷·|u₁|²`
  (was the false single-axis `|u_p|⁷`); threshold unchanged at 4.
- **This tide:** banked the `paramsEquivFlat`-as-linear-iso atom (`ParamsFlatLinear.lean`), CLOSING
  the named `cov` blocker (no `ContinuousLinearEquiv`/fderiv for the reindex); narrowed the `cov`
  residual to the inner structural-det c-o-v + null slice (off the reindex).
