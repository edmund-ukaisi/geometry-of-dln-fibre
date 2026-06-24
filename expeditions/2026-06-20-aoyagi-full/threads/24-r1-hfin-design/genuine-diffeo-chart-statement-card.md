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
>   value `det Dφ = −u₀⁷·u₁²` is verified-exact (sympy `genuine_chart_334c.py` + Codex `xhigh` +
>   the structural `b=aβ` det-`a²` ∘ shear det-`1` ∘ `pivotBlowup8` det-`u₀⁷`), matching `leafH334`.
>   The Lean obstruction is precise: **`paramsEquivFlat M334` is a `piCurry`/`arrowCongr'` reindex
>   using the OPAQUE `Fintype.equivFin (FlatIdx M334)`, with no `ContinuousLinearEquiv`/fderiv/
>   det-`±1` lemma** — so `phi334`'s fderiv cannot yet be factored through it. Building that
>   `paramsEquivFlat`-as-linear-iso is the heavy per-node measure-plumbing atom the `hfin`
>   certificate flags (cost driver 2). `routeM334_box_diverges` axioms: `[propext, sorryAx,
>   Classical.choice, Quot.sound, monomial_rlct]`.
> - **Status.** sorry-free EXCEPT the single `cov` residual; awaiting reviewer fidelity check.

## What changed vs the prior degenerate state

- 3 sorries (one a FALSE `cov = ⊤`) → 1 honest `sorry` (`cov`, a TRUE statement awaiting plumbing).
- `image_subset` and `Ubound` a.e.-positivity: were sorries, now PROVED (the honest chart reaches
  the origin and `Uval334 ≥ a² > 0` off the null `{u₁=0}`).
- The degenerate `chartA334`/`chartC334` (pinned `A(0,1)=A(0,2)=0`) replaced by the `b = a·β`
  forms reading all 21 coords; `loss_schur_blowup_factor` and the assembly reused unchanged.
- The bundle `L2AchieverChart` generalised to carry the genuine two-axis Jacobian `|u₀|⁷·|u₁|²`
  (was the false single-axis `|u_p|⁷`); threshold unchanged at 4.
