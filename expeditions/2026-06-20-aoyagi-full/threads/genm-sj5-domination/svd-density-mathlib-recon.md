# SVD / Gram-eigenvalue change-of-variables — Mathlib (v4.29) vs GAP recon

**Seat:** scout (reconnaissance), aoyagi-full Stage 2, `genm-sj5-domination`. **Date:** 2026-07-13.
**READ-ONLY** (no lean edits, no git). Instruments: `rg` over `.lake/packages/mathlib/` (Mathlib
`v4.29.0`, rev `8a17838`, 2026-03-30) + Read of the banked `RouteMSJ*` library.
**Scopes:** the heaviest new brick of the T-Obl3b waist base case (`tobl3b-routeA-waist-cert.md`
build-path **step 2**): the deep-layer rectangular-SVD / Gram-eigenvalue CoV with its Weyl/Wishart
Jacobian.

---

## ★ HEADLINE

- **The loss identity (build-path step 1) is ALREADY BANKED** — `RouteMSJFrontSpectral.frobSq_mul_eq_sum_eigenvalues`
  proves EXACTLY `‖A₀A₁‖² = Σⱼ λⱼ·‖(A₀Q)_{·j}‖²` (λ = eigenvalues of `A₁A₁ᵀ`, Q its eigenvector
  frame), via the Gram **spectral theorem**, no SVD of `A₁`. The cert's step-1 is done.
- **The A₀-side frame integration (build-path step 3) is ALREADY BANKED** — `RouteMSJOrthoExtend.exists_ortho_ext`
  (orthonormal-columns → full orthogonal extension) + `RouteMSJFrontSpectral.lintegral_comp_orthRightMulₚ`
  (`A₀ ↦ A₀Q` measure-preserving, `|det Q|=1`). This **sidesteps Haar-on-O(s) entirely on the A₀ side**.
- **The corner engine + shell cover + deep-Morse blocks (steps 5–6) are ALREADY BANKED** — `RouteMSJCorankQ.qPeelIntegral_lt_top`
  (complete, sorry-free), `RouteMSJShellCover.{weakEigCount,singularShell,singularShell_iUnion,lintegral_le_sum_finCover}`,
  `S1RadialMorse.sumSqND_box_lt_top`, `RouteMSJQBoxCore.qbox_lintegral_lt_top`.
- **The GAP is build-path step 2 ALONE: the `A₁`-integral's eigenvalue-marginal density** — turning
  `dA₁` into `∏ⱼσⱼ^{z−s}·∏_{i<j}|σ_i²−σ_j²| dσ · dμ(frame)` and integrating out the `A₁`-frame
  (`O(s)` × Stiefel `V_s(ℝ^z)`). **Mathlib provides NOTHING at any level** for this: no eigenvalue
  Jacobian, no Wishart/Weyl density, no Haar on `O(s)`, no Stiefel manifold, no coarea, not even
  eigenvalue-map continuity/differentiability. Only the *general* diffeomorphism CoV
  (`MeasureTheory.Function.Jacobian`) is banked — the scaffold, not the result.
- **Difficulty of step 2:** **s=1 waists — EASY (banked-composable now).** **s≥2 waists — HEAVY** by
  the literal SVD-density route (needs Stiefel+Haar, absent); **MODERATE-HEAVY** by the **cheapest**
  route: the deep-layer **polynomial Schur-flag recursion** (peel `A₁`'s own corank via Schur charts
  on `MeasureTheory.Function.Jacobian` + the banked qPeel, no new Mathlib primitives). **There is no
  moderate route to the global Vandermonde density itself.**

---

## Task 1 — Gram spectral / eigenvalues / singular values (loss identity)

### Banked in Mathlib (exact names)
- **`Mathlib/Analysis/Matrix/Spectrum.lean`** (the workhorse; already consumed by `weakEigCount`,
  `RouteMSJProductTube`, `RouteMSJFrontSpectral`):
  - `Matrix.IsHermitian.eigenvalues : n → ℝ`, `Matrix.IsHermitian.eigenvalues₀ : Fin (card n) → ℝ`
    (the SORTED/antitone tuple, `eigenvalues₀_antitone`), `Matrix.IsHermitian.eigenvectorUnitary`,
    `Matrix.IsHermitian.eigenvectorBasis` (`OrthonormalBasis`), `Matrix.IsHermitian.spectral_theorem`,
    `mulVec_eigenvectorBasis`, `det_eq_prod_eigenvalues`, `rank_eq_card_non_zero_eigs`.
- **`Mathlib/LinearAlgebra/Matrix/PosDef.lean`**: `Matrix.PosSemidef` (+ `.isHermitian`, `.det_nonneg`,
  `.trace_nonneg`, `.submatrix`, `.sqrt`), `posSemidef_self_mul_conjTranspose`.
- **`Mathlib/Analysis/InnerProductSpace/SingularValues.lean`**: `LinearMap.singularValues : ℕ →₀ ℝ`
  (the scalar sequence `√eigenvalues(Tᴴ∘T)`, antitone, `support = range(rank)`). **SCALARS ONLY** —
  no `U,Σ,V` factorization.

### Banked in the project (exact names) — the loss identity is DONE
- `RouteMSJFrontSpectral.frobSq_mul_eq_sum_eigenvalues (A₀ P)` :
  `frobSq (A₀·P) = Σⱼ eigenvalues(P·Pᵀ)ⱼ · Σᵢ ((A₀·Q)ᵢⱼ)²`, `Q = eigenvectorUnitary(P·Pᵀ)`.
  With `P = A₁` this **IS** the cert's `‖A₀A₁‖² = Σⱼσⱼ²‖A₀uⱼ‖²` (λⱼ=σⱼ², `uⱼ`=eigenvectors,
  `X_j := (A₀Q)_{·j}`). Supporting: `RouteMSJGammaAtom.frobSq_eq_trace`, `trace_conj_hermitian_eq_sum_eigenvalues`,
  `RouteMSJProductTube.sigMin` (smallest sing. val via `minStretch`, no `LinearMap.singularValues`),
  `sigMin_sq_eq_iInf_eigenvalues`.

**Verdict Task 1: cleanest route to the loss identity is BANKED — `frobSq_mul_eq_sum_eigenvalues`,
elementary from `spectral_theorem` + `frobSq_eq_trace`. Not the crux.**

---

## Task 2 — the measure CoV / density (THE CRUX) — GENUINELY ABSENT

### Mathlib has NONE of the eigenvalue/SVD density machinery
Confirmed-absent by `rg` (empty or false-positive-only):
- **eigenvalue-map Jacobian / `∏|λ_i−λ_j|` Vandermonde density** — absent. (`LinearAlgebra/Vandermonde.lean`
  exists but is the algebraic determinant `det[x_i^j]`, no measure content.)
- **Wishart / random-matrix eigenvalue density** — absent (no `Wishart` anywhere).
- **rectangular-SVD parametrisation measure / `A ↦ (σ,U,V)` CoV** — absent.
- **Weyl integration formula** (conjugation-invariant integral → chamber × class density) — absent.
- **coarea formula** (`∫ f = ∫∫_{level set} f/|∇g|`) — **absent** (`rg -i coarea` → 0 hits). Rules out
  a "integrate over σ-level-sets" shortcut for the σ-marginal.
- **eigenvalue-map continuity/differentiability** (`A ↦ eigenvalues A` continuous/`HasFDerivAt`) —
  absent. So even *starting* a Jacobian-CoV through the eigenvalue map needs new differentiability.

### The only banked CoV scaffold (the tool a density proof must be built ON)
- **`Mathlib/MeasureTheory/Function/Jacobian.lean`** — the general diffeomorphism CoV, fully present:
  `lintegral_image_eq_lintegral_abs_det_fderiv_mul`, `integral_image_eq_integral_abs_det_fderiv_smul`,
  `map_withDensity_abs_det_fderiv_eq_addHaar`, `lintegral_abs_det_fderiv_eq_addHaar_image`. Requires an
  **explicit differentiable parametrisation with a computed Jacobian determinant** — exactly what is
  missing for the SVD/eigenvalue map.
- `Measure.map_linearMap_addHaar_eq_smul_addHaar` (the LINEAR CoV) — banked; the project's
  `lintegral_comp_rightMulₚ` / `lintegral_comp_orthRightMulₚ` ride it. **Handles linear/orthogonal maps
  only**; the SVD map is nonlinear.

**Verdict Task 2: the density is GENUINELY ABSENT. It must be built from scratch on
`MeasureTheory.Function.Jacobian`, including new eigenvalue/Schur-map differentiability + the Jacobian
determinant. This is build-path step 2, the one substantial new brick — confirming the cert's
"possibly the heaviest single piece".**

---

## Task 3 — compact-group integration (`O(s)`, Stiefel `V_s(ℝ^z)`)

### Mathlib status
- `Matrix.orthogonalGroup n R = Matrix.unitaryGroup n R = unitary (Matrix n n R)`
  (`LinearAlgebra/UnitaryGroup.lean`) — a `Submonoid`/`Group` with `StarMul`. **No `TopologicalGroup`,
  `CompactSpace`, `IsManifold`, `LieGroup`, or Haar-measure instance** (`rg` → 0 hits). `entry_norm_bound_of_unitary`
  (bounded entries) exists but is not wired to compactness.
- **Haar exists generically** (`MeasureTheory/Measure/Haar/Basic.lean`: `haarMeasure`,
  `isHaarMeasure_haarMeasure`, `haarMeasure_unique`) for locally-compact Hausdorff groups — but is
  **not instantiated for `O(s)`**, and would still need a compactness proof + the SVD Jacobian to be
  useful.
- **Stiefel manifold `V_s(ℝ^z)` — ABSENT** (all "Stiefel" hits are the author "Jakob Stiefel"). The
  unit-sphere manifold `EuclideanSpace.instSphere` (`Geometry/Manifold/Instances/Sphere.lean`) exists,
  but the frame/Stiefel bundle is not built.

### The banked workaround (avoids Haar-on-O(s) on the A₀ side)
- `RouteMSJOrthoExtend.exists_ortho_ext` — any `U_s` (`U_sᵀU_s=1`) extends to full orthogonal
  `U∈O(M₂)` with first columns `U_s` (via Mathlib `Orthonormal.exists_orthonormalBasis_extension_of_card_eq`).
- `RouteMSJFrontSpectral.lintegral_comp_orthRightMulₚ` / `RouteMSJDeeperFlagCore.strongBlock_lintegral_le_unif`
  — the orthogonal right-mult `A₀ ↦ A₀·U` is measure-preserving (Jacobian `|det U|=1`), and `U`'s
  entries `≤1` bound the rotated box (frame-constant step). **So the A₀-frame integrates to a finite
  constant with NO Haar/Stiefel.**

**Verdict Task 3: `O(s)`/Stiefel integration is a GAP, but the A₀-frame side is fully dischargeable by
the banked orthogonal-extension + orthogonal-CoV. What remains genuinely needing frame integration is
the `A₁`-frame (its eigenvectors `O(s)` AND right singular vectors Stiefel `V_s(ℝ^z)`) inside the
density — i.e. the same crux as Task 2.**

---

## Task 4 — fallbacks if the density is absent (it is) — three routes, cheapest flagged

### (0) s=1 (rank-1) waists — BANKED-composable NOW (EASY)
For `s=1`, `A₁∈ℝ^{1×z}` a row, `A₀∈ℝ^{x×1}` a column, `‖A₀A₁‖² = ‖A₀‖²·‖A₁‖²` (outer product). So
`I(c) = (∫‖A₀‖^{−2c})·(∫‖A₁‖^{−2c})` — a **product of two Morse integrals**, each
`S1RadialMorse.sumSqND_box_lt_top`, finite for `c < ½·min(x,z) = ½·minAdm(x,1,z)`. **No density, no
frame, no qPeel.** Covers `(2,1,2),(3,1,3),(x,1,z)`. (The cert's "rank-1: literal PRODUCT of two
ℝ²-Morse".) *This is the immediate, cheap deliverable.*

### (a) Per-shell Schur route (cert §1.2) — does NOT compose off-the-shelf
The banked shell cover (`singularShell`+`_iUnion`+`lintegral_le_sum_finCover`) is measurability-free
and reusable. BUT the banked per-shell **corank/Schur machinery** (`RouteMSJCorankStep.corankStep`,
`RouteMSJChartShear.chartInner_schurShearFree_eq`, `RouteMSJCorankPeel.corankBlock_morsePeel_eq/_setLE`,
`RouteMSJGammaAtom.gammaAtom_aniso_shifted_eq`, consumed by `RouteMSJDeeperFlagCore.deeperFlag_shell_core_le`)
pivots the **FRONT factor** and needs `Q_b Q_bᵀ` positive-definite / `hconv : a < m−b+1` — **exactly
the head-split family the cert says WALLS on the waist** (`RouteMSJChartShear` header: "fails on the
bottleneck charts `M₁−t > min deeper widths`"; `deeperFlag_spineToCore` is the unproved `sorry` with
the pivot wall; `sjJointResolution` is the standing named sorry). **This route as banked does not reach
½·minAdm on the waist.**

### (b) Banked matrix-CoV composition — insufficient ALONE, but the backbone of (c)
`RouteMSJGammaAtom.{rightMulₚ, lintegral_comp_rightMulₚ, det_rightMulₚ, frobSq_mul_orthonormal_add}`,
`RouteMSJFrontSpectral.lintegral_comp_orthRightMulₚ`, `RouteMSJProductTube.{measurePreserving_rowsEquiv,
detGram_lintegral_lt_top, det_product_gram, sigMin_rpow_le_det_rpow_of_mem_box}`. These compose to the
**full-rank determinant/Gram route** (`∫ det(XXᵀ)^{−a/2} < ⊤` for `a < n−r+1`) — which is the correct
discharge for **non-waist** 3-width chains (product full-rank) but **degenerates on the waist**: the
product `A₀A₁` has rank `≤ s < min(x,z)`, so `det((A₀A₁)(A₀A₁)ᵀ) ≡ 0` and the `det^{−·}` majorant is
vacuous. **This is precisely why the front-first route walls on the waist.** These CoV lemmas do NOT,
alone, produce the `∏σ^{h}` monomial.

### (c) THE CHEAPEST route for s≥2 waists — deep-layer polynomial Schur-flag recursion
Instead of the transcendental global SVD/Wishart density (which needs Stiefel+Haar, all absent), peel
`A₁`'s **own** corank one direction at a time by a **Schur-complement chart on `A₁` itself** (pivot its
invertible `k×k` block; the Schur complement is a *rational/polynomial* map, so the Jacobian is a
`det(pivot)`-power — amenable to `MeasureTheory.Function.Jacobian`). The `∏σ^{h}` monomial is REPLACED
by the nested Schur-pivot determinant Jacobians; the recursion has depth `≤ s` and terminates at
`s=1`-like leaves (route 0). At the bottom, the banked `qPeelIntegral_lt_top` (q-block corner) consumes
the freed blocks directly. **Reuses: banked Jacobian CoV (Mathlib), qPeel + shell cover + Morse blocks
(project); NEW: deep-layer Schur charts (structurally close to the banked FRONT-factor Schur charts,
roles swapped) + the flag-recursion bookkeeping.** No Stiefel, no Haar, no Vandermonde density.

---

## Difficulty estimate for build-path step 2 (the density brick)

| sub-case | route | difficulty | banked leverage |
|---|---|---|---|
| non-waist 3-width (product full-rank) | (b) determinant/Gram | **done/easy** | `detGram_lintegral_lt_top` etc. — fully banked |
| s=1 waist | (0) product-of-Morse | **EASY** | `sumSqND_box_lt_top` ×2 — composable now |
| s≥2 waist, literal SVD density | full rectangular SVD | **HEAVY** | needs Stiefel `V_s(ℝ^z)` + Haar-on-`O(s)` — **all absent**; ~research-level |
| s≥2 waist, cheapest | (c) deep-layer Schur-flag | **MODERATE-HEAVY** | Jacobian CoV + qPeel + shell cover banked; new = deep-layer Schur charts + recursion |

**Single hardest sub-brick:** the **s≥2 deep-layer corank chart's Jacobian** (whether the Vandermonde
density of the SVD route or the nested `det(pivot)`-power of the Schur route). Everything ELSE in the
cert's 6-step build-path is banked or elementary:
- step 1 (loss identity) — **BANKED** (`frobSq_mul_eq_sum_eigenvalues`).
- step 3 (A₀-frame integration) — **BANKED** (`exists_ortho_ext` + `lintegral_comp_orthRightMulₚ`).
- step 4 (exponent truncation + `Σmin(x,z+s+1−2j)=minAdm`) — **elementary** (`decide`-checkable per chain).
- step 5 (qPeel corner) — **BANKED** (`qPeelIntegral_lt_top`, complete, sorry-free).
- step 6 (shell cover) — **BANKED** (`singularShell*` + `lintegral_le_sum_finCover`).
- **step 2 (the density) — the ONE genuinely-new brick.**

**Recommendation to the base-case formaliser tide (follows the S1 build):**
1. Land the **s=1 leaf** first (route 0) — cheap, unblocks `(x,1,z)` immediately, exercises the qPeel/Morse
   plumbing on a case with no density.
2. Confirm the **non-waist** 3-width leaves via the banked determinant/Gram route (b).
3. For **s≥2 waists**, prototype route (c) (deep-layer Schur chart) as its OWN module BEFORE committing to
   the SVD density — it avoids the Stiefel/Haar Mathlib void entirely and reuses the banked Jacobian CoV.
   Escalate to the full SVD density only if the Schur-flag recursion's bookkeeping proves worse than the
   density's differential geometry (unlikely, given Mathlib has zero Stiefel/Haar scaffold).

## Close (reflection)
- **Most likely to advance the expedition:** the finding that steps 1,3,5,6 are already BANKED collapses
  the cert's "heaviest brick" from a 6-step build to a SINGLE density brick — and route (0) makes s=1
  waists immediate. The base case is far less monolithic than "heavy SVD CoV" suggested.
- **Most likely to break:** the claim that route (c) (deep-layer Schur-flag) is MODERATE-HEAVY rather
  than HEAVY — the deep-layer Schur charts may not transfer as cleanly from the banked FRONT-factor Schur
  machinery as the structural similarity suggests, and the flag-recursion bookkeeping over `s` levels is
  untested. Kill-condition: if a rank-2 (`s=2`, e.g. `(3,2,3)`) deep-layer Schur chart cannot be written
  as a `MeasureTheory.Function.Jacobian` CoV with a `det`-power Jacobian in one module, route (c) is not
  moderate and the SVD density (HEAVY) is forced.
- **Next computation that would clarify:** hand `(3,2,3)` (`x=3,s=2,z=3`, `minAdm=5`) to a pen-and-paper
  seat — write the explicit rank-1 deep-layer Schur chart for `A₁` (2×3) and its Jacobian, and check the
  charge adds to `½·minAdm(3,2,3)=5/2` via the banked qPeel `qPeelIntegral_lt_top`. That single worked
  chart decides route (c)'s difficulty label.
