# Thread 36 — the general achiever Jacobian determinant: route adjudication + build-ready spec

**Seat:** scout (reconnaissance / design). **Date:** 2026-06-26. **Branch:** `expedition/aoyagi-full`.
**Mandate:** adjudicate the route for the ∀M achiever-chart Jacobian determinant
`|det Dφ_{M,t}| = ∏_j |u_j|^{leafH j}` — the ONE residual gating the fully-general
`routeMCore_box_diverges_achiever` atom (`RouteMLayerCoverGE.lean:130`) — and hand the controller a
broken-down, bounded build plan, NOT a vague "multi-week."

The math is SETTLED and re-confirmed here independently (sympy + Mathlib-API check + a decorrelated
xhigh Codex consult, `codex/route-{prompt,answer}.md`). The headline reversal vs the prior wall
report (`be84b67b`): with the block-triangular collapse of the Schur differential, **the determinant
is no longer the blocker** — it is a bounded local theorem. The keystone has MOVED to the
flat-coordinate decoder identity. Route (c) with rate-transfer through `phiGen` is the recommendation.

---

## 0. The atom, and what is already banked

The general atom is one sorry:

    routeMCore_box_diverges_achiever (M) (hpos : 1 ≤ minAdm M) (c' : NNReal)
      (hc' : minAdm M / 2 ≤ c') (ε) (hε : 0 < ε) :
      ∫⁻ x in cubeBox (routeMAmbient M) ε, ofReal (|routeMCore M x|^(-c')) = ⊤

It reduces, M-agnostically and BANKED, to a `NodeAchieverChart M` bundle fed through
`routeMCore_box_diverges_of_nodeChart` (`NodeAchieverChart.lean`). The bundle's fields split by
det-dependence:

- **Banked det-FREE ∀M** (`RouteMGenLeafIntegrand.lean`): `leaf_integrand` (pure algebra in the rate
  identity `F∘φ = u_p²·V`, via `leaf_integrand_of_rate`), `VvalGen_nonneg` (sum of squares).
  Routine: `hpos`, `leafH_pivot`, `Umeas`, `image_subset`.
- **Banked rate identity ∀M** (`RouteMGenChartId.lean`): `routeMCore_phiGen : routeMCore M (phiGen …) =
  u²·VvalGen`, for the ABSTRACT chart `phiGen := paramsEquivFlat M ∘ chartParamsGen`. The chain RATE
  engine (`RouteMGenChain.lean`, `chainOfMt`) is fully landed.
- **The GATE — two coupled residuals**: (i) `NodeAchieverChart.phi` needs a full-ambient flat map
  `(Fin N → ℝ) → (Fin N → ℝ)`; `phiGen` has the radial `u` as a SCALAR argument + opaque block data,
  with no flat fderiv. (ii) the `cov` field needs `|det Dφ| = ∏_j |u_j|^{leafH j}` + injectivity.

`N := routeMAmbient M = flatDim M = ∑_s M_{s.castSucc}·M_{s.succ}`.

---

## 1. The MATH, re-confirmed (three decorrelated angles)

The cert's uniform construction (`threads/26-…/codex/genM-uniform-answer.md`) gives, with
`r_s = t_{s-1}−t_s`, `c_s = M_s − t_s`, `D = ∑_{s} r_s c_s = minAdm M`:

    |det Dφ_{M,t}| = |u|^{D−1} · ∏_{1≤s<L} ∏_{i=1}^{t_s} |q_{s,i}|^{r_s+c_s+2(t_s−i)}.

For (3,3,3,3): `|u|^5·|a|^4·|δ|^2·|b|^3`. The per-axis structure: the binding pivot `u` carries
`minAdm−1` (the only `k=1` loss axis ⟹ threshold `minAdm/2`); every `q` pivot is a `k=0` spectator
(`axisRatio = ⊤`, does not lower the threshold). This matches `NodeAchieverChart.leafH` exactly.

### 1a. The per-factor atomic det law (the keystone math) — INDEPENDENTLY verified

The cert's atomic Schur map (one boundary's frame), with `K : t×t` carrying its FULL `t²` free
entries:

    S(X,K,N,E) = [[K, K·N],[X·K, X·K·N + E]],   X:r×t, N:t×c, E:r×c.

Dimension: `#inputs = t² + rt + tc + rc = (t+r)(t+c) = #outputs` — a SQUARE chart of the
`(t+r)×(t+c)` matrix space. Claim:  `|det DS| = |det K|^{r+c}`.

I verified symbolically (`/tmp/my_schur_det.py`, decorrelated from the cert's own scripts) over
`(t,r,c) ∈ {(1,1,1),(2,1,1),(1,2,1),(1,1,2),(2,1,2),(2,2,1),(1,2,2),(2,2,2),(3,1,1),(3,2,1)}`:
det = `(det K)^{r+c}` in every case (sign irrelevant under `|·|`).

### 1b. THE STRUCTURAL COLLAPSE (the cost reversal) — the differential is block-lower-triangular

This is the finding that downgrades the det from "wall" to "bounded build." The differential
`DS` as a linear map on increments, in the natural block pairing
(output blocks `TL,TR,BL,BR` ↔ input blocks `dK,dN,dX,dE`):

    dA_TL = dK                                   diag block: dK ↦ dK          det 1
    dA_TR = K·dN              [+ dK·N]           diag block: dN ↦ K·dN        det (det K)^c
    dA_BL = dX·K             [+ X·dK]            diag block: dX ↦ dX·K        det (det K)^r
    dA_BR = dE  [+ X·dK·N + X·K·dN + dX·K·N]     diag block: dE ↦ dE          det 1

The bracketed terms are STRICTLY lower-triangular (`TR`/`BL`/`BR` read EARLIER input blocks), so
they don't touch the det. `|det DS| = 1·(det K)^c·(det K)^r·1 = |det K|^{r+c}`. Verified
block-lower-triangular AND det-correct symbolically (`/tmp/schur_factorization.py`) for all the (t,r,c)
above.

**Consequence:** the general det needs NO per-instance SCC grading `frameB`. The (3,3,3,3)'s literal
`frameB : Fin 27 → ℕ`, its hand 7×7 K/Kᵀ coupling block, and its 27-`have` injOn are hand-instance
machinery REPLACED by ONE block-triangular argument with two nontrivial diagonal blocks identified as
left-/right-mult-by-K.

### 1c. Full-chart spot check

(2,2,2), achiever `t=(2,1,0)`: full-chart Jacobian det has u-exponent `minAdm−1 = 2` and
`det / (u²·∏_s det(K_s)^{r_s+c_s})` is a unit (`/tmp/full_det_check.py`). (3,3,3,3) is cert-verified
end-to-end (`u⁵a⁴δ²b³`, `verify_codex_3333.py`).

---

## 2. The parametric Schur-frame det theorem (the EXACT Lean statement + Mathlib route)

State it MATRIX-INDEXED first (over abstract `Matrix (Fin r) (Fin c) ℝ` etc.), per Codex; flatten
only later. The atomic theorem:

```lean
/-- The Schur-frame map of one boundary, as a fderiv-bearing endomorphism of the (t+r)×(t+c) matrix
space (flattened to `Fin ((t+r)*(t+c)) → ℝ` at the use-site). Its abs-det is `|det K|^(r+c)`. -/
theorem schurFrame_abs_det {t r c : ℕ}
    (X : Matrix (Fin r) (Fin t) ℝ) (K : Matrix (Fin t) (Fin t) ℝ)
    (N : Matrix (Fin t) (Fin c) ℝ) :
    |LinearMap.det (schurFrameDeriv X K N).toLinearMap| = |K.det| ^ (r + c)
```

where `schurFrameDeriv X K N : E →ₗ[ℝ] E` (`E = the (dK,dN,dX,dE) increment space) is the linear
differential read off §1b. The PROOF:

1. **The block decomposition.** Express `schurFrameDeriv` in the basis ordered `(dK, dN, dX, dE)` as a
   `BlockTriangular` matrix over the 4-value grading `g : index → Fin 4` (`dK↦0, dN↦1, dX↦2, dE↦3`).
   The strictly-upper couplings vanish (§1b). Mathlib: `Matrix.BlockTriangular.det` (Block.lean:241)
   gives `det = ∏_{a ∈ image g} det(toSquareBlock g a)`.
2. **The four diagonal-block dets:**
   - `dK ↦ dK` block: identity, `det 1` (`Matrix.det_one` / `toSquareBlock` of `1`).
   - `dE ↦ dE` block: identity, `det 1`.
   - `dN ↦ K·dN` block (on `Matrix (Fin t) (Fin c)`): `det = (det K)^c`.
   - `dX ↦ dX·K` block (on `Matrix (Fin r) (Fin t)`): `det = (det K)^r`.
3. **The two nontrivial block dets** — the only genuinely new lemmas:

```lean
/-- Left-mult by K on the t×c matrix space has det (det K)^c. -/
theorem det_mulLeft_matrixSpace {t c : ℕ} (K : Matrix (Fin t) (Fin t) ℝ) :
    LinearMap.det (mulLeftLinear ℝ K : Matrix (Fin t) (Fin c) ℝ →ₗ[ℝ] _) = K.det ^ c
/-- Right-mult by K on the r×t matrix space has det (det K)^r. -/
theorem det_mulRight_matrixSpace {r t : ℕ} (K : Matrix (Fin t) (Fin t) ℝ) :
    LinearMap.det (mulRightLinear ℝ K : Matrix (Fin r) (Fin t) ℝ →ₗ[ℝ] _) = K.det ^ r
```

   **Two interchangeable Mathlib routes for these (both confirmed to exist):**

   - **Route via `LinearMap.det_pi` (Determinant.lean:388).** `Matrix (Fin t) (Fin c) ≃ₗ
     (Fin c → (Fin t → ℝ))` (columns); left-mult-by-K acts as `c` INDEPENDENT copies of `K.mulVecLin`
     (one per column). `det_pi (fun _ : Fin c => K.mulVecLin) = ∏_{Fin c} det(K.mulVecLin) =
     (det K)^c` (via `Finset.prod_const`), and `det(K.mulVecLin) = det(toLin' K) = K.det`
     (`LinearMap.det_toLin'`, Determinant.lean:221). Bridge the matrix-space ≃ columns with
     `LinearMap.det_conj` (Determinant.lean:299). Right-mult ↦ rows: same via
     `Matrix.transposeLinearEquiv` + `Matrix.det_transpose`, or `Matrix.vecMulLinear`.
   - **Route via `Matrix.det_kronecker` (Kronecker.lean:383):** `det (K ⊗ₖ 1_c) = (det K)^c · (det
     1_c)^t = (det K)^c`. Left-mult-by-K as a matrix on the flattened space IS `K ⊗ₖ 1` (up to a
     reindex / `det_submatrix_equiv_self`, Determinant/Basic.lean:223). `det_blockDiagonal`
     (Determinant/Basic.lean:610) is the same value the long way.

   **Recommendation:** the `det_pi` route is cleaner (no flatten-to-Kronecker reindex), and `det_pi`
   is purpose-built for exactly "block-diagonal copies of one endomorphism." Pin both with `example`
   blocks before committing (the §6 contracts).

The composed chart det then telescopes over the List of factors via the banked
`general_composed_clm_abs_det` (`RouteMAchieverGeneralDet.lean`), with per-factor abs-dets:

| factor (per boundary `s`, then global) | abs-det | Mathlib / banked |
|---|---|---|
| radial blow-up (1 factor) | `|u|^{D−1}` | `pivotBlowupOnDeriv_det` (S1G5Charts.lean:509) — BANKED |
| Schur frame `s` (`1≤s<L`) | `|det K_s|^{r_s+c_s}` | `schurFrame_abs_det` (NEW, §2) |
| LDU core `s` | `∏_i |q_{s,i}|^{2(t_s−i)}` | lower-triangular `det` (NEW, easy) |
| unit-triangular chaining `G_s⁻¹` | `1` | `det = 1`, unit-triangular |
| outer reshape `Q` (= `paramsEquivFlat ∘ pack`) | `1` | `measurePreserving` ⟹ `|det|=1` (banked pattern, `Q3333CLM_abs_det`) |

**The LDU core det:** `K_s = L_s·diag(q)·U_s` with `L_s,U_s` unit-triangular ⟹ `det K_s = ∏ q_{s,i}`,
so the SPECTATOR `|det K_s|^{r_s+c_s}` from the frame combines with the LDU-chart's own
`∏|q|^{2(t_s−i)}` Jacobian to give the boxed `∏|q_{s,i}|^{r_s+c_s+2(t_s−i)}`. NB: keeping `K`
FULL-free in the Schur frame (det `(det K)^{r+c}`) and treating the LDU `L diag(q) U → K`
parametrization as a SEPARATE lower-triangular factor is what makes each factor's det a clean
monomial — do NOT fold the LDU into the Schur block.

**Degenerate boundaries (must be in-scope, Codex-flagged):** `r_s=0` (rank stays, no residual block),
`c_s=0` (`Q_s = I`, factor passes through), `t_s=0`, both-zero (`C_s=K_s`). The det formula survives
(empty products = 1); Lean will not forgive a hidden `t−i ≥ 0` assumption — state the block lemmas
with `{t r c : ℕ}` fully general and let `Fin 0` collapse the empty blocks.

---

## 3. The flat-coordinatization / re-architecture (route c) + the rate transfer

### 3a. The chart as a List of full-ambient CLM factors

Build a NEW flat chart `φ_flat,{M,t} : (Fin N → ℝ) → (Fin N → ℝ)` (generalizing
`phi3333 = Q3333 ∘ Frame3333 ∘ Kparam3333` to opaque widths):

    φ_flat = Q ∘ (∏_factors)  where ∏_factors = radial ∘ (Schur_s)_{s} ∘ (Ldu_s)_s   (in flat coords)

Each factor is a full-ambient `(Fin N → ℝ) →L[ℝ] (Fin N → ℝ)` reading its block's coords from the `N`
flat slots and acting as identity elsewhere. The det telescopes by `general_composed_clm_abs_det`
over the per-factor list — BUT with the **prefix-pullback wrinkle** (Codex Q4, confirmed real): factor
`i`'s derivative is evaluated at `prefix_i u` (the output of earlier factors), exactly as
`Frame3333Deriv (Kparam3333 u)` in the (3,3,3,3) anchor. So the build needs a lightweight
`ChartFactor`/prefix-fold carrying `HasFDerivAt`, `InjOn`, and the per-factor abs-det AT the prefix.
The saving grace: each factor's `|det|` is a monomial in that factor's OWN coords, and the prefix
substitution pulls `|det K_s|` back to a fixed spectator monomial via a small `detK_s (prefix_s u) =
± monomial_s u` lemma — after which the final det rewrite is clean.

### 3b. The rate transfer (the keystone — Codex-confirmed route i)

Do NOT re-prove the rate on `φ_flat` from scratch (reruns the landed telescope/cast work
`prod_chartParamsGen_eq`/`dlnLoss_chartParamsGen`/`hWgen`/`hAgen`). Instead make the equality a
CONSTRUCTION INVARIANT: define a decoder `Bflat : (Fin N → ℝ) → GenBlk M t` reading the block data
from the flat coords, and prove

```lean
chartParamsFlat u = chartParamsGen (u p) M t (Bflat u) hle      -- the KEYSTONE identity
```

Then `phiFlat = phiGen (u p) M t (Bflat u) hle` is `congrArg (paramsEquivFlat M)`, and the BANKED
`routeMCore_phiGen` transfers the rate identity `routeMCore M (φ_flat u) = (u p)²·V` for free — no
re-run. **This is the single riskiest sub-piece** (Codex + my read agree): it is a per-layer
matrix equality through the dependent `Fin (M k)` / `Wext`/`Text` reindexing that `chartParamsGen`
carries (the `reindex_finCongr_mul` / `Fin.cast_eq_self` cast kernel — see `lean/CLAUDE.md`'s
dependent-dimension reassociation notes and `hAgen`'s `Fin.cast_eq_self` close).

The `leafH`-from-det summation: pull the per-factor monomials (`|u|^{D−1}`, the `|q|`-spectators)
into the single `∏_j |u_j|^{leafH j}` via `leafH p = minAdm−1` and `leafH q-axes = the
r+c+2(t−i)` exponents, `0` elsewhere — the `leafH3333_prod_eq` pattern at opaque widths (a
`Finset.prod_subset` over the support `{p} ∪ {q-axes}`).

### 3c. cov + injOn (structural, not 27-`have`)

- **injOn** (Codex Q3, confirmed): each factor is a diffeo on the sector where its `K_s` is invertible
  (`det K_s ≠ 0`); the radial on `u_p ≠ 0`. Compose via `Set.InjOn.comp` over the factor list, with
  the good set PREFIX-PULLED: `⋂_i prefix_i ⁻¹' good_i`, carrying `Set.MapsTo`. Per-factor injectivity
  is "this block is a bijection" — `schur_injOn_detK_ne_zero`, `ldu_injOn_q_ne_zero`, `radial_injOn`.
  No per-coordinate recovery.
- **cov**: `NodeAchieverChart.cov` exposes only `V \ {u_p = 0}`; the extra bad slices (`det K_s = 0`,
  `q_{s,i}=0`) are added back as null contributions exactly as `phi334_cov`/`phi3333_cov` do
  (`lintegral_image_eq_lintegral_abs_det_fderiv_mul` on the good set, then the null-slice add-back).
  Nullity of `{det K_s = 0}`: if `det K = ∏ q` (LDU form) it is a finite UNION of coordinate
  hyperplanes (`coordZero_null`); otherwise `MvPolynomial.ae_eval_ne_zero` (the
  `Core.MeasureTheory.PolynomialZeroSet` brick, already used for `Vval3333_ae_pos`).

---

## 4. The broken-down build plan (bounded sub-builds, dependency order)

Each is a scoped Lean lemma/file the controller can commission as a tide. Sizes are rough
elaboration-effort estimates (S ≈ a few lemmas / one short file; M ≈ a substantial file; the heavy
ones flagged).

**Phase A — the parametric Schur-frame det (network-free, matrix-indexed; NO `M`,`t` yet).**

- **A1** `det_mulLeft_matrixSpace` / `det_mulRight_matrixSpace` — `det = (det K)^c` / `(det K)^r` via
  `det_pi` + `det_toLin'` + `det_conj` (+ transpose for right). **Size S.** *Riskiest in Phase A* (the
  matrix-space ≃ columns conjugation; pin with `example` first). Confirm `det_pi`'s exact argument
  shape `LinearMap.pi (fun i => (f i).comp (proj i))` matches the columnwise action.
- **A2** `schurFrameDeriv` (the §1b differential as a CLM) + its `BlockTriangular` over the 4-grading
  + `schurFrame_abs_det : |det| = |det K|^{r+c}` assembled from A1 via `BlockTriangular.det`. Handle
  `r=0`/`c=0`/`t=0`. **Size M.** This is the parametric replacement for the entire (3,3,3,3) `frameB`
  + 7×7-K + `Frame3333Deriv_det` machinery.
- **A3** `lduCoreDeriv_det : |det| = ∏_i |q_i|^{2(t−i)}` (lower-triangular, the `Kparam3333Deriv_det`
  pattern at opaque `t`). **Size S.**

### Phase A build status (2026-06-26, `RouteMSchurFrameDet.lean`, branch `worktree-agent-ae0f9…`)

- **A1 LANDED, sorry-free, axiom-clean** `[propext, Classical.choice, Quot.sound]`.
  `det_mulLeft_matrixSpace = K.det^c`, `det_mulRight_matrixSpace = K.det^r`. Route as designed:
  `colEquiv` (matrix→columns, `transposeLinearEquiv ≫ ofLinearEquiv.symm`) + `det_conj` + `det_pi`
  + `det_toLin'`; right = transpose-conjugate of left. The conjugation identity closes by
  `Matrix.mul_apply` + `Matrix.mulVec` + `rfl` (no entrywise `ext` blow-up).
- **A2 KEYSTONE LANDED, sorry-free, axiom-clean.** The route was REVISED from the design's
  flattened `BlockTriangular`-over-`Fin 4` plan to a cleaner **abstract `lowerTri` nest** (Codex
  `a2-route-{prompt,answer}.md`): a reusable helper `lowerTri f g h : M×N →ₗ M×N`,
  `(m,n)↦(f m, g n + h m)`, with `lowerTri_det = f.det * g.det` proved via
  **`LinearMap.det_eq_det_mul_det`** on the invariant subspace `W = Submodule.snd` (restrict ≅ g via
  `sndEquiv`, quotient `(M×N)/W ≅ M` via `quotientEquivOfIsCompl` + `fstEquiv`). `schurFrameDeriv` is
  a 3-fold `lowerTri` nest over the four diagonal blocks (`id`, `mulLeftMat K`, `mulRightMat K`, `id`);
  `schurFrameDeriv_det = K.det^(r+c)` is one `rw` chain. NO `frameB`, NO 7×7 K-block, NO 27-`have`.
  Fully general `{t r c : ℕ}` (the `Fin 0` degenerate boundaries collapse for free).
  - **VALIDATED against the (3,3,3,3) hand det** (`schurFrame_abs_det_3333_boundary{1,2}[_value]`):
    boundary `s=1` (`t=2,r=c=1`) → `|det K|^2` = the hand `(z1·z4−z2·z3)^2 = (det K₁)^2` block;
    boundary `s=2` (`t=1,r=1,c=2`) → `|det K|^3` = the hand `z9^3 = |b|^3` block. The single uniform
    `|det Kₛ|^(rₛ+cₛ)` law reproduces BOTH hand K-blocks.
- **A3 LANDED IN FULL (diagonal-point AND general `L,U`), sorry-free, axiom-clean** `[propext,
  Classical.choice, Quot.sound]` (`RouteMSchurFrameDet.lean`, `DLNFibre.DLN.RLCT` namespace).
  Foundation: `LowIdx`/`UpIdx`/`LDUParam`, `lowMat`/`upMat` (+ linear `lowMatL`/`upMatL`),
  `assemble_apply`, **`matrixSplit : Matrix ≃ₗ LDUParam`**, the **multiplicity counts**
  `prod_lowIdx_col`/`prod_upIdx_row` (`∏_{j<i} q_j = ∏_j q_j^{t−1−j}` via `Fin.card_Ioi` +
  `Finset.card_bij` + `prod_fiberwise_of_maps_to` — the crux the coordinator flagged).
  - **`lduCoreDerivDiag_det : det = ∏_i q_i^{2(t−1−i)}`** (+ `_abs_det`) — the LDU Jacobian at the
    DIAGONAL point `L=U=1`, block-diagonal via `prodMap`. VALIDATED `..._3333_boundary1` (t=2 → `q_0^2`).
  - **`lduCoreDeriv_det : det = ∏_i q_i^{2(t−1−i)}`** (+ `_abs_det`, `_eq_diag`) — the GENERAL-`L,U`
    LDU Jacobian (`lduCoreDeriv = matrixSplit ∘ lduDerivMat`). Route as planned (Codex
    `a3-assembly-answer.md`): `lduDerivMat_factor` (`L'·N'·U' = M`, unit-factor recombination via
    `noncomm_ring` + the inverse cancellations); `matrixSplit_lduCoreMat` (`N'` read in LDU coords is
    block-diagonal `lowerBlock L'⁻¹ ⊕ id ⊕ upperBlock U'⁻¹`, via the triangularity helpers
    `lowProd_upper_zero`/`upProd_lower_zero`); `det E = 1` (the unit conjugation, via `LinearMap.det_conj`
    + A1 `det_mulLeft/Right_matrixSpace` + `unitLow/Up_det`); each block det `∏ q^{t−1−i}` via
    `lowerBlock_det`/`upperBlock_det` (`det_toMatrix'` + `det_of_lowerTriangular` over the row-major lex
    `lowOrd`/`upOrd`). The inverse-diagonal time-sink (`unitLow/Up_inv_diag`, `(L'⁻¹)_{ii}=1`) discharged
    via `blockTriangular_inv_of_blockTriangular` + the row-`i` sum collapse, as sketched. VALIDATED
    `lduCoreDeriv_det_3333_boundary1` (general point, t=2 → `q_0^2` = hand `Kparam3333Deriv_det`).
  - **BUILD-HYGIENE NOTE:** `scripts/lb` reported a stale-cache "Build completed" after an edit that
    didn't invalidate the olean (a `sorryAx` from the prior diagonal-`sorry` version persisted in the
    cache). Verified the true final state by forced recompile (append `#print axioms` → `lb`, shows
    `[propext, Classical.choice, Quot.sound]`, NO `sorryAx`) + `touch`-rebuild + `scripts/sorries`.
    Going forward: confirm any "sorry-free" claim with `#print axioms` (forces elaboration), not just
    `lb`'s exit status.

**Phase B — the flat chart + det telescope (network-aware).**

- **B1** `Bflat : (Fin N → ℝ) → GenBlk M t` decoder + the per-factor flat CLMs (radial reusing
  `pivotBlowupOn`; Schur/LDU from Phase A) + their `HasFDerivAt`. **Size M** (width bookkeeping).
- **B2** the `ChartFactor`/prefix-fold scaffold (carries `HasFDerivAt` + `InjOn` + abs-det-at-prefix)
  + `detK_s (prefix_s u) = ± monomial_s` pullback lemmas. **Size M.** *Riskiest in Phase B* (prefix
  evaluation across the dependent list).
- **B3** `phiFlat_abs_det : |det Dφ_flat u| = ∏_j |u_j|^{leafH j}` — telescope via
  `general_composed_clm_abs_det` over B1/B2, `leafH`-summation via the `leafH3333_prod_eq` pattern.
  **Size M.**

**Phase C — the rate transfer + the chart bundle (the keystone + assembly).**

- **C1 (KEYSTONE)** `chartParamsFlat_eq_chartParamsGen` → `phiFlat_eq_phiGen`, hence
  `routeMCore_phiFlat = (u p)²·V` from the banked `routeMCore_phiGen`. **Size M–L** (the dependent-`Fin`
  per-layer reindex equality; the `reindex_finCongr_mul` / `Fin.cast_eq_self` kernel). **Riskiest of
  the whole plan.**
- **C2** `phiFlat_injOn` (structural `InjOn.comp` over factors, prefix-pulled good set) +
  `phiFlat_cov` (c-o-v on the good set + null-slice add-back, `det K_s = 0` nullity). **Size M.**
- **C3** the achiever descent path `t` supply for the `leafH p = minAdm−1` profile
  (`RouteMLayerSplit.routeLayerAtlasAcc` achiever leaf — the minimiser, already landed for the rate;
  needs the `r_s,c_s` profile extracted) + `nodeChartGeneral : NodeAchieverChart M` assembly +
  `routeMCore_box_diverges_achiever` ∀M (discharge the `RouteMLayerCoverGE:130` sorry via
  `routeMCore_box_diverges_of_nodeChart`). **Size S** once C1/C2 land (the assembly is the banked
  `nodeChart3333` pattern).

**Keystone:** C1 (`chartParamsFlat = chartParamsGen`). **Riskiest sub-piece:** C1, then B2 (prefix
fold). The det itself (A1–A3, B3) is now bounded and routine.

**Critical-path ordering:** A1→A2 and A3 in parallel; B1 after A; B2 after B1; B3 after A2+A3+B2;
C1 in parallel with all of B (needs only the chart def + the banked rate engine); C2 after B2+C1;
C3 last. A green build per phase; the controller green-gates.

---

## 5. Cross-check against the (3,3,3,3) `RouteM3333Atom` template

The general parametric det must reproduce the concrete `Frame3333Deriv_det = z0⁵·z9³·(z1·z4−z2·z3)²`:

- (3,3,3,3): `t=(3,2,1,0)`, so per boundary `s=1`: `t_1=2, r_1 = t_0−t_1 = 1, c_1 = M_1−t_1 = 1`;
  `s=2`: `t_2=1, r_2 = 1, c_2 = 2`. The Schur frame at `s=1` contributes `|det K_1|^{r_1+c_1} =
  |det K_1|^2`; the `2×2` `K_1` is the `(3,3,3,3)`'s LDU core `K = [[a,aα],[γa, γaα+δ]]`, `det K_1 =
  a·δ`. So the frame gives `(a·δ)^2` — matching the hand 7×7 K/Kᵀ block's `(z1·z4−z2·z3)^2 = (a·δ)^2`
  (the `Frame3333Deriv` `z1·z4−z2·z3` IS `det K`). ✓
- The `z9³` block (the `b³` from boundary `s=2`'s `K_2` = the `1×1` `b`, with `r_2+c_2 = 3` ⟹
  `|det K_2|^3 = |b|^3`). ✓ — the general `|det K_s|^{r_s+c_s}` reproduces BOTH the 7×7 coupling
  block AND the `z9³` block as ONE uniform law (vs the two hand-built blocks).
- The `z0⁵` radial = `pivotBlowupOnDeriv_det` at `card = minAdm = 6` ⟹ `|u|^5`. ✓
- Composing with `Kparam3333Deriv_det = (x1)² = (a)²` (the LDU `∏|q|^{2(t−i)}` at `t_1=2`:
  `2(2−1)=2` on `q_1=a`, `0` on `q_2`): `|a|^2`. Total `|u|^5·(a·δ)^2·|b|^3·|a|^2 =
  |u|^5·|a|^4·|δ|^2·|b|^3`. ✓ EXACTLY `phi3333_abs_det`.

The general parametric det, instantiated at `(3,3,3,3)`/`t=(3,2,1,0)`, reproduces the hand det. This
is the validation gate for Phase A/B (build a `_3spec` specialization à la `routeMCore_phiGen_3spec`).

---

## 6. `example`-block contracts to pin BEFORE building (the uncertain Mathlib API)

Pin these as durable contracts (the `lean/CLAUDE.md` "pre-stage uncertain API" discipline):

1. `det_pi` argument shape: `(LinearMap.pi (fun i : Fin c => (K.mulVecLin).comp (LinearMap.proj i))).det
   = ∏ i, K.mulVecLin.det` — confirm it matches columnwise left-mult.
2. `LinearMap.det_toLin' : (Matrix.toLin' K).det = K.det` and `K.mulVecLin = Matrix.toLin' K` (a `rfl`
   or `Matrix.mulVecLin_eq_toLin'`-style fact — verify the exact name).
3. `LinearMap.det_conj` for the matrix-space ≃ `(Fin c → Fin t → ℝ)` columns equiv.
4. `Matrix.det_kronecker` (fallback) + `Matrix.det_submatrix_equiv_self` for the flatten reindex.
5. `Matrix.BlockTriangular.det` over a `Fin 4` grading (the §1b 4-block) — the `frameB`-free analog.

All five lemma NAMES are confirmed to exist in the v4.29 Mathlib pin (`grep` over
`.lake/packages/mathlib/`); the contracts pin their exact TYPES/argument-order.

**A1 de-risked by standalone elaboration** (`/tmp/det_mulleft_check2.lean`, `/tmp/det_conj_check.lean`,
Mathlib-only, NOT a project build — elaborated clean against the v4.29 pin):
- `LinearMap.det (K.mulVecLin) = K.det` closes by `rw [show K.mulVecLin = Matrix.toLin' K from rfl,
  LinearMap.det_toLin']` (`mulVecLin = toLin'` is `rfl`). ✓
- `LinearMap.det_pi (fun _ : Fin c => K.mulVecLin) : (LinearMap.pi (fun i => (K.mulVecLin).comp
  (LinearMap.proj i))).det = ∏ _i : Fin c, det (K.mulVecLin)` typechecks as-is. ✓
- the collapse `∏_{Fin c} K.det = K.det^c` by `Finset.prod_const, Finset.card_univ, Fintype.card_fin`. ✓
- `LinearMap.det_conj f e` for the matrix-space ≃ `(Fin c → Fin t → ℝ)` columns conjugation
  typechecks. ✓
So `det_mulLeft_matrixSpace = (det K)^c` is `det_conj` (to columns) + `det_pi` + the collapse — a
short, confirmed-elaborating chain. The ONLY un-pinned piece is the explicit column equiv
`Matrix (Fin t) (Fin c) ℝ ≃ₗ (Fin c → Fin t → ℝ)` and the proof that left-mult conjugates to the
block-diag pi map (a `LinearMap.ext` + `Matrix.mulVecLin_apply` entrywise check) — bounded.

---

## 7. Honest cost & the route decision

- **Route (a)** (compute det directly from abstract `chainOfMt`): REJECTED. `phiGen`'s layers are
  abstract `chainA`/`chainQ` reindexes with a scalar radial — there is no flat fderiv to
  differentiate; reifying `GenBlk` as source coords IS the coordinatization problem under another
  name (Codex Q1 + my read agree).
- **Route (c)** with **rate-transfer through `phiGen` (c-i)**: RECOMMENDED. The det collapses to a
  bounded local theorem (§1b/§2); the rate is free via the decoder identity; injOn/cov are
  structural. The work concentrates in ONE keystone (C1) + one scaffold (B2).
- **vs the prior "multi-week" framing** (`be84b67b`): that estimate predated the block-triangular
  collapse, which removes the per-instance `frameB`/7×7-K/27-`have` machinery the wall report cited as
  the multi-week cost. The residual is bounded and broken into the Phase A/B/C lemmas above. It is
  more than a single tide (≈ 8–10 scoped lemmas across 3 phases), but it is a CHARGEABLE sequence of
  bounded builds, not an open design problem.

**One-line recommendation:** route (c), rate-transfer via `phiGen`; keystone =
`chartParamsFlat_eq_chartParamsGen`; the parametric Schur det (`schurFrame_abs_det`, block-triangular,
`det_pi`-based) is the now-bounded engine, not the blocker.
