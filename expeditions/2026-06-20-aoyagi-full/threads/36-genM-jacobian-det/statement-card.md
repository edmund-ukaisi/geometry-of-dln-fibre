# Statement card — Phase A: the parametric Schur-frame Jacobian determinant engine

The network-free, matrix-indexed determinant engine (Phase A of thread 36), replacing the per-instance
`(3,3,3,3)` hand machinery (`frameB`, the 7×7 K/Kᵀ coupling block, the 27-`have` `injOn`) with one
uniform block-triangular collapse `|det DS| = |det K|^(r+c)`.

- **File:** `lean/DLNFibre/DLN/RLCT/Validate/RouteMSchurFrameDet.lean`
  (commit `f7033fe2`, branch `worktree-agent-ae0f9bee9ece28c91`, off `expedition/aoyagi-full`).
- **Status.** A1 + A2 + validation **LANDED sorry-free, axiom-clean** `[propext, Classical.choice,
  Quot.sound]`. Green build (`scripts/lb`, 2188 jobs, zero warnings). **A3 NOT built** — route validated,
  re-rated MEDIUM; roadmapped in `design.md` §4 "Phase A build status". NOT yet wired into the
  aggregator `DLNFibre.lean` (single-writer; controller to add the import).

## Theorems (the landed Phase A engine)

> **`lowerTri_det (f : M →ₗ[ℝ] M) (g : N →ₗ[ℝ] N) (h : M →ₗ[ℝ] N) :`**
> **`  LinearMap.det (lowerTri f g h) = f.det * g.det`**  (`M`, `N` finite-dim over `ℝ`)
>
> - **Content.** The 2-block lower-triangular endomorphism `(m,n) ↦ (f m, g n + h m)` of `M × N` has
>   determinant `f.det · g.det` — the off-diagonal coupling `h` contributes nothing. The reusable
>   keystone helper.
> - **Proof.** `LinearMap.det_eq_det_mul_det` on the invariant subspace `W = Submodule.snd ≅ N`
>   (restrict acts as `g`, via `sndEquiv`), quotient `(M×N)/W ≅ M` (acts as `f`, via
>   `quotientEquivOfIsCompl (snd) (fst) ≫ fstEquiv`). The restrict/quotient identifications are
>   `det_conj` conjugations whose underlying maps match by a short `ext`/`change`.

> **`det_mulLeft_matrixSpace (K : Matrix (Fin t) (Fin t) ℝ) :`**
> **`  LinearMap.det (mulLeftMat (c := c) K) = K.det ^ c`**   (A1, left)
> **`det_mulRight_matrixSpace (K : Matrix (Fin t) (Fin t) ℝ) :`**
> **`  LinearMap.det (mulRightMat (r := r) K) = K.det ^ r`**   (A1, right)
>
> - **Content.** Left-mult `X ↦ K·X` on `Matrix (Fin t) (Fin c) ℝ` has det `K.det^c`; right-mult
>   `X ↦ X·K` on `Matrix (Fin r) (Fin t) ℝ` has det `K.det^r`. The two nontrivial diagonal blocks of
>   the Schur frame.
> - **Proof.** Conjugate by `colEquiv` (matrix→columns, `transposeLinearEquiv ≫ ofLinearEquiv.symm`)
>   to the block-diagonal of `c` copies of `K.mulVecLin`; `det_pi` + `det_toLin'` collapse to
>   `K.det^c`. Right = transpose-conjugate of left (`Matrix.det_transpose`).

> **`schurFrameDeriv (X : Matrix (Fin r)(Fin t) ℝ)(K : Matrix (Fin t)(Fin t) ℝ)(N : Matrix (Fin t)(Fin c) ℝ)`**
> **`  : SchurInc t r c →ₗ[ℝ] SchurInc t r c`** — the Schur-frame differential `DS`:
> `(dK, dN, dX, dE) ↦ (dK, K·dN + dK·N, dX·K + X·dK, dE + X·dK·N + X·K·dN + dX·K·N)`
> (confirmed by `schurFrameDeriv_apply`).
>
> **`schurFrameDeriv_det : LinearMap.det (schurFrameDeriv X K N) = K.det ^ (r + c)`**  (A2 keystone)
> **`schurFrame_abs_det : |LinearMap.det (schurFrameDeriv X K N)| = |K.det| ^ (r + c)`**  (A2, abs form)
>
> - **Content.** The differential of the boundary Schur frame `S(X,K,N,E) = [[K, K·N],[X·K, X·K·N+E]]`
>   has `|det| = |det K|^(r+c)`. The parametric, route-free replacement for the entire `(3,3,3,3)` hand
>   `Frame3333Deriv_det` machinery. Fully general `{t r c : ℕ}` (`Fin 0` collapses degenerate
>   boundaries `r=0`/`c=0`/`t=0`).
> - **Proof.** `schurFrameDeriv` is a 3-fold `lowerTri` nest over the four diagonal blocks (`id`,
>   `mulLeftMat K`, `mulRightMat K`, `id`); `schurFrameDeriv_det` is one `rw` chain through
>   `lowerTri_det` + A1 + `det_id` + `ring`.

## Validation (against the `(3,3,3,3)` hand det `Frame3333Deriv_det`)

`Frame3333Deriv_det = (z 0)^5 · (z 9)^3 · (z 1·z 4 − z 2·z 3)^2` (`RouteM3333Atom`). With
`t = (3,2,1,0)`, the general law `|det Kₛ|^(rₛ+cₛ)` reproduces both K-blocks:

> **`schurFrame_abs_det_3333_boundary1 : |det (schurFrameDeriv X K N)| = |K.det| ^ 2`**
> (`t=2, r=c=1`; with `det K₁ = a·δ` this is the hand `(z1·z4−z2·z3)^2 = (det K₁)^2` block.)
> **`schurFrame_abs_det_3333_boundary2 : |det (schurFrameDeriv X K N)| = |K.det| ^ 3`**
> **`schurFrame_abs_det_3333_boundary2_value : |det (schurFrameDeriv X [[b]] N)| = |b| ^ 3`**
> (`t=1, r=1, c=2`; `K₂ = [[b]]`, `det K₂ = b = z 9`, the hand `(z 9)^3 = |b|^3` block.)

The two hand K-blocks (the 7×7 K/Kᵀ coupling AND the `z9³`) both arise from the SINGLE uniform
`|det Kₛ|^(rₛ+cₛ)` law. The `(z 0)^5` factor is the radial blow-up, not part of the Schur frame.

## Caveats / scope

- **Not wired into the aggregator** (`DLNFibre.lean` is single-writer). Controller to add
  `import DLNFibre.DLN.RLCT.Validate.RouteMSchurFrameDet`.
- **A3 (`lduCore_det`) deferred** — see `design.md` §4 "Phase A build status" for the validated route
  and the precise residual (≈5 lemmas, the multiplicity-count being the crux). A3 does not gate A2.
- A2 is the **per-boundary** Schur-frame factor det. The full chart det (Phases B/C) telescopes these
  over the boundary list with the radial + LDU factors; that is downstream of this thread.
