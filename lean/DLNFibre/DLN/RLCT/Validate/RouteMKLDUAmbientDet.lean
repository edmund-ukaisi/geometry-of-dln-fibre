import DLNFibre.DLN.RLCT.Validate.RouteMInteriorLiveDet

/-!
# `RouteMKLDUAmbientDet` — H2b-i: the full-ambient `kLDU` lens Jacobian abs-det (SKELETON)

The full-ambient determinant of the K-slot LDU lens `kLDU`'s Fréchet Jacobian:

  `|det (fderiv ℝ (kLDU M t ha) y)| = ∏_{k} ∏_{i : Fin t_k} |q_{k,i}|^{2(t_k − 1 − i)}`,
  `q_{k,i} = (matrixSplit (Matrix.of (readK M t ha y k))).2.1 i`.

`kLDU` acts as the per-matrix lens `kLens` on each per-boundary K-core BLOCK of coordinates and as
the IDENTITY on every spectator coordinate (X/N/E roles, lift slots, radial axis) — the blocks are the
disjoint K-core coordinate sets indexed by `chartIdxEquiv`. So the ambient Jacobian is BLOCK-DIAGONAL
under the `chartIdxEquiv` reindex, and its determinant is the product of the per-K-core `kLens` block
dets (banked `kLens_abs_det`, `RouteMInteriorLiveDet`) over the diagonal LDU pivots, spectators
contributing `det = 1`.

## Route (Codex xhigh verified, `threads/genm-h2bdet/codex/ambient-det-answer.md`)

1. reindex `Fin (routeMAmbient M) → ℝ` to `ChartIdx M (tDesc M t) → ℝ` via
   `LinearEquiv.funCongrLeft ℝ ℝ chartIdxEquiv.symm`; `LinearMap.det_conj` ⟹ `det (fderiv kLDU y) =
   det Dchart`, `Dchart` the conjugated map on `ChartIdx → ℝ`.
2. `A := LinearMap.toMatrix' Dchart` is `BlockTriangular Sigma.fst` (cross-boundary fderiv entries
   vanish: the boundary-`k` output K-coordinate depends only on the boundary-`k` input K-coordinates).
   `Matrix.BlockTriangular.det_fintype` ⟹ `A.det = ∏ k : Fin L, (A.toSquareBlock Sigma.fst k).det`.
3. per-boundary block `toSquareBlock k` ≅ `kLens (readK y k)` on the K-core ⊕ `id` on the spectators
   (via `{c : ChartIdx // c.1 = k} ≃ (schur ⊕ lift)` then the K-core/spectator split);
   `LinearMap.det_prodMap` + `LinearMap.det_id` + the banked `kLens_abs_det` ⟹ the per-core monomial.

## Status (LANDED — sorry-free)

`kLDU_ambient_abs_det` is PROVED sorry-free (the route below, executed; genm-ambdet 2026-06-30).
Axiom-clean target `[propext, Classical.choice, Quot.sound]`.

**Locked target sig**: `kLDU_ambient_abs_det` — the RHS keyed to `readK M t ha y k` (the K-core read at
`y`), `q = (matrixSplit (Matrix.of (readK … y k))).2.1` the LDU diagonal pivots.

**Banked input consumed**: `kLens_abs_det` (`RouteMInteriorLiveDet`, axiom-clean) + `kLens_hasFDerivAt`.

## Proof structure (the Codex-verified BlockTriangular route, executed)

1. **Per-output derivative** (`fderiv_kLDU_apply`, `hasFDerivAt_kLDU_out_K`, `kLDU_out_K_fun`,
   `kLDU_out_id_fun`): a K-output reads only its boundary's K-slots via `readKL`; spectators are the
   identity arm.
2. **Conjugation** (`ambChartMat`, `ambChartMat_apply`): reindex `Fin N → ℝ` to `ChartIdx → ℝ` by
   `funCongrLeft ℝ ℝ chartIdxEquiv.symm`, `det_conj` + `det_toMatrix'` ⟹ a matrix det.
3. **Block-triangular** (`fderiv_kLDU_cross_boundary`, `ambChartMat_blockTriangular`): cross-boundary
   entries vanish (readK kills the off-boundary basis vector); `BlockTriangular.det_fintype` ⟹ the
   per-boundary product.
4. **Per-block det** (`toSquareBlock_abs_det`): reindex the boundary-`k` block by `fiberSplit` (K-role
   first, `fiberEquiv` + `frameSplitEquiv` + the `kFront` reassoc); the spectator (X/N/E/lift) sub-block
   is the identity (`fiberSplit_symm_inr_id`, `ambChartMat_id_entry`), `det_eq_toBlocks_of_lower_zero`
   peels it; the K-block is `fderiv kLens (readK y k)` in the std matrix basis (`KBlock_det_eq` via
   `LinearMap.det_toMatrix` + `Matrix.det_reindex_self`); then the banked `kLens_abs_det`.

`LinearMap.det_pi` does NOT apply (homogeneous; dependent K-core widths) — `BlockTriangular.det_fintype`
is the route. All Mathlib names verified at v4.29.
-/

open Matrix
open scoped BigOperators

namespace DLNFibre.DLN.RLCT

variable {L : ℕ}

/-! ## Differentiability of the lens (local copies, decoupled from the contract) -/

/-- **`kLens` is differentiable** (file-private copy; the contract owns the public `differentiable_kLens`). -/
private theorem differentiable_kLens {τ : ℕ} : Differentiable ℝ (kLens (t := τ)) := by
  have hlduc : Differentiable ℝ (lduCoreMap (t := τ)) :=
    fun z => (lduCoreMap_hasFDerivAt z).differentiableAt
  intro K
  unfold kLens
  exact (matrixSplit.symm.toContinuousLinearEquiv.differentiable _).comp K
    ((hlduc _).comp K (matrixSplit.toContinuousLinearEquiv.differentiable K))

/-- **`kLDU` is differentiable** (file-private copy; the contract owns the public `differentiable_kLDU`). -/
private theorem differentiable_kLDU (M t : Fin (L + 1) → ℕ) (ha : StructAdm M t) :
    Differentiable ℝ (kLDU M t ha) := by
  apply differentiable_pi.mpr
  intro q
  unfold kLDU
  split
  · rename_i k s heq
    split
    · rename_i qK hfeq
      have hrk : Differentiable ℝ
          (fun x : Fin (routeMAmbient M) → ℝ => Matrix.of (readK M t ha x k)) := by
        apply differentiable_pi.mpr; intro i; apply differentiable_pi.mpr; intro j
        exact differentiable_apply _
      have hcomp : Differentiable ℝ
          (fun x : Fin (routeMAmbient M) → ℝ => kLens (Matrix.of (readK M t ha x k))) :=
        fun x => (differentiable_kLens _).comp x (hrk x)
      exact differentiable_pi.mp (differentiable_pi.mp hcomp (finProdFinEquiv.symm qK).1)
        (finProdFinEquiv.symm qK).2
    · exact differentiable_apply _
  · exact differentiable_apply _

/-! ## The linear K-core reader + the matrix-entry CLM -/

/-- The matrix entry-`(i,j)` read as a continuous linear map (`Matrix` is reducibly `m → n → R`). -/
noncomputable def matEntryCLM (τ : ℕ) (i j : Fin τ) : Matrix (Fin τ) (Fin τ) ℝ →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin τ => ℝ) j).comp
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin τ => Fin τ → ℝ) i)

@[simp] theorem matEntryCLM_apply (τ : ℕ) (i j : Fin τ) (A : Matrix (Fin τ) (Fin τ) ℝ) :
    matEntryCLM τ i j A = A i j := rfl

/-- `readK · k` as a continuous linear map in the flat vector (it reads single flat coords). -/
noncomputable def readKL (M t : Fin (L + 1) → ℕ) (ha : StructAdm M t) (k : Fin L) :
    (Fin (routeMAmbient M) → ℝ) →ₗ[ℝ]
      Matrix (Fin (Text M t (k.val + 2))) (Fin (Text M t (k.val + 2))) ℝ where
  toFun x := Matrix.of (readK M t ha x k)
  map_add' x y := by ext i j; simp [readK, Pi.add_apply]
  map_smul' a x := by ext i j; simp [readK, Pi.smul_apply]

@[simp] theorem readKL_apply (M t : Fin (L + 1) → ℕ) (ha : StructAdm M t) (k : Fin L)
    (x : Fin (routeMAmbient M) → ℝ) :
    readKL M t ha k x = Matrix.of (readK M t ha x k) := rfl

/-! ## The per-output Fréchet derivative of `kLDU`

`(fderiv kLDU y) v q = fderiv (fun x => kLDU x q) y v` (per-output projection). At a K-output `q`
(boundary `k`, matrix index `ij = finProdFinEquiv.symm qK`) the value is the entry-`ij` read of
`(fderiv kLens (readK y k)) (readKL k v)`; at every other output it is `v q` (the identity arm). -/

/-- `(fderiv kLDU y) v q = fderiv (fun x => kLDU x q) y v`. -/
theorem fderiv_kLDU_apply (M t : Fin (L + 1) → ℕ) (ha : StructAdm M t)
    (y v : Fin (routeMAmbient M) → ℝ) (q : Fin (routeMAmbient M)) :
    (fderiv ℝ (kLDU M t ha) y) v q = (fderiv ℝ (fun x => kLDU M t ha x q) y) v := by
  rw [fderiv_pi (fun i => (differentiable_pi.mp (differentiable_kLDU M t ha) i).differentiableAt)]
  rfl

/-- The per-K-output derivative: at output `q` decoding to boundary `k`, K-role index `qK`
(`ij = finProdFinEquiv.symm qK`), `fun x => kLDU x q = (entry ij) ∘ kLens ∘ (readKL k)`, so its
fderiv is `matEntryCLM ij ∘ (fderiv kLens (readK y k)) ∘ readKL k`. -/
theorem hasFDerivAt_kLDU_out_K (M t : Fin (L + 1) → ℕ) (ha : StructAdm M t) (k : Fin L)
    (i j : Fin (Text M t (k.val + 2))) (y : Fin (routeMAmbient M) → ℝ) :
    HasFDerivAt (fun x => kLens (Matrix.of (readK M t ha x k)) i j)
      ((matEntryCLM (Text M t (k.val + 2)) i j).comp
        ((fderiv ℝ (kLens (t := Text M t (k.val + 2))) (Matrix.of (readK M t ha y k))).comp
          (readKL M t ha k).toContinuousLinearMap))
      y := by
  have hread : HasFDerivAt (fun x => Matrix.of (readK M t ha x k))
      (readKL M t ha k).toContinuousLinearMap y :=
    (readKL M t ha k).toContinuousLinearMap.hasFDerivAt
  have hkl : HasFDerivAt (kLens (t := Text M t (k.val + 2)))
      (fderiv ℝ (kLens (t := Text M t (k.val + 2))) (Matrix.of (readK M t ha y k)))
      ((readKL M t ha k).toContinuousLinearMap y) :=
    (kLens_hasFDerivAt _).differentiableAt.hasFDerivAt
  exact (matEntryCLM (Text M t (k.val + 2)) i j).hasFDerivAt.comp y (hkl.comp y hread)

/-- **The K-reader kills a single basis vector supported off boundary `k`** — `readK x k` reads only
flat coords in boundary-`k`'s chart slot (`chartIdxEquiv.symm ⟨k, …⟩`), so the standard basis vector
`Pi.single (chartIdxEquiv.symm c') 1` at any `c'` with `c'.1 ≠ k` is read as `0`. -/
theorem readKL_single_off_boundary (M t : Fin (L + 1) → ℕ) (ha : StructAdm M t) (k : Fin L)
    (c' : ChartIdx M (tDesc M t)) (hne : c'.1 ≠ k) :
    readKL M t ha k
        (Pi.single ((chartIdxEquiv M (tDesc M t) ha.h0 ha.hc ha.hL).symm c') (1 : ℝ)) = 0 := by
  ext i j
  rw [readKL_apply, Matrix.of_apply, readK, Matrix.zero_apply]
  apply Pi.single_eq_of_ne
  intro hc
  apply hne
  have hci := (chartIdxEquiv M (tDesc M t) ha.h0 ha.hc ha.hL).symm.injective hc
  exact (congrArg Sigma.fst hci).symm

/-- The K-output function identity: at chart index `⟨k, inl s⟩` whose frame-split decode is the K-role
`inl(inl(inl qK))`, `fun x => kLDU x (cf.symm ⟨k, inl s⟩) = fun x => kLens (readK x k) ij.1 ij.2`
(`ij = finProdFinEquiv.symm qK`). -/
theorem kLDU_out_K_fun (M t : Fin (L + 1) → ℕ) (ha : StructAdm M t)
    (k : Fin L) (s : Fin (schurDim M (tDesc M t) k.val))
    {qK : Fin (Text M t (k.val + 1 + 1) * Text M t (k.val + 1 + 1))}
    (hfs : frameSplitEquiv M t (k.val + 1) (ha.hdesc k.val k.isLt) (ha.hub k.val) s
      = Sum.inl (Sum.inl (Sum.inl qK))) :
    (fun x => kLDU M t ha x
        ((chartIdxEquiv M (tDesc M t) ha.h0 ha.hc ha.hL).symm ⟨k, Sum.inl s⟩))
      = (fun x => kLens (Matrix.of (readK M t ha x k))
          (finProdFinEquiv.symm qK).1 (finProdFinEquiv.symm qK).2) := by
  funext x
  show kLDU M t ha x ((chartIdxEquiv M (tDesc M t) ha.h0 ha.hc ha.hL).symm ⟨k, Sum.inl s⟩) = _
  rw [kLDU]
  simp only [Equiv.apply_symm_apply, hfs]
  rfl

/-- The identity-arm function identity: at any chart index `c` that is NOT a K-role output,
`fun x => kLDU x (cf.symm c) = fun x => x (cf.symm c)`. The hypothesis `hid` packages the
frame-split-decode-is-not-K (or lift) condition as a pointwise equality. -/
theorem kLDU_out_id_fun (M t : Fin (L + 1) → ℕ) (ha : StructAdm M t)
    (c : ChartIdx M (tDesc M t))
    (hid : ∀ x, kLDU M t ha x ((chartIdxEquiv M (tDesc M t) ha.h0 ha.hc ha.hL).symm c)
      = x ((chartIdxEquiv M (tDesc M t) ha.h0 ha.hc ha.hL).symm c)) :
    (fun x => kLDU M t ha x ((chartIdxEquiv M (tDesc M t) ha.h0 ha.hc ha.hL).symm c))
      = (fun x => x ((chartIdxEquiv M (tDesc M t) ha.h0 ha.hc ha.hL).symm c)) :=
  funext hid

/-- **Cross-boundary vanishing** — the derivative of `kLDU`'s output coordinate at chart index `c`,
in the direction of the basis vector at chart index `c'`, is `0` whenever `c'.1 ≠ c.1`. The
boundary-`c.1` K-output reads only boundary-`c.1` K-slots (`readKL_single_off_boundary`); every
identity-arm output reads only the coordinate `c` itself (`c ≠ c'` since their fst differs). -/
theorem fderiv_kLDU_cross_boundary (M t : Fin (L + 1) → ℕ) (ha : StructAdm M t)
    (y : Fin (routeMAmbient M) → ℝ) (c c' : ChartIdx M (tDesc M t)) (hne : c'.1 ≠ c.1) :
    (fderiv ℝ (kLDU M t ha) y)
        (Pi.single ((chartIdxEquiv M (tDesc M t) ha.h0 ha.hc ha.hL).symm c') (1 : ℝ))
        ((chartIdxEquiv M (tDesc M t) ha.h0 ha.hc ha.hL).symm c) = 0 := by
  set cf := chartIdxEquiv M (tDesc M t) ha.h0 ha.hc ha.hL with hcf
  rw [fderiv_kLDU_apply]
  -- identity-arm vanishing: the projection of the off-`c` basis vector is `0`
  have hid_vanish : (fderiv ℝ (fun x => x (cf.symm c)) y)
      (Pi.single (cf.symm c') (1 : ℝ)) = 0 := by
    rw [(hasFDerivAt_apply (cf.symm c) y).fderiv, ContinuousLinearMap.proj_apply]
    exact Pi.single_eq_of_ne (fun hc => hne (congrArg Sigma.fst (cf.symm.injective hc.symm))) 1
  obtain ⟨k, s | s⟩ := c
  · match hfs : frameSplitEquiv M t (k.val + 1) (ha.hdesc k.val k.isLt) (ha.hub k.val) s with
    | Sum.inl (Sum.inl (Sum.inl qK)) =>
      rw [kLDU_out_K_fun M t ha k s hfs, (hasFDerivAt_kLDU_out_K M t ha k _ _ y).fderiv]
      have hz : (readKL M t ha k).toContinuousLinearMap (Pi.single (cf.symm c') (1 : ℝ)) = 0 := by
        rw [LinearMap.coe_toContinuousLinearMap']
        exact readKL_single_off_boundary M t ha k c' hne
      simp only [ContinuousLinearMap.comp_apply, hz, ContinuousLinearMap.map_zero,
        matEntryCLM_apply, Matrix.zero_apply]
    | Sum.inl (Sum.inl (Sum.inr qK)) =>
      rw [kLDU_out_id_fun M t ha ⟨k, Sum.inl s⟩
        (fun x => by rw [kLDU]; simp only [hcf, Equiv.apply_symm_apply, hfs])]; exact hid_vanish
    | Sum.inl (Sum.inr qK) =>
      rw [kLDU_out_id_fun M t ha ⟨k, Sum.inl s⟩
        (fun x => by rw [kLDU]; simp only [hcf, Equiv.apply_symm_apply, hfs])]; exact hid_vanish
    | Sum.inr qK =>
      rw [kLDU_out_id_fun M t ha ⟨k, Sum.inl s⟩
        (fun x => by rw [kLDU]; simp only [hcf, Equiv.apply_symm_apply, hfs])]; exact hid_vanish
  · rw [kLDU_out_id_fun M t ha ⟨k, Sum.inr s⟩
      (fun x => by rw [kLDU]; simp only [hcf, Equiv.apply_symm_apply])]; exact hid_vanish

/-! ## Block-diagonal determinant helpers + the boundary-`k` fiber equiv -/

/-- A matrix over `α ⊕ β` with zero lower-left block has det = product of diagonal-block dets. -/
theorem det_eq_toBlocks_of_lower_zero {α β : Type} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] (B : Matrix (α ⊕ β) (α ⊕ β) ℝ)
    (h : ∀ i j, B (Sum.inr i) (Sum.inl j) = 0) :
    B.det = (B.toBlocks₁₁).det * (B.toBlocks₂₂).det := by
  have hB : B = Matrix.fromBlocks B.toBlocks₁₁ B.toBlocks₁₂ 0 B.toBlocks₂₂ := by
    rw [← Matrix.fromBlocks_toBlocks B]
    congr 1
    ext i j; exact h i j
  conv_lhs => rw [hB]
  rw [Matrix.det_fromBlocks_zero₂₁]

/-- The boundary-`k` fiber of `ChartIdx`: `{c // c.1 = k} ≃ (Fin (schurDim k) ⊕ Fin (liftDim k))`. -/
def fiberEquiv (M : Fin (L + 1) → ℕ) (τ : ℕ → ℕ) (k : Fin L) :
    {c : ChartIdx M τ // c.1 = k} ≃ (Fin (schurDim M τ k.val) ⊕ Fin (liftDim M τ k.val)) where
  toFun c := by rcases c with ⟨⟨k', x⟩, hk⟩; exact hk ▸ x
  invFun s := ⟨⟨k, s⟩, rfl⟩
  left_inv := by rintro ⟨⟨k', x⟩, rfl⟩; rfl
  right_inv := by intro s; rfl

@[simp] theorem fiberEquiv_symm_apply (M : Fin (L + 1) → ℕ) (τ : ℕ → ℕ) (k : Fin L)
    (s : Fin (schurDim M τ k.val) ⊕ Fin (liftDim M τ k.val)) :
    (fiberEquiv M τ k).symm s = ⟨⟨k, s⟩, rfl⟩ := rfl

/-- Reassociate `((((A⊕X)⊕N)⊕E)⊕Lf)` to `A ⊕ (((X⊕N)⊕E)⊕Lf)` (pull the deep-left `A` to front). -/
def kFront (A X N E Lf : Type) :
    (((((A ⊕ X) ⊕ N) ⊕ E) ⊕ Lf)) ≃ (A ⊕ ((((X ⊕ N) ⊕ E) ⊕ Lf))) where
  toFun w := match w with
    | Sum.inl (Sum.inl (Sum.inl (Sum.inl a))) => Sum.inl a
    | Sum.inl (Sum.inl (Sum.inl (Sum.inr x))) => Sum.inr (Sum.inl (Sum.inl (Sum.inl x)))
    | Sum.inl (Sum.inl (Sum.inr n)) => Sum.inr (Sum.inl (Sum.inl (Sum.inr n)))
    | Sum.inl (Sum.inr e) => Sum.inr (Sum.inl (Sum.inr e))
    | Sum.inr l => Sum.inr (Sum.inr l)
  invFun w := match w with
    | Sum.inl a => Sum.inl (Sum.inl (Sum.inl (Sum.inl a)))
    | Sum.inr (Sum.inl (Sum.inl (Sum.inl x))) => Sum.inl (Sum.inl (Sum.inl (Sum.inr x)))
    | Sum.inr (Sum.inl (Sum.inl (Sum.inr n))) => Sum.inl (Sum.inl (Sum.inr n))
    | Sum.inr (Sum.inl (Sum.inr e)) => Sum.inl (Sum.inr e)
    | Sum.inr (Sum.inr l) => Sum.inr l
  left_inv w := by rcases w with ((((a | x) | n) | e) | l) <;> rfl
  right_inv w := by rcases w with a | (((x | n) | e) | l) <;> rfl

/-! ## The conjugated chart matrix `ambChartMat` + its block-triangularity -/

/-- The flat→chart linear isomorphism `E := funCongrLeft ℝ ℝ chartIdxEquiv.symm`. -/
noncomputable def ambChartE (M t : Fin (L + 1) → ℕ) (ha : StructAdm M t) :
    (Fin (routeMAmbient M) → ℝ) ≃ₗ[ℝ] (ChartIdx M (tDesc M t) → ℝ) :=
  LinearEquiv.funCongrLeft ℝ ℝ (chartIdxEquiv M (tDesc M t) ha.h0 ha.hc ha.hL).symm

/-- The conjugated Jacobian matrix on `ChartIdx → ℝ`: `toMatrix' (E ∘ₗ Dφ ∘ₗ E.symm)`. -/
noncomputable def ambChartMat (M t : Fin (L + 1) → ℕ) (ha : StructAdm M t)
    (y : Fin (routeMAmbient M) → ℝ) : Matrix (ChartIdx M (tDesc M t)) (ChartIdx M (tDesc M t)) ℝ :=
  LinearMap.toMatrix' (((ambChartE M t ha) : _ →ₗ[ℝ] _).comp
    (((fderiv ℝ (kLDU M t ha) y).toLinearMap).comp ((ambChartE M t ha).symm : _ →ₗ[ℝ] _)))

/-- The entry of the conjugated matrix is the per-output/per-direction `fderiv kLDU` value. -/
theorem ambChartMat_apply (M t : Fin (L + 1) → ℕ) (ha : StructAdm M t)
    (y : Fin (routeMAmbient M) → ℝ) (c c' : ChartIdx M (tDesc M t)) :
    ambChartMat M t ha y c c'
      = (fderiv ℝ (kLDU M t ha) y)
          (Pi.single ((chartIdxEquiv M (tDesc M t) ha.h0 ha.hc ha.hL).symm c') (1 : ℝ))
          ((chartIdxEquiv M (tDesc M t) ha.h0 ha.hc ha.hL).symm c) := by
  rw [ambChartMat, LinearMap.toMatrix'_apply]
  show (ambChartE M t ha) ((fderiv ℝ (kLDU M t ha) y)
    ((ambChartE M t ha).symm (Pi.single c' (1 : ℝ)))) c = _
  set cf := chartIdxEquiv M (tDesc M t) ha.h0 ha.hc ha.hL with hcf
  -- the source basis vector pulls back to the flat basis vector at `cf.symm c'`
  have hpull : (ambChartE M t ha).symm (Pi.single c' (1 : ℝ))
      = Pi.single (cf.symm c') (1 : ℝ) := by
    rw [ambChartE, LinearEquiv.funCongrLeft_symm]
    funext a
    rw [LinearEquiv.funCongrLeft_apply, LinearMap.funLeft_apply, Equiv.symm_symm]
    by_cases h : a = cf.symm c'
    · subst h; rw [Equiv.apply_symm_apply, Pi.single_eq_same, Pi.single_eq_same]
    · rw [Pi.single_eq_of_ne (fun hc => h (by rw [← Equiv.symm_apply_apply cf a, hc])),
        Pi.single_eq_of_ne h]
  rw [hpull, ambChartE, LinearEquiv.funCongrLeft_apply, LinearMap.funLeft_apply, ← hcf]

/-- `ambChartMat` is block-triangular for `Sigma.fst` (cross-boundary entries vanish). -/
theorem ambChartMat_blockTriangular (M t : Fin (L + 1) → ℕ) (ha : StructAdm M t)
    (y : Fin (routeMAmbient M) → ℝ) :
    (ambChartMat M t ha y).BlockTriangular Sigma.fst := by
  intro c c' hlt
  rw [ambChartMat_apply]
  exact fderiv_kLDU_cross_boundary M t ha y c c' (ne_of_lt hlt)

/-- The K-block matrix `KBlock` (over `Fin (τ*τ)`) is the `stdBasis` matrix of `fderiv kLens (readK y k)`
reindexed by `finProdFinEquiv`; its det equals `LinearMap.det (fderiv kLens (readK y k))`. -/
theorem KBlock_det_eq (M t : Fin (L + 1) → ℕ) (ha : StructAdm M t)
    (y : Fin (routeMAmbient M) → ℝ) (k : Fin L)
    (B : Matrix (Fin (Text M t (k.val + 1 + 1) * Text M t (k.val + 1 + 1)))
        (Fin (Text M t (k.val + 1 + 1) * Text M t (k.val + 1 + 1))) ℝ)
    (hB : ∀ a b, B a b = (fderiv ℝ (kLens (t := Text M t (k.val + 1 + 1)))
        (Matrix.of (readK M t ha y k)))
        (Matrix.single (finProdFinEquiv.symm b).1 (finProdFinEquiv.symm b).2 1)
        (finProdFinEquiv.symm a).1 (finProdFinEquiv.symm a).2) :
    B.det = LinearMap.det (fderiv ℝ (kLens (t := Text M t (k.val + 1 + 1)))
        (Matrix.of (readK M t ha y k))).toLinearMap := by
  have hBeq : B = Matrix.reindex finProdFinEquiv finProdFinEquiv
      (LinearMap.toMatrix
        (Matrix.stdBasis ℝ (Fin (Text M t (k.val + 1 + 1))) (Fin (Text M t (k.val + 1 + 1))))
        (Matrix.stdBasis ℝ (Fin (Text M t (k.val + 1 + 1))) (Fin (Text M t (k.val + 1 + 1))))
        (fderiv ℝ (kLens (t := Text M t (k.val + 1 + 1)))
          (Matrix.of (readK M t ha y k))).toLinearMap) := by
    ext a b
    rw [hB a b, Matrix.reindex_apply, Matrix.submatrix_apply, LinearMap.toMatrix_apply,
      show (Matrix.stdBasis ℝ (Fin (Text M t (k.val + 1 + 1))) (Fin (Text M t (k.val + 1 + 1))))
            (finProdFinEquiv.symm b)
          = Matrix.single (finProdFinEquiv.symm b).1 (finProdFinEquiv.symm b).2 1 from by
        rw [← Matrix.stdBasis_eq_single]]
    simp [Matrix.stdBasis]
  rw [hBeq, Matrix.det_reindex_self, LinearMap.det_toMatrix]

/-- The reindexed block `B := reindex e e (toSquareBlock)` (e the fiber+frame split) entry, as an
`ambChartMat` entry at the decoded chart indices. -/
theorem reindexBlock_apply (M t : Fin (L + 1) → ℕ) (ha : StructAdm M t)
    (y : Fin (routeMAmbient M) → ℝ) (k : Fin L)
    (e : {c : ChartIdx M (tDesc M t) // c.1 = k}
      ≃ ((((Fin (Text M t (k.val + 1 + 1) * Text M t (k.val + 1 + 1)) ⊕
          Fin ((Text M t (k.val + 1) - Text M t (k.val + 1 + 1)) * Text M t (k.val + 1 + 1))) ⊕
          Fin (Text M t (k.val + 1 + 1) * (Wext M (k.val + 1) - Text M t (k.val + 1 + 1)))) ⊕
          Fin ((Text M t (k.val + 1) - Text M t (k.val + 1 + 1)) *
            (Wext M (k.val + 1) - Text M t (k.val + 1 + 1)))) ⊕
          Fin (liftDim M (tDesc M t) k.val)))
    (σ σ' : _) :
    Matrix.reindex e e ((ambChartMat M t ha y).toSquareBlock Sigma.fst k) σ σ'
      = ambChartMat M t ha y (e.symm σ).val (e.symm σ').val := by
  rw [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.toSquareBlock_def, Matrix.of_apply]

/-- **Identity-arm entry** — if the output chart index `c` is the identity arm of `kLDU` (the pointwise
hypothesis `hid`), then `ambChartMat ... c c'' = if cf.symm c = cf.symm c'' then 1 else 0`. -/
theorem ambChartMat_id_entry (M t : Fin (L + 1) → ℕ) (ha : StructAdm M t)
    (y : Fin (routeMAmbient M) → ℝ) (c c'' : ChartIdx M (tDesc M t))
    (hid : ∀ x, kLDU M t ha x ((chartIdxEquiv M (tDesc M t) ha.h0 ha.hc ha.hL).symm c)
      = x ((chartIdxEquiv M (tDesc M t) ha.h0 ha.hc ha.hL).symm c)) :
    ambChartMat M t ha y c c''
      = if (chartIdxEquiv M (tDesc M t) ha.h0 ha.hc ha.hL).symm c
            = (chartIdxEquiv M (tDesc M t) ha.h0 ha.hc ha.hL).symm c'' then 1 else 0 := by
  set cf := chartIdxEquiv M (tDesc M t) ha.h0 ha.hc ha.hL
  rw [ambChartMat_apply, fderiv_kLDU_apply, kLDU_out_id_fun M t ha c hid,
    (hasFDerivAt_apply (cf.symm c) y).fderiv, ContinuousLinearMap.proj_apply, Pi.single_apply,
    eq_comm]

/-- The K-isolating fiber split `{c // c.1 = k} ≃ (Fin (τ*τ) ⊕ NonK)`, K-role first. -/
noncomputable def fiberSplit (M t : Fin (L + 1) → ℕ) (ha : StructAdm M t) (k : Fin L) :
    {c : ChartIdx M (tDesc M t) // c.1 = k}
      ≃ (Fin (Text M t (k.val + 1 + 1) * Text M t (k.val + 1 + 1)) ⊕
          ((((Fin ((Text M t (k.val + 1) - Text M t (k.val + 1 + 1)) * Text M t (k.val + 1 + 1)) ⊕
            Fin (Text M t (k.val + 1 + 1) * (Wext M (k.val + 1) - Text M t (k.val + 1 + 1)))) ⊕
            Fin ((Text M t (k.val + 1) - Text M t (k.val + 1 + 1)) *
              (Wext M (k.val + 1) - Text M t (k.val + 1 + 1)))) ⊕
            Fin (liftDim M (tDesc M t) k.val)))) :=
  (fiberEquiv M (tDesc M t) k).trans
    (((frameSplitEquiv M t (k.val + 1) (ha.hdesc k.val k.isLt) (ha.hub k.val)).sumCongr
      (Equiv.refl (Fin (liftDim M (tDesc M t) k.val)))).trans (kFront _ _ _ _ _))

/-- `fiberSplit.symm (inl qK)` is the boundary-`k` K-role chart index at matrix index `qK`. -/
theorem fiberSplit_symm_inl (M t : Fin (L + 1) → ℕ) (ha : StructAdm M t) (k : Fin L)
    (qK : Fin (Text M t (k.val + 1 + 1) * Text M t (k.val + 1 + 1))) :
    ((fiberSplit M t ha k).symm (Sum.inl qK)).val
      = ⟨k, Sum.inl ((frameSplitEquiv M t (k.val + 1) (ha.hdesc k.val k.isLt) (ha.hub k.val)).symm
          (Sum.inl (Sum.inl (Sum.inl qK))))⟩ := rfl

/-- **Per-boundary block det** — `|det (ambChartMat.toSquareBlock Sigma.fst k)| = ∏_i |q_{k,i}|^{…}`,
the banked per-K-core `kLens_abs_det` transported through the boundary-`k` fiber identification:
reindex by `fiberSplit` (K-role first), peel the spectator identity block, identify the K-block with
`fderiv kLens (readK y k)` in the std matrix basis (`KBlock_det_eq`), then `kLens_abs_det`. -/
theorem toSquareBlock_abs_det (M t : Fin (L + 1) → ℕ) (ha : StructAdm M t)
    (y : Fin (routeMAmbient M) → ℝ) (k : Fin L) :
    |((ambChartMat M t ha y).toSquareBlock Sigma.fst k).det|
      = ∏ i : Fin (Text M t (k.val + 2)),
          |(matrixSplit (Matrix.of (readK M t ha y k))).2.1 i|
            ^ (2 * ((Text M t (k.val + 2) : ℕ) - 1 - (i : ℕ))) := by
  set cf := chartIdxEquiv M (tDesc M t) ha.h0 ha.hc ha.hL with hcf
  set τ := Text M t (k.val + 1 + 1) with hτ
  set e := fiberSplit M t ha k with he
  set B := Matrix.reindex e e ((ambChartMat M t ha y).toSquareBlock Sigma.fst k) with hBdef
  -- det of the block = det of its reindex
  have hdet0 : ((ambChartMat M t ha y).toSquareBlock Sigma.fst k).det = B.det := by
    rw [hBdef, Matrix.det_reindex_self]
  -- the K-block entry matches `KBlock_det_eq`'s shape
  have hKentry : ∀ a b, B.toBlocks₁₁ a b
      = (fderiv ℝ (kLens (t := τ)) (Matrix.of (readK M t ha y k)))
          (Matrix.single (finProdFinEquiv.symm b).1 (finProdFinEquiv.symm b).2 1)
          (finProdFinEquiv.symm a).1 (finProdFinEquiv.symm a).2 := by
    intro a b
    rw [Matrix.toBlocks₁₁, Matrix.of_apply, hBdef, Matrix.reindex_apply, Matrix.submatrix_apply,
      Matrix.toSquareBlock_def, Matrix.of_apply, fiberSplit_symm_inl,
      fiberSplit_symm_inl, ambChartMat_apply, fderiv_kLDU_apply,
      kLDU_out_K_fun M t ha k _
        (by rw [Equiv.apply_symm_apply] :
          frameSplitEquiv M t (k.val + 1) (ha.hdesc k.val k.isLt) (ha.hub k.val)
            ((frameSplitEquiv M t (k.val + 1) (ha.hdesc k.val k.isLt) (ha.hub k.val)).symm
              (Sum.inl (Sum.inl (Sum.inl a)))) = Sum.inl (Sum.inl (Sum.inl a))),
      (hasFDerivAt_kLDU_out_K M t ha k _ _ y).fderiv]
    simp only [ContinuousLinearMap.comp_apply, LinearEquiv.apply_symm_apply, matEntryCLM_apply,
      LinearMap.coe_toContinuousLinearMap']
    -- the read direction is the single basis matrix at index `finProdFinEquiv.symm b`
    have hread : (readKL M t ha k)
        (Pi.single (cf.symm ⟨k, Sum.inl ((frameSplitEquiv M t (k.val + 1)
          (ha.hdesc k.val k.isLt) (ha.hub k.val)).symm (Sum.inl (Sum.inl (Sum.inl b))))⟩) (1 : ℝ))
        = Matrix.single (finProdFinEquiv.symm b).1 (finProdFinEquiv.symm b).2 1 := by
      ext p q
      rw [readKL_apply, Matrix.of_apply, readK, Matrix.single_apply]
      by_cases hpq : (finProdFinEquiv.symm b).1 = p ∧ (finProdFinEquiv.symm b).2 = q
      · obtain ⟨hp, hq⟩ := hpq
        rw [if_pos ⟨hp, hq⟩, ← hp, ← hq, Prod.mk.eta, Equiv.apply_symm_apply, Pi.single_eq_same]
      · rw [if_neg hpq, Pi.single_eq_of_ne]
        intro hc
        apply hpq
        have hsig := cf.symm.injective hc
        have h2 := eq_of_heq (Sigma.mk.inj_iff.mp hsig).2
        have h3 := (frameSplitEquiv M t (k.val + 1) (ha.hdesc k.val k.isLt)
          (ha.hub k.val)).symm.injective ((Sum.inl.injEq _ _).mp h2)
        have h4 : (p, q) = finProdFinEquiv.symm b :=
          finProdFinEquiv.injective (by
            rw [Equiv.apply_symm_apply]
            exact (Sum.inl.injEq _ _).mp ((Sum.inl.injEq _ _).mp ((Sum.inl.injEq _ _).mp h3)))
        exact ⟨(congrArg Prod.fst h4).symm, (congrArg Prod.snd h4).symm⟩
    rw [hread]
  -- every NonK chart index is an identity arm of kLDU
  -- every NonK chart index decodes to a non-K frame role or a lift slot (the `kLDU` identity arm)
  set fse := frameSplitEquiv M t (k.val + 1) (ha.hdesc k.val k.isLt) (ha.hub k.val) with hfse
  -- the chart index of each NonK case: `inl (fse.symm non-K)` for X/N/E, `inr lift` for the lift
  have hchart : ∀ i, (e.symm (Sum.inr i)).val = (⟨k,
      match i with
      | Sum.inl (Sum.inl (Sum.inl x')) => Sum.inl (fse.symm (Sum.inl (Sum.inl (Sum.inr x'))))
      | Sum.inl (Sum.inl (Sum.inr n)) => Sum.inl (fse.symm (Sum.inl (Sum.inr n)))
      | Sum.inl (Sum.inr ee) => Sum.inl (fse.symm (Sum.inr ee))
      | Sum.inr l => Sum.inr l⟩ : ChartIdx M (tDesc M t)) := by
    intro i
    rw [he, fiberSplit]
    rcases i with ((x' | n) | ee) | l <;> rfl
  have hNonK_id : ∀ i, ∀ x, kLDU M t ha x (cf.symm ((e.symm (Sum.inr i)).val))
      = x (cf.symm ((e.symm (Sum.inr i)).val)) := by
    intro i x
    rw [hchart, hcf, kLDU]
    rcases i with ((x' | n) | ee) | l
    · simp only [Equiv.apply_symm_apply, hfse]
    · simp only [Equiv.apply_symm_apply, hfse]
    · simp only [Equiv.apply_symm_apply, hfse]
    · simp only [Equiv.apply_symm_apply]
  -- the NonK block is the identity; the lower-left block vanishes
  have hid_entry : ∀ (i j : _),
      B (Sum.inr i) j
        = if cf.symm (e.symm (Sum.inr i)).val = cf.symm (e.symm j).val then 1 else 0 := by
    intro i j
    rw [hBdef, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.toSquareBlock_def,
      Matrix.of_apply]
    exact ambChartMat_id_entry M t ha y _ _ (hNonK_id i)
  have hlower : ∀ i j, B (Sum.inr i) (Sum.inl j) = 0 := by
    intro i j
    rw [hid_entry, if_neg]
    intro hc
    exact Sum.inr_ne_inl (e.symm.injective (Subtype.ext (cf.symm.injective hc)))
  have hB22 : B.toBlocks₂₂ = (1 : Matrix _ _ ℝ) := by
    ext i j
    rw [Matrix.toBlocks₂₂, Matrix.of_apply, hid_entry, Matrix.one_apply]
    by_cases h : i = j
    · rw [h, if_pos rfl, if_pos rfl]
    · rw [if_neg h, if_neg (fun hc =>
        h (e.symm.injective (Subtype.ext (cf.symm.injective hc)) |> Sum.inr_injective))]
  -- assemble: det = K-block det · NonK det(=1); bridge K-block to LinearMap.det; kLens_abs_det
  rw [hdet0, det_eq_toBlocks_of_lower_zero B hlower, hB22, Matrix.det_one, mul_one,
    KBlock_det_eq M t ha y k B.toBlocks₁₁ hKentry]
  exact kLens_abs_det (Matrix.of (readK M t ha y k))

/-- **H2b-i — the full-ambient `kLDU` lens Jacobian abs-det** (the route-independent atom the
BdetMonomial assembly multiplies by): `|det (fderiv kLDU y)| = ∏_k ∏_i |q_{k,i}|^{2(t_k−1−i)}`, the
product over boundaries `k` of the per-K-core `kLens` LDU-pivot monomial at the K-core read at `y`.
The BlockTriangular-over-`chartIdxEquiv` assembly of the banked per-core `kLens_abs_det`. -/
theorem kLDU_ambient_abs_det (M t : Fin (L + 1) → ℕ) (ha : StructAdm M t)
    (y : Fin (routeMAmbient M) → ℝ) :
    |LinearMap.det (fderiv ℝ (kLDU M t ha) y).toLinearMap|
      = ∏ k : Fin L, ∏ i : Fin (Text M t (k.val + 2)),
          |(matrixSplit (Matrix.of (readK M t ha y k))).2.1 i|
            ^ (2 * ((Text M t (k.val + 2) : ℕ) - 1 - (i : ℕ))) := by
  -- det via the conjugation + block-triangular product over the per-boundary blocks
  have hconj : LinearMap.det (fderiv ℝ (kLDU M t ha) y).toLinearMap
      = (ambChartMat M t ha y).det := by
    rw [ambChartMat, LinearMap.det_toMatrix']
    exact (LinearMap.det_conj (fderiv ℝ (kLDU M t ha) y).toLinearMap (ambChartE M t ha)).symm
  rw [hconj, (ambChartMat_blockTriangular M t ha y).det_fintype, Finset.abs_prod]
  refine Finset.prod_congr rfl (fun k _ => ?_)
  -- per-block: |det (toSquareBlock k)| = ∏ i |q_{k,i}|^{2(t-1-i)}
  exact toSquareBlock_abs_det M t ha y k

end DLNFibre.DLN.RLCT
