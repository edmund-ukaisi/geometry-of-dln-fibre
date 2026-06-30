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

## Status (SKELETON — the cast-heavy core isolated)

The setup (reindex + det_conj + the BlockTriangular goal) is verified to elaborate. The headline
`kLDU_ambient_abs_det` carries one STATED `sorry` (correct statement, locked sig). NOT axiom-clean yet.

## HANDOFF (genm-h2bdet → cast-specialist, 2026-06-30)

**Locked target sig**: `kLDU_ambient_abs_det` below — the RHS is keyed to `readK M t ha y k` (the K-core
read at `y`), `q = (matrixSplit (Matrix.of (readK … y k))).2.1` the LDU diagonal pivots. The
`interiorLive_BdetMonomial` assembly (genm-h2bdet) multiplies this by the Schur-frame factor.

**Banked input (consume directly)**: `kLens_abs_det` (`RouteMInteriorLiveDet`, axiom-clean):
`|det (fderiv kLens K)| = ∏ i, |(matrixSplit K).2.1 i| ^ (2*(t−1−i))`. Also `kLens_hasFDerivAt` (explicit
fderiv = `matrixSplit.symm ∘L lduCoreD(split K) ∘L matrixSplit`). The per-K-core block det.

**ROUTE 1 division (with genm-r1lower)**: genm-r1lower owns the eihd free-y₀ det lemma (separate module)
+ the abs_det assembly/injOn/glue; genm-castdet owns `hreg` (route-A, `|det(eihdOut.symm∘eIn)|=1`); this
file owns the ambient det; the `interiorLive_BdetMonomial` chain-rule assembly (genm-h2bdet) folds all
three at `y₀ = kLDU(pbo u)`.

**Two remaining sub-pieces** (Codex xhigh route, `threads/genm-h2bdet/codex/ambient-det-answer.md`):

1. **Cross-boundary entry vanishing** (~40-60 line). `A := toMatrix' (E ∘ₗ (fderiv kLDU y) ∘ₗ E.symm)`,
   `E := funCongrLeft ℝ ℝ chartIdxEquiv.symm`. Prove `A.BlockTriangular Sigma.fst`. Entry
   `A c c' = (fderiv kLDU y) (Pi.single (chartIdxEquiv.symm c') 1) (chartIdxEquiv.symm c)` (via
   `toMatrix'_apply` + `funLeft_apply` + `funCongrLeft_symm`). Reduce per-coordinate by `fderiv_pi`
   (differentiability = `differentiable_kLDU`, contract). The boundary-`c.1` output K-coordinate is
   `kLens (readK x c.1) i j` (or identity for spectators); `readK x k` reads only boundary-`k` K-slots,
   so its fderiv kills the `Pi.single` direction at any `c'.1 ≠ c.1` (readK-linear-on-slots ⟹
   `kLens'`-of-0-component ⟹ 0). Then `Matrix.BlockTriangular.det_fintype` ⟹
   `A.det = ∏ k : Fin L, (A.toSquareBlock Sigma.fst k).det`.

2. **Per-boundary block identification** (~80-120 line, the cast-heavy part). Identify
   `A.toSquareBlock Sigma.fst k` with `kLens (readK y k) ⊕ id` (K-core block ⊕ spectators), det via
   `LinearMap.det_prodMap` + `LinearMap.det_id` + the banked `kLens_abs_det`. The opaque-width casts:
   * `{c : ChartIdx // c.1 = k} ≃ (Fin (schurDim k) ⊕ Fin (liftDim k))` (the boundary-`k` slot fiber),
     then split the schur fiber by `frameSplitEquiv` into K/X/N/E and isolate the K-role;
   * `Fin (Text … (k+2) * Text … (k+2)) ≃ Fin (Text…) × Fin (Text…)` via `finProdFinEquiv` (the K-core
     matrix-index reshape — matches `readK`'s `finProdFinEquiv (i,j)` tag);
   * `Matrix.det_reindex_self` to move between the `toSquareBlock` subtype and the role-Sum index.
   Spectator sub-block (X/N/E/lift) is the identity (kLDU's id-arm) ⟹ `det = 1`.

`LinearMap.det_pi` does NOT apply (homogeneous; dependent K-core widths) — `BlockTriangular.det_fintype`
is the route. All Mathlib names verified at v4.29.
-/

open Matrix
open scoped BigOperators

namespace DLNFibre.DLN.RLCT

variable {L : ℕ}

/-- **H2b-i — the full-ambient `kLDU` lens Jacobian abs-det** (the route-independent atom the
BdetMonomial assembly multiplies by): `|det (fderiv kLDU y)| = ∏_k ∏_i |q_{k,i}|^{2(t_k−1−i)}`, the
product over boundaries `k` of the per-K-core `kLens` LDU-pivot monomial at the K-core read at `y`.
SKELETON: the BlockTriangular-over-`chartIdxEquiv` assembly of the banked per-core `kLens_abs_det`. -/
theorem kLDU_ambient_abs_det (M t : Fin (L + 1) → ℕ) (ha : StructAdm M t)
    (y : Fin (routeMAmbient M) → ℝ) :
    |LinearMap.det (fderiv ℝ (kLDU M t ha) y).toLinearMap|
      = ∏ k : Fin L, ∏ i : Fin (Text M t (k.val + 2)),
          |(matrixSplit (Matrix.of (readK M t ha y k))).2.1 i|
            ^ (2 * ((Text M t (k.val + 2) : ℕ) - 1 - (i : ℕ))) :=
  sorry

end DLNFibre.DLN.RLCT
