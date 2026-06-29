import DLNFibre.DLN.RLCT.Validate.RouteMDecoderDiff
import DLNFibre.DLN.RLCT.Validate.RouteMAchieverWitnessInterior

/-!
# `RouteMSchurValue` — the `Cgen s = Schur frame` matrix VALUE identity (per-block, opaque-width)

Sub-piece #4 of the opaque-`M` fderiv-as-staircase construction (engine-id design, Codex consult
`threads/80-genM-nodechart/codex/engine-id-answer.md`, rank-4 = lowest-risk of the remaining): the
chart's compressed transition at an interior boundary `s` IS the Schur frame. With the achiever
blocks `Bmat s = bmatStack(K, X)` (`= [K ; X·K]`), `chainQ(N) = [I | N]`, `Rmat s = rmatPad(E)`
(`= [[0,0],[0,E]]`),

  `Cgen-shape := bmatStack(K,X) · chainQ(N) + u • rmatPad(E) = [[K, K·N],[X·K, X·K·N + u·E]]`,

the per-boundary Schur frame `S(X, K, N, u·E)`. Banked PER-BLOCK (Codex's grain): four block lemmas
(`K` / `K·N` / `X·K` / `X·K·N + u·E`), each at the split row/col `castAdd`/`natAdd` indices, closed
by the banked accessors (`bmatStack_top`/`_bot`, `chainQ_apply_castAdd`/`_natAdd`, `rmatPad_*_*`) +
`Matrix.mul_apply` over the chaining split — NO global `ext` over opaque `Fin (Text s)`/`(Wext s)`.

* `schurFrameProd` — the abstract `bmatStack(K,X) · chainQ(N) + u • rmatPad(E)` (network-free).
* `schurFrameProd_block_K` / `_KN` / `_XK` / `_XKNuE` — the four output blocks.

This makes the fderiv identification (#5) a per-block chain-rule/congruence problem, not a reindex.

Axiom-clean `[propext, Classical.choice, Quot.sound]` (matrix algebra; no analysis).
-/

open Matrix
open scoped BigOperators

noncomputable section

namespace DLNFibre.DLN.RLCT

variable {L : ℕ}

/-- **The Schur-frame product (abstract)** `bmatStack(K,X) · chainQ(N) + u • rmatPad(E)` at an
interior boundary `s`, over the opaque `Text`/`Wext` widths. The chart's `Cgen s` shape with the
achiever blocks; this module shows it is the Schur frame `[[K, K·N],[X·K, X·K·N + u·E]]`. -/
noncomputable def schurFrameProd (M t : Fin (L + 1) → ℕ) (s : ℕ)
    (h1 : Text M t (s + 1) ≤ Text M t s) (h2 : Text M t (s + 1) ≤ Wext M s) (u : ℝ)
    (K : Matrix (Fin (Text M t (s + 1))) (Fin (Text M t (s + 1))) ℝ)
    (X : Matrix (Fin (Text M t s - Text M t (s + 1))) (Fin (Text M t (s + 1))) ℝ)
    (N : Matrix (Fin (Text M t (s + 1))) (Fin (Wext M s - Text M t (s + 1))) ℝ)
    (E : Matrix (Fin (Text M t s - Text M t (s + 1))) (Fin (Wext M s - Text M t (s + 1))) ℝ) :
    Matrix (Fin (Text M t s)) (Fin (Wext M s)) ℝ :=
  bmatStack M t s h1 K X
      * chainQ (show Text M t (s + 1) + (Wext M s - Text M t (s + 1)) = Wext M s by omega) N
    + u • rmatPad M t s h1 h2 E

/-- The chaining-row left (kept `I`) and right (residual `N`) column casts of `chainQ N`. -/
private theorem chainQ_left {M t : Fin (L + 1) → ℕ} {s : ℕ} (h2 : Text M t (s + 1) ≤ Wext M s)
    (N : Matrix (Fin (Text M t (s + 1))) (Fin (Wext M s - Text M t (s + 1))) ℝ)
    (i : Fin (Text M t (s + 1))) (j : Fin (Text M t (s + 1))) :
    chainQ (show Text M t (s + 1) + (Wext M s - Text M t (s + 1)) = Wext M s by omega) N i
        (Fin.cast (show Text M t (s + 1) + (Wext M s - Text M t (s + 1)) = Wext M s by omega)
          (Fin.castAdd (Wext M s - Text M t (s + 1)) j))
      = (1 : Matrix (Fin (Text M t (s + 1))) (Fin (Text M t (s + 1))) ℝ) i j :=
  chainQ_apply_castAdd _ N i j

private theorem chainQ_right {M t : Fin (L + 1) → ℕ} {s : ℕ} (h2 : Text M t (s + 1) ≤ Wext M s)
    (N : Matrix (Fin (Text M t (s + 1))) (Fin (Wext M s - Text M t (s + 1))) ℝ)
    (i : Fin (Text M t (s + 1))) (a : Fin (Wext M s - Text M t (s + 1))) :
    chainQ (show Text M t (s + 1) + (Wext M s - Text M t (s + 1)) = Wext M s by omega) N i
        (Fin.cast (show Text M t (s + 1) + (Wext M s - Text M t (s + 1)) = Wext M s by omega)
          (Fin.natAdd (Text M t (s + 1)) a))
      = N i a :=
  chainQ_apply_natAdd _ N i a

/-- **Block `K` (top-left):** `schurFrameProd … (top row a, left col b) = K a b`. -/
theorem schurFrameProd_block_K (M t : Fin (L + 1) → ℕ) (s : ℕ)
    (h1 : Text M t (s + 1) ≤ Text M t s) (h2 : Text M t (s + 1) ≤ Wext M s) (u : ℝ)
    (K : Matrix (Fin (Text M t (s + 1))) (Fin (Text M t (s + 1))) ℝ)
    (X : Matrix (Fin (Text M t s - Text M t (s + 1))) (Fin (Text M t (s + 1))) ℝ)
    (N : Matrix (Fin (Text M t (s + 1))) (Fin (Wext M s - Text M t (s + 1))) ℝ)
    (E : Matrix (Fin (Text M t s - Text M t (s + 1))) (Fin (Wext M s - Text M t (s + 1))) ℝ)
    (a : Fin (Text M t (s + 1))) (b : Fin (Text M t (s + 1))) :
    schurFrameProd M t s h1 h2 u K X N E
        (Fin.cast (show Text M t (s + 1) + (Text M t s - Text M t (s + 1)) = Text M t s by omega)
          (Fin.castAdd (Text M t s - Text M t (s + 1)) a))
        (Fin.cast (show Text M t (s + 1) + (Wext M s - Text M t (s + 1)) = Wext M s by omega)
          (Fin.castAdd (Wext M s - Text M t (s + 1)) b))
      = K a b := by
  rw [schurFrameProd, Matrix.add_apply, Matrix.smul_apply, rmatPad_castAdd_castAdd, smul_zero,
    add_zero, Matrix.mul_apply]
  rw [Finset.sum_eq_single b]
  · rw [bmatStack_top, chainQ_left h2, Matrix.one_apply_eq, mul_one]
  · intro y _ hy
    rw [chainQ_left h2, Matrix.one_apply, if_neg hy, mul_zero]
  · intro hcon; exact absurd (Finset.mem_univ b) hcon

/-- **Block `K·N` (top-right):** `schurFrameProd … (top row a, right col b) = (K·N) a b`. -/
theorem schurFrameProd_block_KN (M t : Fin (L + 1) → ℕ) (s : ℕ)
    (h1 : Text M t (s + 1) ≤ Text M t s) (h2 : Text M t (s + 1) ≤ Wext M s) (u : ℝ)
    (K : Matrix (Fin (Text M t (s + 1))) (Fin (Text M t (s + 1))) ℝ)
    (X : Matrix (Fin (Text M t s - Text M t (s + 1))) (Fin (Text M t (s + 1))) ℝ)
    (N : Matrix (Fin (Text M t (s + 1))) (Fin (Wext M s - Text M t (s + 1))) ℝ)
    (E : Matrix (Fin (Text M t s - Text M t (s + 1))) (Fin (Wext M s - Text M t (s + 1))) ℝ)
    (a : Fin (Text M t (s + 1))) (b : Fin (Wext M s - Text M t (s + 1))) :
    schurFrameProd M t s h1 h2 u K X N E
        (Fin.cast (show Text M t (s + 1) + (Text M t s - Text M t (s + 1)) = Text M t s by omega)
          (Fin.castAdd (Text M t s - Text M t (s + 1)) a))
        (Fin.cast (show Text M t (s + 1) + (Wext M s - Text M t (s + 1)) = Wext M s by omega)
          (Fin.natAdd (Text M t (s + 1)) b))
      = (K * N) a b := by
  rw [schurFrameProd, Matrix.add_apply, Matrix.smul_apply, rmatPad_castAdd_natAdd, smul_zero,
    add_zero, Matrix.mul_apply, Matrix.mul_apply]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  rw [bmatStack_top, chainQ_right h2]

/-- **Block `X·K` (bottom-left):** `schurFrameProd … (bot row a, left col b) = (X·K) a b`. -/
theorem schurFrameProd_block_XK (M t : Fin (L + 1) → ℕ) (s : ℕ)
    (h1 : Text M t (s + 1) ≤ Text M t s) (h2 : Text M t (s + 1) ≤ Wext M s) (u : ℝ)
    (K : Matrix (Fin (Text M t (s + 1))) (Fin (Text M t (s + 1))) ℝ)
    (X : Matrix (Fin (Text M t s - Text M t (s + 1))) (Fin (Text M t (s + 1))) ℝ)
    (N : Matrix (Fin (Text M t (s + 1))) (Fin (Wext M s - Text M t (s + 1))) ℝ)
    (E : Matrix (Fin (Text M t s - Text M t (s + 1))) (Fin (Wext M s - Text M t (s + 1))) ℝ)
    (a : Fin (Text M t s - Text M t (s + 1))) (b : Fin (Text M t (s + 1))) :
    schurFrameProd M t s h1 h2 u K X N E
        (Fin.cast (show Text M t (s + 1) + (Text M t s - Text M t (s + 1)) = Text M t s by omega)
          (Fin.natAdd (Text M t (s + 1)) a))
        (Fin.cast (show Text M t (s + 1) + (Wext M s - Text M t (s + 1)) = Wext M s by omega)
          (Fin.castAdd (Wext M s - Text M t (s + 1)) b))
      = (X * K) a b := by
  rw [schurFrameProd, Matrix.add_apply, Matrix.smul_apply, rmatPad_natAdd_castAdd, smul_zero,
    add_zero, Matrix.mul_apply]
  -- summand `(bmatStack_bot = (X·K) a y) · (chainQ_left = (1) y b)`; collapse the `1`-boole sum.
  rw [Finset.sum_eq_single b]
  · rw [bmatStack_bot, chainQ_left h2, Matrix.one_apply_eq, mul_one]
  · intro y _ hy
    rw [chainQ_left h2, Matrix.one_apply, if_neg hy, mul_zero]
  · intro hcon; exact absurd (Finset.mem_univ b) hcon

/-- **Block `X·K·N + u·E` (bottom-right):** `schurFrameProd … (bot row a, right col b)
= (X·K·N) a b + u·E a b`. -/
theorem schurFrameProd_block_XKNuE (M t : Fin (L + 1) → ℕ) (s : ℕ)
    (h1 : Text M t (s + 1) ≤ Text M t s) (h2 : Text M t (s + 1) ≤ Wext M s) (u : ℝ)
    (K : Matrix (Fin (Text M t (s + 1))) (Fin (Text M t (s + 1))) ℝ)
    (X : Matrix (Fin (Text M t s - Text M t (s + 1))) (Fin (Text M t (s + 1))) ℝ)
    (N : Matrix (Fin (Text M t (s + 1))) (Fin (Wext M s - Text M t (s + 1))) ℝ)
    (E : Matrix (Fin (Text M t s - Text M t (s + 1))) (Fin (Wext M s - Text M t (s + 1))) ℝ)
    (a : Fin (Text M t s - Text M t (s + 1))) (b : Fin (Wext M s - Text M t (s + 1))) :
    schurFrameProd M t s h1 h2 u K X N E
        (Fin.cast (show Text M t (s + 1) + (Text M t s - Text M t (s + 1)) = Text M t s by omega)
          (Fin.natAdd (Text M t (s + 1)) a))
        (Fin.cast (show Text M t (s + 1) + (Wext M s - Text M t (s + 1)) = Wext M s by omega)
          (Fin.natAdd (Text M t (s + 1)) b))
      = (X * K * N) a b + u * E a b := by
  rw [schurFrameProd, Matrix.add_apply, Matrix.smul_apply, rmatPad_natAdd_natAdd, smul_eq_mul,
    Matrix.mul_apply]
  congr 1
  rw [show (X * K * N) a b = ∑ y, (X * K) a y * N y b from Matrix.mul_apply]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  rw [bmatStack_bot, chainQ_right h2]

end DLNFibre.DLN.RLCT

end
