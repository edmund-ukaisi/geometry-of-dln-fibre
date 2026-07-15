/-
Copyright (c) 2026. Released under Apache 2.0; see LICENSE.
-/
import DLNFibre.DLN.RLCT.Validate.RouteMSJIncidenceChart5BigCell
import DLNFibre.DLN.RLCT.Validate.RouteMSJGammaAtom
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.LinearAlgebra.Matrix.Rank

set_option linter.style.longLine false

/-!
# `RouteMSJDeepAtlas` — the DEEP stratified-resolution atlas, geometric charts (Tide A)

**Thread `genm-deepatlas`, aoyagi-full Stage 2.** The deep analog of the front incidence-rank atlas
(`RouteMSJIncidenceChart*`): the geometric charts of the telescoping-Schur resolution of the deep
degeneration `{rank Z_deep ≤ s}` in the DLN deep parameter space
(`genm-deepatlas-design/design.md` §2). This file is **Tide A only** — the per-level block-Schur
big-cell (reused from the front) + the genuinely-new **product-layer reduction** unit-Jacobian change
of variables. It is standalone (NOT wired to the aggregator); the coherent Route-B unit is integrated
by the controller.

**Scope guard (design §4, `couplingfin`, `deepgate`).** These are the RANK/measure charts of the
resolution, defined by the rank stratification `{E_j = 0}` alone. They are **independent of the loss**:
the product seam `F·E` in the composed loss (design §4.2) is a Tide-D loss-monomialisation phenomenon
and appears in **no** theorem here. Every codim is the parameter-space CR recursion (design §6), never
the determinantal `(M₂−s)(M_last−s)` — this file supplies only the atlas primitives, not the count.

## What lands here (sorry-free)

### Deliverable 1 — the per-level block-Schur big-cell (re-export, no new math; design §2.1)
At a recursion level with effective last layer `M ∈ ℝ^{n×d}`, top-left size-`r` pivot `Δ ∈ GL_r`,
block `M = [[Δ,U],[V,W]]` and transverse Schur coordinate `E := W − VΔ⁻¹U`:
* **`deepLevel_bigcell_cov`** — the `W ↦ E` translation change of variables, Jacobian `≡ 1`
  (re-export of `chart5_bigcell_cov`).
* **`deepLevel_rank_eq`** — `rank M = r + rank E` (re-export of `chart5_rank_eq`).
* **`deepLevel_rank_le_iff`** — `{rank M ≤ r} = {E = 0}` in the CoV coordinates (re-export of
  `chart5_rank_le_iff_reassembled`).
These are the front chart-(5) facts re-framed at the deep "effective last layer" level, in the pivot
top-left normal form; the general `(I,J)` pivot permutation (Jacobian `±1`) is Tide B's reindexing.

### Deliverable 2 — the product-layer reduction, unit-Jacobian CoV (the new piece; design §2.2)
The reduced chain's last layer is the **product** `L·A` (`A =` the pivot columns of `M`), not free.
The completion `G₀ = [[I,0],[VΔ⁻¹,I]]` is unitriangular (`det G₀ = 1`), `L·G₀ = (H, F)` splits into the
new free last layer `H = L·A·Δ⁻¹` and a spectator `F`.
* **`deepReduce_skeleton`** — the rank-`r` skeleton (CUR) factorization on `{E = 0}`:
  `[[Δ,U],[V,VΔ⁻¹U]] = A · Δ⁻¹ · D`, `A = [[Δ],[V]]` (pivot columns), `D = [Δ|U]` (pivot rows). This is
  why the reduction works: on the rank-drop stratum `M` factors through its pivot minor.
* **`deepReduce_G0_det_eq_one`** — `det G₀ = 1` (the completion is unit-Jacobian).
* **`deepReduce_cov`** — the unit-Jacobian CoV: right-multiplication of the free layer `L` by any
  `|det G| = 1` matrix preserves the raw-pi lintegral (`∫⁻ L, g(L·G) = ∫⁻ L, g L`). Instantiated at
  `G = G₀` (via `deepReduce_G0_det_eq_one`) this is the "product-layer reduction" CoV. Reuses the banked
  raw-pi diamond-dodge `lintegral_comp_rightMulₚ`.
* **`deepReduce_rank`** — the rank identity on `{E = 0}`: `rank(X · M) = rank(X · A · Δ⁻¹)` for any
  preceding head `X` (`= rank(B·L·M) = rank(B·H)` with `X = B·L`). The reduced last layer `H = L·A·Δ⁻¹`
  carries the full composed rank; the pivot rows `[Δ|U]` (full row rank `r`) drop out.

Axiom target `[propext, Classical.choice, Quot.sound]`.
-/

namespace DLNFibre.DLN.RLCT

open Matrix MeasureTheory
open scoped ENNReal BigOperators

namespace DeepAtlas

/-! ## Deliverable 1 — the per-level block-Schur big-cell (re-export of the front chart 5) -/

variable {r s t : ℕ}

/-- **Per-level big-cell CoV, Jacobian ≡ 1** (design §2.1). At a recursion level with effective last
layer `M`, top-left size-`r` pivot, the transverse-Schur translation `W₂₂ ↦ E` of the last block
preserves the raw-pi lintegral. Re-export of the front `chart5_bigcell_cov` at the deep level. -/
theorem deepLevel_bigcell_cov
    (f : (Chart5FixedBlocks r s t) × (Fin s → Fin t → ℝ) → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ p : (Chart5FixedBlocks r s t) × (Fin s → Fin t → ℝ), f (p.1, p.2 + chart5Shift p.1)
      = ∫⁻ p, f p :=
  chart5_bigcell_cov f hf

/-- **Per-level rank identity** `rank M = r + rank E`, `E = W − V Δ⁻¹ U` the transverse Schur
complement (design §2.1). Re-export of the front `chart5_rank_eq` (`Core.SchurChartIff`). -/
theorem deepLevel_rank_eq
    (Δ : Matrix (Fin r) (Fin r) ℝ) (U : Matrix (Fin r) (Fin t) ℝ)
    (V : Matrix (Fin s) (Fin r) ℝ) (W : Matrix (Fin s) (Fin t) ℝ) (hΔ : IsUnit Δ.det) :
    (Matrix.fromBlocks Δ U V W).rank = r + (W - V * Δ⁻¹ * U).rank :=
  chart5_rank_eq Δ U V W hΔ

/-- **Per-level rank-drop slice** `{rank M ≤ r} = {E = 0}` in the CoV coordinates (design §2.1). The
rank-drop stratum is the transverse coordinate origin. Re-export of `chart5_rank_le_iff_reassembled`. -/
theorem deepLevel_rank_le_iff
    (Δ : Matrix (Fin r) (Fin r) ℝ) (U : Matrix (Fin r) (Fin t) ℝ)
    (V : Matrix (Fin s) (Fin r) ℝ) (E : Fin s → Fin t → ℝ) (hΔ : IsUnit Δ.det) :
    (Matrix.fromBlocks Δ U V (E + chart5Shift (Δ, U, V))).rank ≤ r ↔ E = 0 :=
  chart5_rank_le_iff_reassembled Δ U V E hΔ

/-! ## Deliverable 2 — the product-layer reduction (the new piece, design §2.2) -/

/-- **The rank-`r` skeleton (CUR) factorization on `{E = 0}`.** On the rank-drop stratum the effective
last layer factors through its pivot minor:

    [[Δ, U], [V, V Δ⁻¹ U]]  =  [[Δ],[V]] · Δ⁻¹ · [Δ | U]  =  A · Δ⁻¹ · D,

`A = fromRows Δ V` (the pivot columns), `D = fromCols Δ U` (the pivot rows). This is the algebraic
heart of the reduction: multiplying by a preceding layer `L`, `L·M = (L·A·Δ⁻¹)·D = H·D`, so the reduced
last layer `H = L·A·Δ⁻¹` carries the composed rank (`deepReduce_rank`). -/
theorem deepReduce_skeleton {r nr dc : ℕ}
    (Δ : Matrix (Fin r) (Fin r) ℝ) (U : Matrix (Fin r) (Fin dc) ℝ)
    (V : Matrix (Fin nr) (Fin r) ℝ) (hΔ : IsUnit Δ.det) :
    (Matrix.fromBlocks Δ U V (V * Δ⁻¹ * U) : Matrix (Fin r ⊕ Fin nr) (Fin r ⊕ Fin dc) ℝ)
      = Matrix.fromRows Δ V * Δ⁻¹ * Matrix.fromCols Δ U := by
  have h1 : Δ * Δ⁻¹ = 1 := Matrix.mul_nonsing_inv Δ hΔ
  have h2 : Δ⁻¹ * Δ = 1 := Matrix.nonsing_inv_mul Δ hΔ
  rw [Matrix.fromRows_mul, Matrix.fromRows_mul_fromCols, h1, Matrix.one_mul, Matrix.one_mul,
    Matrix.mul_assoc V Δ⁻¹ Δ, h2, Matrix.mul_one]

/-- **The completion is unit-Jacobian: `det G₀ = 1`.** `G₀ = [[I_r, 0], [S, I_{n−r}]]` (with
`S = V Δ⁻¹`) is unitriangular, so its determinant is `1` — the reduction change of variables has
Jacobian `1`. -/
theorem deepReduce_G0_det_eq_one {r nr : ℕ} (S : Matrix (Fin nr) (Fin r) ℝ) :
    (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℝ) 0 S 1).det = 1 := by
  rw [Matrix.det_fromBlocks_zero₁₂]; simp

/-- **The unit-Jacobian change of variables (raw-pi form).** Right-multiplying the free layer
`L : Fin m → Fin n → ℝ` by any `|det G| = 1` matrix `G` preserves the Lebesgue lintegral:

    ∫⁻ L, g (fun i ↦ L i ᵥ* G)  =  ∫⁻ L, g L .

The "product-layer reduction" CoV of design §2.2 is the instance `G = G₀` (`deepReduce_G0_det_eq_one`
certifies `|det G₀| = 1`). Reuses the banked raw-pi `lintegral_comp_rightMulₚ` (dodging the
`Matrix.module` vs `NormedSpace.toModule` measure diamond, lean/CLAUDE.md); the Jacobian factor
`|det G|^m = 1` collapses. -/
theorem deepReduce_cov {m n : ℕ} (G : Matrix (Fin n) (Fin n) ℝ) (hG : |G.det| = 1)
    (g : (Fin m → Fin n → ℝ) → ℝ≥0∞) (hg : Measurable g) :
    ∫⁻ L : Fin m → Fin n → ℝ, g (fun i => L i ᵥ* G) = ∫⁻ L, g L := by
  have hdet : G.det ≠ 0 := by
    intro h; rw [h, abs_zero] at hG; exact zero_ne_one hG
  rw [lintegral_comp_rightMulₚ m G hdet g hg, hG]
  simp

/-- **Rank preservation under a right inverse.** If `D · D' = 1` then `rank(X · D) = rank X`: `D`
has a right inverse, so `X = (X·D)·D'` is recovered from `X·D` and the rank cannot drop. Stated over
arbitrary Fintype index types (the pivot rows `D = fromCols Δ U` carry a sum column type). -/
theorem rank_mul_eq_of_mul_eq_one {p q s : Type*} [Fintype q] [Fintype s] [DecidableEq q]
    (X : Matrix p q ℝ) (D : Matrix q s ℝ) (D' : Matrix s q ℝ) (h : D * D' = 1) :
    (X * D).rank = X.rank := by
  refine le_antisymm (Matrix.rank_mul_le_left X D) ?_
  calc X.rank = (X * (D * D')).rank := by rw [h, Matrix.mul_one]
    _ = (X * D * D').rank := by rw [← Matrix.mul_assoc X D D']
    _ ≤ (X * D).rank := Matrix.rank_mul_le_left _ _

/-- **The reduction rank identity on `{E = 0}`.** For any preceding head `X`, the composed rank
through the effective last layer `M = [[Δ,U],[V,VΔ⁻¹U]]` equals the composed rank through the reduced
free last layer `H = X·A·Δ⁻¹`:

    rank(X · M)  =  rank(X · fromRows Δ V · Δ⁻¹) .

Taking `X = B·L` recovers the design's `rank(B·L·M) = rank(B·H)` (`H = L·A·Δ⁻¹`): the pivot rows
`[Δ|U]` (full row rank `r`, right inverse `[[Δ⁻¹],[0]]`) drop out. This is the composite-rank
recursion step of the telescoping resolution. -/
theorem deepReduce_rank {p r nr dc : ℕ}
    (X : Matrix (Fin p) (Fin r ⊕ Fin nr) ℝ)
    (Δ : Matrix (Fin r) (Fin r) ℝ) (U : Matrix (Fin r) (Fin dc) ℝ)
    (V : Matrix (Fin nr) (Fin r) ℝ) (hΔ : IsUnit Δ.det) :
    (X * Matrix.fromBlocks Δ U V (V * Δ⁻¹ * U)).rank
      = (X * Matrix.fromRows Δ V * Δ⁻¹).rank := by
  -- `X · M = (X·A·Δ⁻¹) · D` on `{E = 0}` (skeleton + reassociation with explicit `mul_assoc` args,
  -- dodging the dependent-`HMul` higher-order matching whnf blowup, lean/CLAUDE.md).
  have hM : X * Matrix.fromBlocks Δ U V (V * Δ⁻¹ * U)
      = X * Matrix.fromRows Δ V * Δ⁻¹ * Matrix.fromCols Δ U := by
    rw [deepReduce_skeleton Δ U V hΔ,
      ← Matrix.mul_assoc X (Matrix.fromRows Δ V * Δ⁻¹) (Matrix.fromCols Δ U),
      ← Matrix.mul_assoc X (Matrix.fromRows Δ V) Δ⁻¹]
  -- `D = fromCols Δ U` (the pivot rows) has right inverse `[[Δ⁻¹],[0]]`, so `rank(·D) = rank ·`.
  rw [hM]
  exact rank_mul_eq_of_mul_eq_one (X * Matrix.fromRows Δ V * Δ⁻¹) (Matrix.fromCols Δ U)
    (Matrix.fromRows Δ⁻¹ 0)
    (by rw [Matrix.fromCols_mul_fromRows, Matrix.mul_nonsing_inv Δ hΔ, Matrix.mul_zero, add_zero])

/-! ## Non-vacuity witnesses -/

/-- The pivot hypothesis is satisfiable: the identity pivot `Δ = I₂` is a unit. -/
example : IsUnit (1 : Matrix (Fin 2) (Fin 2) ℝ).det := by simp

/-- Non-vacuity of the skeleton and the reduction rank identity at a concrete `2×2` pivot cell
(`Δ = I₂` a unit, `U`, `V`, head `X` arbitrary): both theorems apply, yielding a genuine matrix
factorization and a rank equality. -/
example (U : Matrix (Fin 2) (Fin 3) ℝ) (V : Matrix (Fin 4) (Fin 2) ℝ)
    (X : Matrix (Fin 5) (Fin 2 ⊕ Fin 4) ℝ)
    (hΔ : IsUnit (1 : Matrix (Fin 2) (Fin 2) ℝ).det) : True := by
  have _hskel := deepReduce_skeleton (1 : Matrix (Fin 2) (Fin 2) ℝ) U V hΔ
  have _hrank := deepReduce_rank X (1 : Matrix (Fin 2) (Fin 2) ℝ) U V hΔ
  trivial

/-- Non-vacuity of the unit-Jacobian determinant: the completion `[[I₂,0],[S,I₁]]` has `det = 1`
for any coupling block `S`. -/
example (S : Matrix (Fin 1) (Fin 2) ℝ) :
    (Matrix.fromBlocks (1 : Matrix (Fin 2) (Fin 2) ℝ) 0 S 1).det = 1 :=
  deepReduce_G0_det_eq_one S

end DeepAtlas

end DLNFibre.DLN.RLCT
