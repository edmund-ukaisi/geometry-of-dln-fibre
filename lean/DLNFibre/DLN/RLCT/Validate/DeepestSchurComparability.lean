import DLNFibre.DLN.RLCT.Validate.DeepestGaugeBlocks

/-!
# `DLNFibre.DLN.RLCT.Validate.DeepestSchurComparability` — the S5c germ atom

The matrix-algebra core of the S5c sub-obligation of `framedParams_split_eq_frame_raw`
(`DeepestGaugeConstruction`): the GLOBAL product Schur complement `R` and the product of the
per-layer Schur cores `∏S_s` are comparable **on the deepest-point germ** (NOT uniformly on a box).
Design cert: `expeditions/2026-06-20-aoyagi-full/threads/31-pin2-comparability/s5c-r2-cert.md`
(+ `s5c-cert.md`).

## The exact middle-factor identity (L = 2, all `r, M`; verified r=1/M=2 and r=2/M=1)

Block-LDU of the two-layer product gives the **exact** middle-factor form
`R = S0 · W · S1`, `W = I_M − Z1 · A⁻¹ · Y0`, `A = a0·a1 + Y0·Z1` the global product pivot (`A → I_r`
at the deepest point, so `A⁻¹` is bounded). The product of per-layer Schur cores is `∏S = S0 · S1`,
so the remainder is the **exact ring identity**

    R − ∏S = S0 · (W − I_M) · S1 = − S0 · (Z1 · A⁻¹ · Y0) · S1.

## The germ scope (the load-bearing subtlety, Codex-confirmed)

The naive two-sided box ratio `∑‖R‖² ≍ ∑‖∏S‖²` is **FALSE** for `M > 1` off-germ (rank-deficient
witness `S0 = εE₁₂, S1 = εE₂₁` ⇒ `∏S = ε²E₁₁ ≠ 0` but `W[1,1] = 0` forces `R = 0`). What HOLDS, and
what the germ-invariant `rlctAt` needs, is the **in-sum difference bound**: with `K := Z1 · A⁻¹ · Y0`
(the off-pivot correction, `= O(ε²)` since `Z1, Y0 = O(ε)`, `A⁻¹ = O(1)`), the remainder
`D := R − ∏S = − S0 · K · S1` has Frobenius energy bounded sub-multiplicatively, and

    |∑‖R‖² − ∑‖∏S‖²| ≤ 2·(cross term) + ∑‖D‖²    (the difference-of-squared-Frobenius split)

with the cross term Cauchy–Schwarz-bounded by `∑‖∏S‖² · ∑‖D‖²`. The consumer charges `∑‖D‖²` to the
regular energy `∑E²` (via `‖Z1‖, ‖Y0‖ ≤ √(∑E²)`, the regular blocks near the deepest point) — that
charge depends on the `deepestSplit` apparatus and lives downstream; this file delivers the
**network-free matrix-algebra core**: the exact remainder identity + the Frobenius
sub-multiplicative remainder bound + the difference-of-squared-Frobenius germ bound.

## Status

The pieces below are pure `Matrix`/`Finset` algebra (no `deepestSplit`, no `Params`). The named atom
`schur_core_germ_comparability` bundles them. Axiom-clean (`[propext, Classical.choice, Quot.sound]`).
-/

open Matrix
open scoped BigOperators
namespace DLNFibre.DLN.RLCT

/-- The squared-Frobenius energy `∑ᵢ ∑ⱼ (X i j)²` of a matrix. The loss/energy currency throughout
the deepest-point squeeze (`dlnLoss`, `deepestCoreF`, the block residuals are all this shape). -/
def frobSq {m n : Type*} [Fintype m] [Fintype n] (X : Matrix m n ℝ) : ℝ :=
  ∑ i, ∑ j, (X i j) ^ 2

/-- `frobSq` is nonnegative (a sum of squares). -/
theorem frobSq_nonneg {m n : Type*} [Fintype m] [Fintype n] (X : Matrix m n ℝ) :
    0 ≤ frobSq X :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- `frobSq (-X) = frobSq X` (each entry is negated, the square is even). -/
theorem frobSq_neg {m n : Type*} [Fintype m] [Fintype n] (X : Matrix m n ℝ) :
    frobSq (-X) = frobSq X := by
  simp only [frobSq, Matrix.neg_apply, neg_sq]

/-! ## The two-layer Schur-complement LDU identity (the frame-free `hR` for the germ charge)

The S5c atom below consumes `hR : R = S0·(1−K)·S1` for the GLOBAL product Schur complement `R`. These
network-free `Matrix`-algebra lemmas SUPPLY that `hR` for the L = 2 two-layer product: the Schur
complement of `(fromBlocks A0 Y0 Z0 T0)·(fromBlocks A1 Y1 Z1 T1)` over the product pivot
`P = A0·A1 + Y0·Z1` equals the middle-factor form of the per-layer Schur cores. The producer's frame
stripping (the banked `hconj` chain) reduces its framed product to exactly this frame-free `∏C_s`, so
`schur_product_ldu` delivers the `hR` the germ charge feeds into `schur_core_germ_comparability`.
Design cert: `expeditions/2026-06-20-aoyagi-full/threads/31-pin2-comparability/frame-stripping-cert.md`
(L = 2 only; general-L is a separate induction, not needed for the L = 2 headline). -/

/-- Unipotent-strip invariance of the (1,1)-block Schur complement: for `fromBlocks P Q Rb Sb` with
`P` invertible, the Schur complement `Sb − Rb·⅟P·Q` is unchanged after a lower-unipotent left factor
`fromBlocks 1 0 X 1` and an upper-unipotent right factor `fromBlocks 1 V 0 1`. Pure inverse-cancel
algebra (`P·⅟P = 1` localizes the cancellation). -/
theorem schur_unipotent_strip {r n0 n2 : Type*} [Fintype r] [DecidableEq r]
    [Fintype n0] [DecidableEq n0] [Fintype n2] [DecidableEq n2]
    {α : Type*} [CommRing α]
    (P : Matrix r r α) (Q : Matrix r n2 α) (Rb : Matrix n0 r α) (Sb : Matrix n0 n2 α)
    (X : Matrix n0 r α) (V : Matrix r n2 α) [Invertible P] :
    ((Matrix.fromBlocks (1 : Matrix r r α) 0 X 1
        * Matrix.fromBlocks P Q Rb Sb
        * Matrix.fromBlocks (1 : Matrix r r α) V 0 1).toBlocks₂₂)
      - (Matrix.fromBlocks (1 : Matrix r r α) 0 X 1
          * Matrix.fromBlocks P Q Rb Sb
          * Matrix.fromBlocks (1 : Matrix r r α) V 0 1).toBlocks₂₁
        * ⅟P
        * (Matrix.fromBlocks (1 : Matrix r r α) 0 X 1
            * Matrix.fromBlocks P Q Rb Sb
            * Matrix.fromBlocks (1 : Matrix r r α) V 0 1).toBlocks₁₂
      = Sb - Rb * ⅟P * Q := by
  rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  simp only [Matrix.one_mul, Matrix.mul_one, Matrix.zero_mul, Matrix.mul_zero, add_zero,
    Matrix.toBlocks_fromBlocks₂₂, Matrix.toBlocks_fromBlocks₂₁, Matrix.toBlocks_fromBlocks₁₂]
  -- Goal: `(X*P+Rb)*V + (X*Q+Sb) − (X*P+Rb)*⅟P*(P*V+Q) = Sb − Rb*⅟P*Q`.
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc,
    Matrix.mul_invOf_cancel_left, Matrix.invOf_mul_cancel_left,
    Matrix.mul_invOf_cancel_right, Matrix.invOf_mul_cancel_right,
    sub_eq_add_neg, Matrix.neg_mul, Matrix.mul_neg]
  abel

/-- `a·c − a·k·c = a·(1 − k)·c` for a square middle factor `k` (rectangular outer widths `m0, m2`).
The clean final factoring of the two-layer Schur identity (`a = S0 : m0×m1`, `c = S1 : m1×m2`,
`k = Z1·⅟P·Y0 : m1×m1`), stated abstractly so it dodges the `set`-abbreviation unfolding that
`Matrix.mul_sub` would otherwise trigger on `S1`'s body. -/
theorem factor_one_sub_middle {m0 m1 m2 : Type*} [Fintype m1] [DecidableEq m1]
    {α : Type*} [CommRing α] (a : Matrix m0 m1 α) (k : Matrix m1 m1 α) (c : Matrix m1 m2 α) :
    a * c - a * k * c = a * (1 - k) * c := by
  rw [Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul, Matrix.mul_assoc]

/-- The middle LDU factor of the two-layer product collapses to a single block matrix with the global
pivot `P = A0·A1 + Y0·Z1` and the per-layer Schur cores `S0, S1` (rectangular outer widths `m0, m2`,
shared middle `m1`): `D0·(U0·L1)·D1 = fromBlocks P (Y0·S1) (S0·Z1) (S0·S1)`. -/
theorem schur_middle_ldu_blocks {r m0 m1 m2 : Type*} [Fintype r] [DecidableEq r]
    [Fintype m1] [DecidableEq m1]
    {α : Type*} [CommRing α]
    (A0 A1 : Matrix r r α) (Y0 : Matrix r m1 α) (Z1 : Matrix m1 r α)
    (S0 : Matrix m0 m1 α) (S1 : Matrix m1 m2 α) [Invertible A0] [Invertible A1] :
    Matrix.fromBlocks A0 (0 : Matrix r m1 α) (0 : Matrix m0 r α) S0 *
        (Matrix.fromBlocks (1 : Matrix r r α) (⅟A0 * Y0) (0 : Matrix m1 r α) 1 *
          Matrix.fromBlocks (1 : Matrix r r α) (0 : Matrix r m1 α) (Z1 * ⅟A1) 1) *
        Matrix.fromBlocks A1 (0 : Matrix r m2 α) (0 : Matrix m1 r α) S1
      = Matrix.fromBlocks (A0 * A1 + Y0 * Z1) (Y0 * S1) (S0 * Z1) (S0 * S1) := by
  rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply,
    Matrix.fromBlocks_inj]
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp only [Matrix.mul_zero, Matrix.zero_mul, Matrix.one_mul, Matrix.mul_one,
      add_zero, zero_add, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc,
      Matrix.mul_invOf_cancel_left, Matrix.invOf_mul_cancel_left,
      Matrix.mul_invOf_cancel_right, Matrix.invOf_mul_cancel_right,
      mul_invOf_self, invOf_mul_self] <;>
    abel

/-- **The two-layer Schur-complement LDU identity** (the genuinely new bridge for the deepest-point
germ charge; RECTANGULAR outer widths `m0, m2`, shared middle `m1`). The GLOBAL (1,1)-block Schur
complement of the product of two gauge-sliced layers `(fromBlocks A0 Y0 Z0 T0)·(fromBlocks A1 Y1 Z1 T1)`
— with `C0 : (r⊕m0)×(r⊕m1)`, `C1 : (r⊕m1)×(r⊕m2)` — over the product pivot `P = A0·A1 + Y0·Z1` equals
the middle-factor form `S0·(1 − K)·S1` of the per-layer Schur cores `S0 = T0 − Z0·⅟A0·Y0 : m0×m1`,
`S1 = T1 − Z1·⅟A1·Y1 : m1×m2`, with `K = Z1·⅟P·Y0 : m1×m1` the off-pivot correction. This is the `hR`
hypothesis the S5c atom `schur_core_germ_comparability` consumes. The producer's Schur complement is
genuinely rectangular (`(H0−r)×(Hlast−r)`, `H0 ≠ Hlast`), so the three-width form is load-bearing.
Verified TRUE by sympy across `r, m0, m1, m2` shapes. -/
theorem schur_product_ldu {r m0 m1 m2 : Type*} [Fintype r] [DecidableEq r]
    [Fintype m0] [DecidableEq m0] [Fintype m1] [DecidableEq m1] [Fintype m2] [DecidableEq m2]
    {α : Type*} [CommRing α]
    (A0 A1 : Matrix r r α) (Y0 : Matrix r m1 α) (Y1 : Matrix r m2 α)
    (Z0 : Matrix m0 r α) (Z1 : Matrix m1 r α) (T0 : Matrix m0 m1 α) (T1 : Matrix m1 m2 α)
    [Invertible A0] [Invertible A1]
    [hP : Invertible (A0 * A1 + Y0 * Z1)] :
    (Z0 * Y1 + T0 * T1)
        - (Z0 * A1 + T0 * Z1) * ⅟(A0 * A1 + Y0 * Z1) * (A0 * Y1 + Y0 * T1)
      = (T0 - Z0 * ⅟A0 * Y0)
          * (1 - Z1 * ⅟(A0 * A1 + Y0 * Z1) * Y0)
          * (T1 - Z1 * ⅟A1 * Y1) := by
  -- Abbreviations (NOT `set P`: that would copy `hP` to a fresh instance whose `⅟` differs).
  set S0 : Matrix m0 m1 α := T0 - Z0 * ⅟A0 * Y0 with hS0def
  set S1 : Matrix m1 m2 α := T1 - Z1 * ⅟A1 * Y1 with hS1def
  -- The raw product equals the LDU sandwich `L0 · (middle) · U1`.
  have hC0 : Matrix.fromBlocks A0 Y0 Z0 T0
      = Matrix.fromBlocks (1 : Matrix r r α) (0 : Matrix r m0 α) (Z0 * ⅟A0)
            (1 : Matrix m0 m0 α)
        * Matrix.fromBlocks A0 (0 : Matrix r m1 α) (0 : Matrix m0 r α) S0
        * Matrix.fromBlocks (1 : Matrix r r α) (⅟A0 * Y0) (0 : Matrix m1 r α)
            (1 : Matrix m1 m1 α) := by
    rw [hS0def]; exact Matrix.fromBlocks_eq_of_invertible₁₁ A0 Y0 Z0 T0
  have hC1 : Matrix.fromBlocks A1 Y1 Z1 T1
      = Matrix.fromBlocks (1 : Matrix r r α) (0 : Matrix r m1 α) (Z1 * ⅟A1)
            (1 : Matrix m1 m1 α)
        * Matrix.fromBlocks A1 (0 : Matrix r m2 α) (0 : Matrix m1 r α) S1
        * Matrix.fromBlocks (1 : Matrix r r α) (⅟A1 * Y1) (0 : Matrix m2 r α)
            (1 : Matrix m2 m2 α) := by
    rw [hS1def]; exact Matrix.fromBlocks_eq_of_invertible₁₁ A1 Y1 Z1 T1
  -- `C0·C1 = L0 · (D0·(U0·L1)·D1) · U1`, with the middle collapsed by `schur_middle_ldu_blocks`.
  have hprod : Matrix.fromBlocks A0 Y0 Z0 T0 * Matrix.fromBlocks A1 Y1 Z1 T1
      = Matrix.fromBlocks (1 : Matrix r r α) 0 (Z0 * ⅟A0) 1
          * Matrix.fromBlocks (A0 * A1 + Y0 * Z1) (Y0 * S1) (S0 * Z1) (S0 * S1)
          * Matrix.fromBlocks (1 : Matrix r r α) (⅟A1 * Y1) 0 1 := by
    rw [hC0, hC1, ← schur_middle_ldu_blocks A0 A1 Y0 Z1 S0 S1]
    simp only [Matrix.mul_assoc]
  -- The explicit product blocks (LHS Schur) match `toBlocks` of the raw product.
  have hblk : Matrix.fromBlocks A0 Y0 Z0 T0 * Matrix.fromBlocks A1 Y1 Z1 T1
      = Matrix.fromBlocks (A0 * A1 + Y0 * Z1) (A0 * Y1 + Y0 * T1)
          (Z0 * A1 + T0 * Z1) (Z0 * Y1 + T0 * T1) := by
    rw [Matrix.fromBlocks_multiply]
  -- Read off the Schur complement of the raw product from its explicit blocks, then strip.
  -- Instantiate at `A0*A1+Y0*Z1` so the `Invertible` instance is `hP` (no `set`-copy mismatch).
  have hstrip := schur_unipotent_strip (A0 * A1 + Y0 * Z1) (Y0 * S1) (S0 * Z1) (S0 * S1)
    (Z0 * ⅟A0) (⅟A1 * Y1)
  rw [← hprod, hblk] at hstrip
  simp only [Matrix.toBlocks_fromBlocks₂₂, Matrix.toBlocks_fromBlocks₂₁,
    Matrix.toBlocks_fromBlocks₁₂] at hstrip
  -- `hstrip : (Z0Y1+T0T1) − (Z0A1+T0Z1)·⅟P·(A0Y1+Y0T1) = S0·S1 − (S0·Z1)·⅟P·(Y0·S1)`.
  rw [hstrip]
  -- Final factoring: `S0·S1 − S0·(Z1·⅟P·Y0)·S1 = S0·(1 − Z1·⅟P·Y0)·S1`.
  have hassoc : S0 * Z1 * ⅟(A0 * A1 + Y0 * Z1) * (Y0 * S1)
      = S0 * (Z1 * ⅟(A0 * A1 + Y0 * Z1) * Y0) * S1 := by
    simp only [Matrix.mul_assoc]
  rw [hassoc, factor_one_sub_middle]

/-- **The Schur-core remainder identity** (exact ring algebra, L = 2). With the global product Schur
complement written in middle-factor form `R = S0 · (1 − K) · S1` (the block-LDU output, `K = Z1·A⁻¹·Y0`
the off-pivot correction), the deviation of `R` from the product of per-layer cores `∏S = S0·S1` is
exactly `− S0 · K · S1`. Pure `Ring`/`Matrix` distribution — no germ, no norm. -/
theorem schur_core_remainder_identity {m0 m1 m2 : Type*} [Fintype m1] [DecidableEq m1]
    (S0 : Matrix m0 m1 ℝ) (S1 : Matrix m1 m2 ℝ) (K : Matrix m1 m1 ℝ) (R : Matrix m0 m2 ℝ)
    (hR : R = S0 * (1 - K) * S1) :
    R - S0 * S1 = - (S0 * K * S1) := by
  subst hR
  rw [Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul]
  abel

/-- **The Frobenius sub-multiplicative remainder bound** (the germ-order accounting). The remainder
`D = − S0·K·S1` (hence `R − ∏S`) has squared-Frobenius energy bounded by the product of the three
factor energies: `∑‖S0·K·S1‖² ≤ (∑‖S0‖²)·(∑‖K‖²)·(∑‖S1‖²)`. This is what makes the remainder **higher
order** on the germ: with `S0, S1 = O(ε)` and `K = O(ε²)`, the bound is `O(ε⁶)`, charged to the
`O(ε²)` regular energy by the consumer. Two `frobenius_mul_le` + `frobSq_nonneg` monotonicity. -/
theorem schur_core_remainder_frobeniusSq_le {m0 m1 m2 : Type*} [Fintype m0] [Fintype m1] [Fintype m2]
    (S0 : Matrix m0 m1 ℝ) (S1 : Matrix m1 m2 ℝ) (K : Matrix m1 m1 ℝ) :
    frobSq (S0 * K * S1) ≤ frobSq S0 * frobSq K * frobSq S1 := by
  -- `∑‖(S0·K)·S1‖² ≤ (∑‖S0·K‖²)·(∑‖S1‖²) ≤ (∑‖S0‖²·∑‖K‖²)·(∑‖S1‖²)`.
  simp only [frobSq]
  have h1 : (∑ i, ∑ j, ((S0 * K * S1) i j) ^ 2)
      ≤ (∑ i, ∑ k, ((S0 * K) i k) ^ 2) * (∑ j, ∑ k, (S1 k j) ^ 2) :=
    frobenius_mul_le (S0 * K) S1
  have h2 : (∑ i, ∑ k, ((S0 * K) i k) ^ 2)
      ≤ (∑ i, ∑ k, (S0 i k) ^ 2) * (∑ j, ∑ k, (K k j) ^ 2) :=
    frobenius_mul_le S0 K
  have hS1nn : (0 : ℝ) ≤ ∑ j, ∑ k, (S1 k j) ^ 2 :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  -- The `K`/`S1` factors of `frobenius_mul_le` are column-major (`∑ j ∑ k · k j`); normalise both to
  -- the row-major `frobSq` orientation by `Finset.sum_comm`.
  have hKcomm : (∑ j, ∑ k, (K k j) ^ 2) = ∑ i, ∑ j, (K i j) ^ 2 := Finset.sum_comm
  have hS1comm : (∑ j, ∑ k, (S1 k j) ^ 2) = ∑ i, ∑ j, (S1 i j) ^ 2 := Finset.sum_comm
  rw [hKcomm] at h2
  rw [hS1comm] at h1 hS1nn
  calc (∑ i, ∑ j, ((S0 * K * S1) i j) ^ 2)
      ≤ (∑ i, ∑ k, ((S0 * K) i k) ^ 2) * (∑ i, ∑ j, (S1 i j) ^ 2) := h1
    _ ≤ ((∑ i, ∑ k, (S0 i k) ^ 2) * (∑ i, ∑ j, (K i j) ^ 2)) * (∑ i, ∑ j, (S1 i j) ^ 2) :=
        mul_le_mul_of_nonneg_right h2 hS1nn

/-- **The double-sum Cauchy–Schwarz cross-term bound** (the squared form, sqrt-free). For two
matrices the entrywise inner product squared is bounded by the product of their squared-Frobenius
energies: `(∑ᵢⱼ X i j · Y i j)² ≤ frobSq X · frobSq Y`. The flattened (`Fintype.sum_prod_type'`)
Cauchy–Schwarz (`Finset.sum_mul_sq_le_sq_mul_sq`). Bounds the cross term in the difference split. -/
theorem frobInner_sq_le {m n : Type*} [Fintype m] [Fintype n] (X Y : Matrix m n ℝ) :
    (∑ i, ∑ j, X i j * Y i j) ^ 2 ≤ frobSq X * frobSq Y := by
  simp only [frobSq]
  -- Flatten the double sums over `m × n`, then single-index Cauchy–Schwarz.
  rw [← Fintype.sum_prod_type' (fun i j => X i j * Y i j),
      ← Fintype.sum_prod_type' (fun i j => (X i j) ^ 2),
      ← Fintype.sum_prod_type' (fun i j => (Y i j) ^ 2)]
  exact Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun p : m × n => X p.1 p.2) (fun p : m × n => Y p.1 p.2)

/-- **The difference-of-squared-Frobenius split** (route-independent algebra). Writing `R = ∏S + D`
(`∏S := S0·S1`, `D := R − ∏S` the remainder), the squared-Frobenius energies satisfy the exact
expansion `frobSq R = frobSq ∏S + 2·⟨∏S, D⟩ + frobSq D`. Pure `Finset` distribution (`(a+b)² =
a² + 2ab + b²` entrywise). -/
theorem frobSq_add_eq {m n : Type*} [Fintype m] [Fintype n] (P D : Matrix m n ℝ) :
    frobSq (P + D) = frobSq P + 2 * (∑ i, ∑ j, P i j * D i j) + frobSq D := by
  simp only [frobSq, Matrix.add_apply]
  -- Per-entry `(P + D)² = P² + 2·P·D + D²`, then split the double sums.
  have hentry : ∀ i, (∑ j, (P i j + D i j) ^ 2)
      = (∑ j, (P i j) ^ 2) + 2 * (∑ j, P i j * D i j) + (∑ j, (D i j) ^ 2) := by
    intro i
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [Finset.sum_congr rfl fun i _ => hentry i]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.mul_sum]

/-- **The S5c germ-comparability atom** (the named deliverable; design cert `s5c-r2-cert.md`). NAME =
the four difference-bound INGREDIENTS that make the germ comparability `∑‖R‖² ≍ ∑‖∏S‖²` derivable —
NOT a standalone comparability (the `∑E²` charge that closes it lives in the consumer; see below). For
the L = 2 reduced core, the global product Schur complement `R` (in middle-factor form
`R = S0·(1−K)·S1`, `K = Z1·A⁻¹·Y0` the off-pivot correction) and the product of per-layer Schur cores
`∏S = S0·S1`: the squared-Frobenius energies differ by exactly `2·⟨∏S, D⟩ + frobSq D`, where
`D = R − ∏S = −S0·K·S1` is the remainder, whose energy is sub-multiplicatively bounded
`frobSq D ≤ frobSq S0·frobSq K·frobSq S1`.

This is the GERM (in-sum) form, NOT a uniform two-sided box ratio (the box ratio
`∑‖R‖² ≍ ∑‖∏S‖²` is FALSE for `M > 1` off-germ; cert). The consumer charges `frobSq D` to the
regular energy `∑E²` (since `K = Z1·A⁻¹·Y0 = O(ε²)` is charged via `‖Z1‖, ‖Y0‖ ≤ √(∑E²)`). The cross
term is bounded sqrt-free via `frobInner_sq_le`: `(⟨∏S, D⟩)² ≤ frobSq ∏S · frobSq D`. Bundles
`schur_core_remainder_identity` (exact `D = −S0·K·S1`) + `frobSq_add_eq` + `frobInner_sq_le` +
`schur_core_remainder_frobeniusSq_le`. -/
theorem schur_core_germ_comparability {m0 m1 m2 : Type*} [Fintype m0] [Fintype m1] [DecidableEq m1]
    [Fintype m2]
    (S0 : Matrix m0 m1 ℝ) (S1 : Matrix m1 m2 ℝ) (K : Matrix m1 m1 ℝ) (R : Matrix m0 m2 ℝ)
    (hR : R = S0 * (1 - K) * S1) :
    -- (i) the exact remainder identity: `R − ∏S = −S0·K·S1`
    (R - S0 * S1 = - (S0 * K * S1))
    -- (ii) the sub-multiplicative remainder energy bound
    ∧ frobSq (R - S0 * S1) ≤ frobSq S0 * frobSq K * frobSq S1
    -- (iii) the in-sum difference-of-squared-Frobenius split (germ form): the energies of `R` and
    --       `∏S` differ by exactly twice the cross term plus the remainder energy
    ∧ (frobSq R = frobSq (S0 * S1) + 2 * (∑ i, ∑ j, (S0 * S1) i j * (R - S0 * S1) i j)
          + frobSq (R - S0 * S1))
    -- (iv) the cross term is Cauchy–Schwarz-controlled by the two energies
    ∧ (∑ i, ∑ j, (S0 * S1) i j * (R - S0 * S1) i j) ^ 2
        ≤ frobSq (S0 * S1) * frobSq (R - S0 * S1) := by
  have hid : R - S0 * S1 = - (S0 * K * S1) := schur_core_remainder_identity S0 S1 K R hR
  refine ⟨hid, ?_, ?_, frobInner_sq_le (S0 * S1) (R - S0 * S1)⟩
  · -- (ii): `frobSq (R − ∏S) = frobSq (−S0·K·S1) = frobSq (S0·K·S1)`, then sub-multiplicativity.
    rw [hid, frobSq_neg]
    exact schur_core_remainder_frobeniusSq_le S0 S1 K
  · -- (iii): `R = ∏S + D` with `D := R − ∏S` frozen, then `frobSq_add_eq`.
    set D := R - S0 * S1 with hD
    have hRsplit : R = S0 * S1 + D := by rw [hD]; abel
    rw [hRsplit]; exact frobSq_add_eq (S0 * S1) D

/-! ## Non-vacuity witness (RECTANGULAR instance)

The atom's antecedent `R = S0·(1−K)·S1` is inhabited with a genuinely nonzero off-pivot correction
`K ≠ 0` AND genuinely RECTANGULAR off-diagonals (the three-width generalization is exercised, not the
square special case). Take `m0 = Fin 2`, `m1 = m2 = Fin 1`: `S0 = ![1, 0]ᵀ : 2×1`, `K = [1/2] : 1×1`,
`S1 = [1] : 1×1`, `R = S0·(1−K)·S1 = ![1/2, 0]ᵀ`. Then `R − ∏S = ![−1/2, 0]ᵀ ≠ 0` — the remainder is
genuinely nonzero (the bound is not the empty `0 ≤ 0`), on a non-square shape. -/
example :
    let S0 : Matrix (Fin 2) (Fin 1) ℝ := Matrix.of fun i _ => if i = 0 then (1 : ℝ) else 0
    let K : Matrix (Fin 1) (Fin 1) ℝ := Matrix.of fun _ _ => (1 : ℝ) / 2
    let S1 : Matrix (Fin 1) (Fin 1) ℝ := 1
    let R : Matrix (Fin 2) (Fin 1) ℝ := S0 * (1 - K) * S1
    -- the off-pivot correction is genuinely nonzero, so the rectangular remainder is genuinely nonzero
    K ≠ 0 ∧ R - S0 * S1 ≠ 0 := by
  refine ⟨?_, ?_⟩
  · intro h
    have := congrFun (congrFun h 0) 0
    simp [Matrix.of_apply, Matrix.zero_apply] at this
  · intro h
    have hid := schur_core_remainder_identity (m0 := Fin 2) (m1 := Fin 1) (m2 := Fin 1)
      (Matrix.of fun i _ => if i = 0 then (1 : ℝ) else 0)
      (1 : Matrix (Fin 1) (Fin 1) ℝ) (Matrix.of fun _ _ => (1 : ℝ) / 2)
      ((Matrix.of fun i _ => if i = 0 then (1 : ℝ) else 0)
        * (1 - Matrix.of fun _ _ => (1 : ℝ) / 2) * (1 : Matrix (Fin 1) (Fin 1) ℝ)) rfl
    rw [h] at hid
    -- `0 = −(S0·K·S1)`, but `(S0·K·S1) 0 0 = 1·(1/2)·1 = 1/2 ≠ 0`.
    have := congrFun (congrFun hid.symm 0) 0
    simp [Matrix.mul_apply, Matrix.of_apply, Matrix.neg_apply] at this
end DLNFibre.DLN.RLCT
