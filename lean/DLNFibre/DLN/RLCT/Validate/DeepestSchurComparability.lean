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

/-- **The Schur-core remainder identity** (exact ring algebra, L = 2). With the global product Schur
complement written in middle-factor form `R = S0 · (1 − K) · S1` (the block-LDU output, `K = Z1·A⁻¹·Y0`
the off-pivot correction), the deviation of `R` from the product of per-layer cores `∏S = S0·S1` is
exactly `− S0 · K · S1`. Pure `Ring`/`Matrix` distribution — no germ, no norm. -/
theorem schur_core_remainder_identity {M : Type*} [Fintype M] [DecidableEq M]
    (S0 S1 K R : Matrix M M ℝ) (hR : R = S0 * (1 - K) * S1) :
    R - S0 * S1 = - (S0 * K * S1) := by
  subst hR
  rw [Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul]
  abel

/-- **The Frobenius sub-multiplicative remainder bound** (the germ-order accounting). The remainder
`D = − S0·K·S1` (hence `R − ∏S`) has squared-Frobenius energy bounded by the product of the three
factor energies: `∑‖S0·K·S1‖² ≤ (∑‖S0‖²)·(∑‖K‖²)·(∑‖S1‖²)`. This is what makes the remainder **higher
order** on the germ: with `S0, S1 = O(ε)` and `K = O(ε²)`, the bound is `O(ε⁶)`, charged to the
`O(ε²)` regular energy by the consumer. Two `frobenius_mul_le` + `frobSq_nonneg` monotonicity. -/
theorem schur_core_remainder_frobeniusSq_le {M : Type*} [Fintype M]
    (S0 S1 K : Matrix M M ℝ) :
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
theorem schur_core_germ_comparability {M : Type*} [Fintype M] [DecidableEq M]
    (S0 S1 K R : Matrix M M ℝ) (hR : R = S0 * (1 - K) * S1) :
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

/-! ## Non-vacuity witness

The atom's antecedent `R = S0·(1−K)·S1` is inhabited with a genuinely nonzero off-pivot correction
`K ≠ 0`, and the remainder `R − ∏S` is then genuinely nonzero (the bound is not the empty `0 ≤ 0`).
The scalar (`M = Fin 1`) instance with all blocks `= t`: `R = t²(1−t)`, `∏S = t²`, remainder `= −t³`,
and the sub-multiplicative bound is `t⁶ ≤ t²·t²·t²` — TIGHT (equality), confirming the bound is sharp
in the worst (full-rank scalar) case, not slack-by-construction. -/
example :
    let t : ℝ := (1 : ℝ) / 2
    let S : Matrix (Fin 1) (Fin 1) ℝ := Matrix.of fun _ _ => t
    let K : Matrix (Fin 1) (Fin 1) ℝ := Matrix.of fun _ _ => t
    let R : Matrix (Fin 1) (Fin 1) ℝ := S * (1 - K) * S
    -- the off-pivot correction is genuinely nonzero, so the remainder is genuinely nonzero
    K ≠ 0 ∧ R - S * S ≠ 0 := by
  refine ⟨?_, ?_⟩
  · intro h
    have := congrFun (congrFun h 0) 0
    simp [Matrix.of_apply, Matrix.zero_apply] at this
  · intro h
    have hid := schur_core_remainder_identity (M := Fin 1)
      (Matrix.of fun _ _ => (1 : ℝ) / 2) (Matrix.of fun _ _ => (1 : ℝ) / 2)
      (Matrix.of fun _ _ => (1 : ℝ) / 2)
      ((Matrix.of fun _ _ => (1 : ℝ) / 2) * (1 - Matrix.of fun _ _ => (1 : ℝ) / 2)
        * (Matrix.of fun _ _ => (1 : ℝ) / 2)) rfl
    rw [h] at hid
    -- `0 = −(S·K·S)`, but `(S·K·S) 0 0 = (1/2)³ ≠ 0`.
    have := congrFun (congrFun hid.symm 0) 0
    simp [Matrix.mul_apply, Matrix.of_apply, Matrix.neg_apply] at this
end DLNFibre.DLN.RLCT
