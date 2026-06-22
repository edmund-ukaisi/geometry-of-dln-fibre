import DLNFibre.Core.CTheta
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.WellKnown

/-!
# `DLNFibre.Core.QSeries` — the q-series primitives (M1)

The generating-function objects of Lehalleur–Rimányi 2024 §5, as formal power series over `ℤ`
(`PowerSeries ℤ`, written `ℤ⟦X⟧`, with the formal variable `X` playing the rôle of `q`). This module
defines the primitives and proves their basic shape facts (constant term `1`, all coefficients
`≥ 0`, small `P 0 = 1` / empty-product helpers). It does **not** attempt the §5 identities (PEEL,
Thm 5.5/5.6, the `(C, θ)`-extraction) — those are later layers (M3/M4) that stand on this bedrock.

**The objects.** For `k ≥ 1`, the inverse-q-Pochhammer factor `(1 − q^k)^{-1}` is the geometric
series `∑_{j≥0} q^{jk}` — over `ℤ⟦X⟧` this is `geomFactor k = mk (fun n ↦ if k ∣ n then 1 else 0)`,
the series with coefficient `1` at multiples of `k` and `0` elsewhere. Then

* `P s = ∏_{k=1}^{s} geomFactor k` (the **inverse q-Pochhammer** `∏_{k=1}^s (1−q^k)^{-1}`);
* `Pm N m = ∏_{0 ≤ i ≤ j ≤ N} P (m (i,j))` (the **Kostant-partition factor**, the upper triangle);
* `Pmult h = ∏_i P (h i)` (the **multiplicity factor** of a dimension vector `h`);
* `Qseries d r = ∑_{m ∈ kostantPartitions d r} X^{codimForm N (extendℤ m)} · Pm N m` (Thm 5.6 LHS).

The exponent `codimForm N (extendℤ m)` is the committed Cor 3.5 form from `Core.CTheta`; it is a `ℤ`
but is `≥ 0` on Kostant partitions (a sum of products of non-negative multiplicities), so its
`toNat` is the honest power. `Qseries` raises `X` to `(codimForm N (extendℤ m)).toNat`.

**The shape facts (what M3/M4 will consume).**

* `geomFactor`, `P`, `Pm`, `Pmult` have **constant term `1`** (`constantCoeff_*`).
* `geomFactor`, `P`, `Pm`, `Pmult` have **all coefficients `≥ 0`** (`coeff_*_nonneg`), via closure
  of the predicate `NonnegCoeffs` under `1`, `*`, and `Finset.prod`.
* the **telescoping** `geomFactor k · (1 − X^k) = 1` for `k ≥ 1` (`geomFactor_mul_one_sub`) pins the
  inverse-Pochhammer reading.
* small helpers: `P_zero` (`P 0 = 1`), `Pmult_const_zero` (`Pmult` of the zero vector is `1`).

**Dependency rule:** `Core` only — never import `DLNFibre.DLN`.
-/

namespace DLNFibre.Core

open PowerSeries Finset

variable {N : ℕ}

/-! ## The non-negativity predicate and its closure

`NonnegCoeffs φ` says every coefficient of `φ : ℤ⟦X⟧` is `≥ 0`. The §5 generating functions are sums
and products of such series, and the `(C, θ)`-extraction (M3) needs that no cancellation occurs in
`Qseries`; the floor for that is that each `Pm m` has non-negative coefficients. The predicate is
closed under `1`, `*`, and `Finset.prod`. -/

/-- `φ : ℤ⟦X⟧` has **all coefficients non-negative**. -/
def NonnegCoeffs (φ : ℤ⟦X⟧) : Prop := ∀ n, 0 ≤ coeff (R := ℤ) n φ

/-- The unit series `1` has non-negative coefficients. -/
theorem nonnegCoeffs_one : NonnegCoeffs 1 := by
  intro n; rw [coeff_one]; split_ifs <;> norm_num

/-- A product of two non-negative-coefficient series has non-negative coefficients: each coefficient
is a `Finset.sum` over the antidiagonal of products of non-negative terms. -/
theorem NonnegCoeffs.mul {φ ψ : ℤ⟦X⟧} (hφ : NonnegCoeffs φ) (hψ : NonnegCoeffs ψ) :
    NonnegCoeffs (φ * ψ) := by
  intro n
  rw [coeff_mul]
  exact Finset.sum_nonneg fun p _ ↦ mul_nonneg (hφ p.1) (hψ p.2)

/-- A `Finset.prod` of non-negative-coefficient series has non-negative coefficients (closure of
`NonnegCoeffs` under finite products). -/
theorem NonnegCoeffs.prod {ι : Type*} (s : Finset ι) (f : ι → ℤ⟦X⟧)
    (hf : ∀ i ∈ s, NonnegCoeffs (f i)) : NonnegCoeffs (∏ i ∈ s, f i) :=
  Finset.prod_induction f NonnegCoeffs (fun _ _ ↦ NonnegCoeffs.mul) nonnegCoeffs_one hf

/-! ## The geometric factor `(1 − q^k)^{-1} = ∑_{j≥0} q^{jk}`

`geomFactor k` is the explicit geometric series with coefficient `1` at multiples of `k` and `0`
elsewhere. For `k ≥ 1` it telescopes against `1 − X^k` to `1`, so it is the inverse of `1 − X^k` and
the "`(1 − q^k)^{-1}`" reading holds. (`geomFactor 0 = 1`, since `0 ∣ n ↔ n = 0`.) -/

/-- The geometric factor with coefficient `1` at multiples of `k` and `0` elsewhere; for `k ≥ 1`
this is `(1 − q^k)^{-1} = ∑_{j≥0} q^{jk}` (see `geomFactor_mul_one_sub`). -/
noncomputable def geomFactor (k : ℕ) : ℤ⟦X⟧ := mk fun n ↦ if k ∣ n then 1 else 0

@[simp] theorem coeff_geomFactor (k n : ℕ) :
    coeff (R := ℤ) n (geomFactor k) = if k ∣ n then 1 else 0 := coeff_mk n _

/-- `geomFactor k` has constant term `1` (`k ∣ 0` always). -/
@[simp] theorem constantCoeff_geomFactor (k : ℕ) :
    constantCoeff (R := ℤ) (geomFactor k) = 1 := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_geomFactor, if_pos (dvd_zero k)]

/-- `geomFactor k` has non-negative coefficients (each is `0` or `1`). -/
theorem nonnegCoeffs_geomFactor (k : ℕ) : NonnegCoeffs (geomFactor k) := by
  intro n; rw [coeff_geomFactor]; split_ifs <;> norm_num

/-- **Telescoping.** For `k ≥ 1`, `geomFactor k · (1 − X^k) = 1`: the geometric series is the
inverse of `1 − X^k`, so the "`(1 − q^k)^{-1}`" reading of `geomFactor` (hence of `P`) holds. -/
theorem geomFactor_mul_one_sub {k : ℕ} (hk : 1 ≤ k) :
    geomFactor k * (1 - X ^ k) = 1 := by
  ext n
  rw [coeff_one]
  -- expand the product coefficient via `mul_sub`, `mul_one`, and `coeff (geomFactor · X^k)`
  rw [mul_sub, mul_one, map_sub, coeff_geomFactor,
    show geomFactor k * X ^ k = X ^ k * geomFactor k from mul_comm _ _, coeff_X_pow_mul']
  by_cases hn : n = 0
  · subst hn
    rw [if_pos (dvd_zero k), if_pos rfl, if_neg (by omega : ¬ k ≤ 0)]; ring
  · rw [if_neg hn]
    by_cases hkle : k ≤ n
    · -- `coeff (n-k) (geomFactor k) = if k ∣ (n-k) then 1 else 0`, and `k ∣ (n-k) ↔ k ∣ n`
      rw [if_pos hkle, coeff_geomFactor]
      have hiff : k ∣ (n - k) ↔ k ∣ n := by
        constructor
        · intro h
          have : (n - k) + k = n := Nat.sub_add_cancel hkle
          exact this ▸ Nat.dvd_add h (dvd_refl k)
        · intro h; exact Nat.dvd_sub h (dvd_refl k)
      by_cases hkn : k ∣ n
      · rw [if_pos hkn, if_pos (hiff.mpr hkn)]; ring
      · rw [if_neg hkn, if_neg (fun h ↦ hkn (hiff.mp h))]; ring
    · -- `k > n`: the `X^k`-shifted term vanishes, and `k ∤ n` (else `k ≤ n`)
      rw [if_neg hkle, if_neg (fun h ↦ hkle (Nat.le_of_dvd (by omega) h))]; ring

/-! ## The inverse q-Pochhammer `P s = ∏_{k=1}^{s} (1 − q^k)^{-1}` -/

/-- The **inverse q-Pochhammer** `P s = ∏_{k=1}^{s} (1 − q^k)^{-1} = ∏_{k=1}^{s} geomFactor k`
(`P 0 = 1`, the empty product). -/
noncomputable def P (s : ℕ) : ℤ⟦X⟧ := ∏ k ∈ Finset.Icc 1 s, geomFactor k

/-- `P 0 = 1` (empty product over `Icc 1 0 = ∅`). -/
@[simp] theorem P_zero : P 0 = 1 := by simp [P]

/-- `P` has constant term `1`: each `geomFactor k` does, and `constantCoeff` is a ring hom. -/
@[simp] theorem constantCoeff_P (s : ℕ) : constantCoeff (R := ℤ) (P s) = 1 := by
  rw [P, map_prod]; exact Finset.prod_eq_one fun k _ ↦ constantCoeff_geomFactor k

/-- `P` has non-negative coefficients (a product of non-negative-coefficient geometric factors). -/
theorem nonnegCoeffs_P (s : ℕ) : NonnegCoeffs (P s) :=
  NonnegCoeffs.prod _ _ fun k _ ↦ nonnegCoeffs_geomFactor k

/-- `0 ≤` every coefficient of `P s` (unfolded form of `nonnegCoeffs_P`). -/
theorem coeff_P_nonneg (s n : ℕ) : 0 ≤ coeff (R := ℤ) n (P s) := nonnegCoeffs_P s n

/-- `P (s+1) = P s · geomFactor (s+1)`: peel the top factor off `Icc 1 (s+1)`. A recurrence M3
will use. -/
theorem P_succ (s : ℕ) : P (s + 1) = P s * geomFactor (s + 1) := by
  rw [P, P, ← Finset.prod_Icc_succ_top (by omega : 1 ≤ s + 1)]

/-! ## `Pm` — the Kostant-partition factor `∏_{0 ≤ i ≤ j ≤ N} P (m (i,j))`

`Pm N m` is the product of `P (m (i,j))` over the upper-triangular pairs `i ≤ j`. The index type
matches `Core.CTheta` (`m : Fin (N+1) × Fin (N+1) → ℕ`); the product runs over the `Finset` of pairs
with `p.1 ≤ p.2`. -/

/-- The upper-triangular pairs `{ (i,j) : i ≤ j }` of `Fin (N+1) × Fin (N+1)`. -/
def upperPairs (N : ℕ) : Finset (Fin (N + 1) × Fin (N + 1)) :=
  Finset.univ.filter fun p ↦ p.1 ≤ p.2

/-- The **Kostant-partition factor** `Pm N m = ∏_{0 ≤ i ≤ j ≤ N} P (m (i,j))`. -/
noncomputable def Pm (N : ℕ) (m : Fin (N + 1) × Fin (N + 1) → ℕ) : ℤ⟦X⟧ :=
  ∏ p ∈ upperPairs N, P (m p)

/-- `Pm` has constant term `1` (a product of `P`-factors, each with constant term `1`). -/
@[simp] theorem constantCoeff_Pm (m : Fin (N + 1) × Fin (N + 1) → ℕ) :
    constantCoeff (R := ℤ) (Pm N m) = 1 := by
  rw [Pm, map_prod]; exact Finset.prod_eq_one fun p _ ↦ constantCoeff_P _

/-- `Pm` has non-negative coefficients (a product of non-negative-coefficient `P`-factors). -/
theorem nonnegCoeffs_Pm (m : Fin (N + 1) × Fin (N + 1) → ℕ) : NonnegCoeffs (Pm N m) :=
  NonnegCoeffs.prod _ _ fun p _ ↦ nonnegCoeffs_P (m p)

/-- `0 ≤` every coefficient of `Pm N m` (unfolded form of `nonnegCoeffs_Pm`). -/
theorem coeff_Pm_nonneg (m : Fin (N + 1) × Fin (N + 1) → ℕ) (n : ℕ) :
    0 ≤ coeff (R := ℤ) n (Pm N m) := nonnegCoeffs_Pm m n

/-! ## `Pmult` — the multiplicity factor `∏_i P (h i)` of a dimension vector -/

/-- The **multiplicity factor** `Pmult h = ∏_i P (h i)` of a dimension vector `h`. -/
noncomputable def Pmult {N : ℕ} (h : Fin (N + 1) → ℕ) : ℤ⟦X⟧ := ∏ i, P (h i)

/-- `Pmult` has constant term `1`. -/
@[simp] theorem constantCoeff_Pmult (h : Fin (N + 1) → ℕ) :
    constantCoeff (R := ℤ) (Pmult h) = 1 := by
  rw [Pmult, map_prod]; exact Finset.prod_eq_one fun i _ ↦ constantCoeff_P _

/-- `Pmult` has non-negative coefficients. -/
theorem nonnegCoeffs_Pmult (h : Fin (N + 1) → ℕ) : NonnegCoeffs (Pmult h) :=
  NonnegCoeffs.prod _ _ fun i _ ↦ nonnegCoeffs_P (h i)

/-- `0 ≤` every coefficient of `Pmult h`. -/
theorem coeff_Pmult_nonneg (h : Fin (N + 1) → ℕ) (n : ℕ) :
    0 ≤ coeff (R := ℤ) n (Pmult h) := nonnegCoeffs_Pmult h n

/-- `Pmult` of the zero vector is `1` (each factor `P 0 = 1`). -/
@[simp] theorem Pmult_const_zero : Pmult (fun _ : Fin (N + 1) ↦ 0) = 1 := by
  rw [Pmult]; exact Finset.prod_eq_one fun i _ ↦ by rw [P_zero]

/-! ## `Qseries` — the Thm 5.6 left-hand-side generating function

`Qseries d r = ∑_{m ∈ kostantPartitions d r} X^{codimForm N (extendℤ m)} · Pm N m`. The exponent is
`(codimForm N (extendℤ m)).toNat` — the form is `≥ 0` on Kostant partitions (a sum of products of
non-negative multiplicities), so `toNat` is the honest exponent. Each summand has non-negative
coefficients, so `Qseries` does too; that non-cancellation is what the M3 `(C, θ)`-extraction rests
on. -/

/-- The **Thm 5.6 generating function**
`Qseries d r = ∑_{m ∈ kostantPartitions d r} X^{codimForm N (extendℤ m)} · Pm N m`,
with the exponent taken as `(codimForm N (extendℤ m)).toNat`. -/
noncomputable def Qseries (d : Fin (N + 1) → ℕ) (r : ℕ) : ℤ⟦X⟧ :=
  ∑ m ∈ kostantPartitions d r,
    (X : ℤ⟦X⟧) ^ (codimForm N (extendℤ m)).toNat * Pm N m

/-- `Qseries` has non-negative coefficients: a sum of `X^c · Pm m` terms, each with non-negative
coefficients (the M3 `(C, θ)`-extraction needs this non-cancellation). -/
theorem nonnegCoeffs_Qseries (d : Fin (N + 1) → ℕ) (r : ℕ) : NonnegCoeffs (Qseries d r) := by
  intro n
  rw [Qseries, map_sum]
  refine Finset.sum_nonneg fun m _ ↦ ?_
  have : NonnegCoeffs ((X : ℤ⟦X⟧) ^ (codimForm N (extendℤ m)).toNat * Pm N m) := by
    refine NonnegCoeffs.mul (fun j ↦ ?_) (nonnegCoeffs_Pm m)
    rw [coeff_X_pow]; split_ifs <;> norm_num
  exact this n

/-- `0 ≤` every coefficient of `Qseries d r`. -/
theorem coeff_Qseries_nonneg (d : Fin (N + 1) → ℕ) (r : ℕ) (n : ℕ) :
    0 ≤ coeff (R := ℤ) n (Qseries d r) := nonnegCoeffs_Qseries d r n

end DLNFibre.Core
