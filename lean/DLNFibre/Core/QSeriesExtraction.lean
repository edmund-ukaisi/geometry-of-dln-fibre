import DLNFibre.Core.QSeries

/-!
# `DLNFibre.Core.QSeriesExtraction` — the `(C, θ)` extraction (M5 / Lemma 5.2)

`cCodim` and `numTop` are recoverable from the generating function `Qseries` (M1): `cCodim` is the
lowest degree with a nonzero coefficient, and `numTop` is that coefficient. This is the bridge that
turns symmetry of `Qseries` (Thm 5.5, manifestly multiset-symmetric) into symmetry of `(C, θ)`.

The mechanism (no cancellation): every `Pm m` has constant term `1` and non-negative coefficients
(M1), and `codimForm (extendℤ m) ≥ 0`, so in `Qseries d r = ∑_m X^{c(m)} · Pm m` with
`c(m) = (codimForm (extendℤ m)).toNat ≥ cCodim`:
* coefficients below `cCodim` vanish (every term starts at degree `c(m) ≥ cCodim`);
* the coefficient at `cCodim` counts the minimisers — `numTop`.
-/

namespace DLNFibre.Core

open PowerSeries Finset

variable {N : ℕ}

/-- `extendℤ m` is pointwise non-negative (it is `0` or a `ℕ`-cast). -/
theorem extendℤ_nonneg (m : Fin (N + 1) × Fin (N + 1) → ℕ) (a b : ℤ) :
    0 ≤ extendℤ m a b := by
  unfold extendℤ; split_ifs with h
  · exact Int.natCast_nonneg _
  · exact le_refl 0

/-- `codimForm (extendℤ m) ≥ 0` — a sum of products of non-negative terms. -/
theorem codimForm_extendℤ_nonneg (m : Fin (N + 1) × Fin (N + 1) → ℕ) :
    0 ≤ codimForm N (extendℤ m) := by
  unfold codimForm
  refine Finset.sum_nonneg fun i _ ↦ Finset.sum_nonneg fun u _ ↦
    Finset.sum_nonneg fun j _ ↦ Finset.sum_nonneg fun v _ ↦ ?_
  exact mul_nonneg (extendℤ_nonneg m _ _) (extendℤ_nonneg m _ _)

/-- `0 ≤ cCodim d r h` (the minimum of non-negative `codimForm` values). -/
theorem cCodim_nonneg {d : Fin (N + 1) → ℕ} {r : ℕ} (h : (kostantPartitions d r).Nonempty) :
    0 ≤ cCodim d r h := by
  rw [cCodim]
  exact Finset.le_inf' h (fun m ↦ codimForm N (extendℤ m)) (fun m _ ↦ codimForm_extendℤ_nonneg m)

/-- Each Kostant partition's exponent dominates `cCodim` (as `ℕ`, via `toNat`). -/
theorem cCodimToNat_le_expon {d : Fin (N + 1) → ℕ} {r : ℕ} (h : (kostantPartitions d r).Nonempty)
    {m : Fin (N + 1) × Fin (N + 1) → ℕ} (hm : m ∈ kostantPartitions d r) :
    (cCodim d r h).toNat ≤ (codimForm N (extendℤ m)).toNat := by
  apply Int.toNat_le_toNat
  rw [cCodim]
  exact Finset.inf'_le _ hm

/-- **Coefficients below `cCodim` vanish.** -/
theorem Qseries_coeff_lt {d : Fin (N + 1) → ℕ} {r : ℕ} (h : (kostantPartitions d r).Nonempty)
    {n : ℕ} (hn : n < (cCodim d r h).toNat) : coeff (R := ℤ) n (Qseries d r) = 0 := by
  rw [Qseries, map_sum]
  refine Finset.sum_eq_zero fun m hm ↦ ?_
  rw [coeff_X_pow_mul', if_neg]
  have := cCodimToNat_le_expon h hm
  omega

/-- **The coefficient at `cCodim` is `numTop`** (no cancellation: each minimiser contributes its
`Pm`'s constant term `1`). -/
theorem Qseries_coeff_cCodim {d : Fin (N + 1) → ℕ} {r : ℕ} (h : (kostantPartitions d r).Nonempty) :
    coeff (R := ℤ) (cCodim d r h).toNat (Qseries d r) = (numTop d r h : ℤ) := by
  rw [Qseries, map_sum, numTop, Finset.card_filter, Nat.cast_sum]
  refine Finset.sum_congr rfl fun m hm ↦ ?_
  rw [coeff_X_pow_mul']
  have hle := cCodimToNat_le_expon h hm
  have hnn := codimForm_extendℤ_nonneg (N := N) m
  have hcc := cCodim_nonneg h
  by_cases hc : codimForm N (extendℤ m) = cCodim d r h
  · rw [if_pos (by omega), if_pos hc, Nat.cast_one]
    have hsub : (cCodim d r h).toNat - (codimForm N (extendℤ m)).toNat = 0 := by omega
    rw [hsub, coeff_zero_eq_constantCoeff_apply, constantCoeff_Pm]
  · rw [if_neg (by omega), if_neg hc, Nat.cast_zero]

/-- `numTop > 0`: the minimum `cCodim` is attained by at least one Kostant partition. -/
theorem numTop_pos {d : Fin (N + 1) → ℕ} {r : ℕ} (h : (kostantPartitions d r).Nonempty) :
    0 < numTop d r h := by
  rw [numTop, Finset.card_pos]
  obtain ⟨m, hm, hmin⟩ := Finset.exists_mem_eq_inf' h (fun m ↦ codimForm N (extendℤ m))
  exact ⟨m, Finset.mem_filter.mpr ⟨hm, by rw [cCodim, ← hmin]⟩⟩

/-! ## The `(C, θ)` bridge: `Qseries` determines `cCodim` and `numTop`

`cCodim` is the order of `Qseries` (least degree with a nonzero coefficient — nonzero because the
coefficient there is `numTop > 0`), and `numTop` is that coefficient. Hence equal `Qseries` force
equal `(C, θ)` — the lever that turns Thm 5.5's manifest multiset-symmetry into Cor 5.10. -/

/-- Equal `Qseries` ⟹ equal `cCodim` (as `ℕ` via `toNat`; both are non-negative). -/
theorem cCodim_toNat_eq_of_Qseries_eq {d d' : Fin (N + 1) → ℕ} {r r' : ℕ}
    (h : (kostantPartitions d r).Nonempty) (h' : (kostantPartitions d' r').Nonempty)
    (hQ : Qseries d r = Qseries d' r') :
    (cCodim d r h).toNat = (cCodim d' r' h').toNat := by
  rcases Nat.lt_trichotomy (cCodim d r h).toNat (cCodim d' r' h').toNat with hlt | heq | hgt
  · exfalso
    have h0 := Qseries_coeff_lt h' (d := d') (r := r') (n := (cCodim d r h).toNat) hlt
    rw [← hQ, Qseries_coeff_cCodim h] at h0
    have := numTop_pos h; omega
  · exact heq
  · exfalso
    have h0 := Qseries_coeff_lt h (d := d) (r := r) (n := (cCodim d' r' h').toNat) hgt
    rw [hQ, Qseries_coeff_cCodim h'] at h0
    have := numTop_pos h'; omega

/-- Equal `Qseries` ⟹ equal `cCodim` (over `ℤ`). -/
theorem cCodim_eq_of_Qseries_eq {d d' : Fin (N + 1) → ℕ} {r r' : ℕ}
    (h : (kostantPartitions d r).Nonempty) (h' : (kostantPartitions d' r').Nonempty)
    (hQ : Qseries d r = Qseries d' r') : cCodim d r h = cCodim d' r' h' := by
  have htn := cCodim_toNat_eq_of_Qseries_eq h h' hQ
  have h1 := cCodim_nonneg h
  have h2 := cCodim_nonneg h'
  omega

/-- Equal `Qseries` ⟹ equal `numTop`. -/
theorem numTop_eq_of_Qseries_eq {d d' : Fin (N + 1) → ℕ} {r r' : ℕ}
    (h : (kostantPartitions d r).Nonempty) (h' : (kostantPartitions d' r').Nonempty)
    (hQ : Qseries d r = Qseries d' r') : numTop d r h = numTop d' r' h' := by
  have hc := cCodim_toNat_eq_of_Qseries_eq h h' hQ
  have : (numTop d r h : ℤ) = (numTop d' r' h' : ℤ) := by
    rw [← Qseries_coeff_cCodim h, ← Qseries_coeff_cCodim h', hc, hQ]
  exact_mod_cast this

end DLNFibre.Core
