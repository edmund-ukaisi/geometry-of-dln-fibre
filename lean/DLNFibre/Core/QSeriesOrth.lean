import DLNFibre.Core.QSeriesDurfee

/-!
# `DLNFibre.Core.QSeriesOrth` — the inverse-Pochhammer orthogonality (M4's one classical q-input)

`altP k := (−1)^k · X^{k(k−1)/2} · P k` (the "alternating" companion of `P`). The single classical
`q`-fact Thm 5.5 (S3) rests on is the orthogonality

`orth : ∑_{k=0}^{u} altP k · P (u − k) = (if u = 0 then 1 else 0)` over `ℤ⟦X⟧`.

This is the coefficient form of `(x;q)_∞ · (x;q)_∞^{-1} = 1`. Mathlib v4.29 has no `q`-binomial /
`q`-Vandermonde library — and this proof needs none: a self-contained single-variable induction on `u`,
driven entirely by the LANDED `P_mul_one_sub_succ` (`P (s+1)·(1−X^{s+1}) = P s`). The mechanism:

* `(AA)` `altP_mul_one_sub : altP (k+1)·(1−X^{k+1}) = −X^k · altP k` — pure `ring` off `(PA)` and the
  exponent identity `C(k+1,2) = k + C(k,2)`.
* `orth_recurrence` : `O u · (1−X^u) = (1−X^{u−1}) · O (u−1)` for `u ≥ 1`, where `O u` is the orth sum.
  Distribute the pure split `1−X^u = (1−X^{u−k}) + X^{u−k}·(1−X^k)`: the first part telescopes to
  `O (u−1)` (the `k=u` term dies, `1−X^0=0`); the second, after the `k=0` peel and the `j=k−1` reindex
  (`Finset.sum_range_succ'`, the M2 `B_sum_desc` precedent), gives `−X^{u−1}·O (u−1)`.
* `orth` : induct — `O 0 = 1`; `u ≥ 1` ⟹ `O u·(1−X^u) = 0` (IH `O (u−1) = 0` for `u ≥ 2`; the `1−X^u`
  factor is a non-zero-divisor, `one_sub_X_pow_ne_zero`), so `O u = 0`.
-/

namespace DLNFibre.Core

open PowerSeries Finset

/-- The alternating inverse-Pochhammer companion `altP k = (−1)^k · X^{k(k−1)/2} · P k`. -/
noncomputable def altP (k : ℕ) : ℤ⟦X⟧ := (-1) ^ k * X ^ (k * (k - 1) / 2) * P k

/-- `altP 0 = 1`. -/
@[simp] theorem altP_zero : altP 0 = 1 := by simp [altP]

/-- The exponent identity `(k+1)·k/2 = k + k·(k−1)/2` (triangular numbers), via the Pascal recurrence
`(k+1).choose 2 = k.choose 1 + k.choose 2` and `Nat.choose_two_right`. -/
theorem choose2_succ (k : ℕ) : (k + 1) * ((k + 1) - 1) / 2 = k + k * (k - 1) / 2 := by
  have h1 : (k + 1).choose 2 = k * (k - 1) / 2 + k := by
    rw [Nat.choose_succ_succ k 1, Nat.choose_one_right, Nat.choose_two_right, Nat.add_comm]
  have h2 : (k + 1).choose 2 = (k + 1) * ((k + 1) - 1) / 2 := Nat.choose_two_right (k + 1)
  omega

/-- **(AA)** — `altP (k+1)·(1−X^{k+1}) = −X^k · altP k`. Pure `ring` off the LANDED `(PA)`
`P (k+1)·(1−X^{k+1}) = P k` and the exponent identity `choose2_succ`. -/
theorem altP_mul_one_sub (k : ℕ) :
    altP (k + 1) * (1 - X ^ (k + 1)) = -X ^ k * altP k := by
  rw [altP, altP, choose2_succ]
  rw [show ((-1 : ℤ⟦X⟧)) ^ (k + 1) = -((-1) ^ k) from by rw [pow_succ]; ring,
    pow_add]
  -- group the P-factor against (1 − X^{k+1}) and apply (PA)
  rw [show (-((-1 : ℤ⟦X⟧) ^ k) * (X ^ k * X ^ (k * (k - 1) / 2)) * P (k + 1)) * (1 - X ^ (k + 1))
        = -X ^ k * ((-1) ^ k * X ^ (k * (k - 1) / 2) * (P (k + 1) * (1 - X ^ (k + 1))))
        from by ring,
    P_mul_one_sub_succ]

/-- The orthogonality sum `O u = ∑_{k=0}^{u} altP k · P (u − k)`. -/
noncomputable def orthSum (u : ℕ) : ℤ⟦X⟧ := ∑ k ∈ Finset.range (u + 1), altP k * P (u - k)

/-- `orthSum 0 = altP 0 · P 0 = 1`. -/
@[simp] theorem orthSum_zero : orthSum 0 = 1 := by simp [orthSum]

/-- The pure split `1 − X^u = (1 − X^{u−k}) + X^{u−k}·(1 − X^k)` over `ℤ⟦X⟧`, for `k ≤ u`. -/
theorem one_sub_pow_split_le {u k : ℕ} (h : k ≤ u) :
    (1 : ℤ⟦X⟧) - X ^ u = (1 - X ^ (u - k)) + X ^ (u - k) * (1 - X ^ k) := by
  have : (X : ℤ⟦X⟧) ^ (u - k) * X ^ k = X ^ u := by rw [← pow_add, Nat.sub_add_cancel h]
  rw [mul_sub, mul_one, this]; ring

/-- **The orthogonality recurrence**: `orthSum u · (1 − X^u) = (1 − X^{u−1}) · orthSum (u−1)`
for `u = v + 1`. Distribute `1 − X^{v+1}` by `one_sub_pow_split`: the `(1−X^{u−k})` part telescopes
(via `(PA)`, the `k = u` term dying) to `orthSum v`; the `X^{u−k}·(1−X^k)` part, after peeling `k = 0`
and reindexing `j = k−1` (via `(AA)`), gives `−X^v · orthSum v`. -/
theorem orth_recurrence (v : ℕ) :
    orthSum (v + 1) * (1 - X ^ (v + 1)) = (1 - X ^ v) * orthSum v := by
  -- distribute (1 − X^{v+1}) into each summand, split via `one_sub_pow_split`
  rw [orthSum, Finset.sum_mul]
  have hsplit : ∀ k ∈ Finset.range (v + 1 + 1),
      altP k * P (v + 1 - k) * (1 - X ^ (v + 1))
        = altP k * (P (v + 1 - k) * (1 - X ^ (v + 1 - k)))
          + X ^ (v + 1 - k) * (1 - X ^ k) * (altP k * P (v + 1 - k)) := by
    intro k hk
    rw [Finset.mem_range, Nat.lt_succ_iff] at hk
    rw [one_sub_pow_split_le hk]; ring
  rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib]
  -- first sum telescopes to `orthSum v`; second to `−X^v · orthSum v`
  have hA : (∑ k ∈ Finset.range (v + 1 + 1),
        altP k * (P (v + 1 - k) * (1 - X ^ (v + 1 - k)))) = orthSum v := by
    rw [Finset.sum_range_succ]
    -- the `k = v+1` term vanishes: `P 0 · (1 − X^0) = 0`
    rw [show v + 1 - (v + 1) = 0 from by omega, pow_zero, sub_self, mul_zero, mul_zero, add_zero]
    rw [orthSum]
    refine Finset.sum_congr rfl fun k hk ↦ ?_
    rw [Finset.mem_range, Nat.lt_succ_iff] at hk
    rw [show v + 1 - k = (v - k) + 1 from by omega, P_mul_one_sub_succ]
  have hB : (∑ k ∈ Finset.range (v + 1 + 1),
        X ^ (v + 1 - k) * (1 - X ^ k) * (altP k * P (v + 1 - k))) = -X ^ v * orthSum v := by
    rw [Finset.sum_range_succ']
    -- peel `k = 0`: `(1 − X^0) = 0` kills it
    rw [pow_zero, sub_self]
    simp only [mul_zero, zero_mul, add_zero]
    rw [orthSum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j hj ↦ ?_
    rw [Finset.mem_range, Nat.lt_succ_iff] at hj
    -- reindex term: `(AA)` on `altP (j+1)·(1−X^{j+1})` + the `X` exponents combine to `X^v`
    rw [show X ^ (v + 1 - (j + 1)) * (1 - X ^ (j + 1)) * (altP (j + 1) * P (v + 1 - (j + 1)))
          = X ^ (v - j) * (altP (j + 1) * (1 - X ^ (j + 1))) * P (v - j) from by
            rw [show v + 1 - (j + 1) = v - j from by omega]; ring,
      altP_mul_one_sub]
    rw [show X ^ (v - j) * (-X ^ j * altP j) * P (v - j)
          = -(X ^ (v - j) * X ^ j) * (altP j * P (v - j)) from by ring,
      ← pow_add, show (v - j) + j = v from by omega]
  rw [hA, hB]; ring

/-- **Orthogonality** (the one classical `q`-input of Thm 5.5): `∑_{k=0}^{u} altP k · P (u−k) =
[u = 0]`. Induction on `u` via `orth_recurrence`: `O (v+1)·(1−X^{v+1}) = (1−X^v)·O v`, where the RHS is
`0` (base `v=0`: `1−X^0 = 0`; step `v≥1`: IH `O v = 0`), and `1−X^{v+1}` is a non-zero-divisor. -/
theorem orth (u : ℕ) : orthSum u = (if u = 0 then 1 else 0) := by
  induction u with
  | zero => simp
  | succ v ih =>
    -- the RHS of the recurrence is 0
    have hrhs : (1 - X ^ v) * orthSum v = 0 := by
      rcases Nat.eq_zero_or_pos v with hv | hv
      · subst hv; simp
      · rw [ih, if_neg (by omega), mul_zero]
    have hzero : orthSum (v + 1) * (1 - X ^ (v + 1)) = 0 := by rw [orth_recurrence, hrhs]
    rw [if_neg (Nat.succ_ne_zero v)]
    rcases mul_eq_zero.mp hzero with h | h
    · exact h
    · exact absurd h (one_sub_X_pow_ne_zero (by omega))

end DLNFibre.Core
