import DLNFibre.Core.Analysis.RLCT.Local
import DLNFibre.Core.Analysis.RLCT.Basic
import Mathlib.Data.Real.Pointwise

/-!
# `RLCT.PowerRule` — B4: the power rule `rlctAt (K^n) x₀ = rlctAt K x₀ / n`

**Raising the germ to a natural power `n ≥ 1` scales the local RLCT by `1/n`.** For a nonnegative
germ `K` (`0 ≤ K` pointwise) and `n ≥ 1`,

`rlctAt (fun x ↦ (K x)^n) x₀ = rlctAt K x₀ / n`.

The DLN-relevant instance is `n = 2` (`rlctAt (K^2) x₀ = rlctAt K x₀ / 2`) — the square that turns a
germ into the square-loss.

## Route (unconditional in the pole/junk regime — `sSup` scaling)

The key germ identity: for `0 ≤ K x`,
`negPow (K^n) c x = ((K x)^n)^(-c) = (K x)^(-(n·c)) = negPow K (n·c) x` (`Real.rpow_natCast` +
`Real.rpow_mul`). So local admissibility transfers:
`c ∈ localAdmissibleExponents (K^n) x₀ ↔ (n·c) ∈ localAdmissibleExponents K x₀` (using `n > 0` for
the sign `0 ≤ c ↔ 0 ≤ n·c`). Hence the admissible set of `K^n` is `(1/n) • (that of K)`, and
`Real.sSup_smul_of_nonneg` (`0 ≤ 1/n`) scales the `sSup`:
`rlctAt (K^n) x₀ = sSup ((1/n) • S) = (1/n) • sSup S = rlctAt K x₀ / n`.

No `BddAbove` hypothesis is needed: `Real.sSup_smul_of_nonneg` holds for any set (the junk-`0` at
an unbounded set scales coherently, `(1/n)·0 = 0`), so the identity is valid in both the pole
regime and the regular/junk regime — the scaling is exact wherever `rlctAt` is defined.

Bare Mathlib-mirror namespace `RLCT` (network-free).
-/

open MeasureTheory Set Filter Topology Pointwise

namespace RLCT

variable {n : ℕ}

/-- The `n`-th power germ `x ↦ (K x)^n` (natural-number power of the base). -/
noncomputable def powGerm (K : (Fin n → ℝ) → ℝ) (k : ℕ) : (Fin n → ℝ) → ℝ :=
  fun x ↦ (K x) ^ k

@[simp] lemma powGerm_apply (K : (Fin n → ℝ) → ℝ) (k : ℕ) (x : Fin n → ℝ) :
    powGerm K k x = (K x) ^ k := rfl

/-- **The germ identity: `negPow (K^k) c = negPow K (k·c)`** on the nonnegative locus. For
`0 ≤ K x`, `((K x)^k)^(-c) = (K x)^(-(k·c))` (`Real.rpow_natCast` recasts the `npow` to `rpow`, then
`Real.rpow_mul` collapses the double power). -/
lemma negPow_powGerm {K : (Fin n → ℝ) → ℝ} (hK : ∀ x, 0 ≤ K x) (k : ℕ) (c : ℝ) :
    negPow (powGerm K k) c = negPow K ((k : ℝ) * c) := by
  funext x
  simp only [negPow_apply, powGerm_apply]
  rw [← Real.rpow_natCast (K x) k, ← Real.rpow_mul (hK x)]
  ring_nf

/-- **Local-admissibility transfer under the power germ.** For `0 ≤ K` and `k ≥ 1`,
`c ∈ localAdmissibleExponents (K^k) x₀ ↔ (k·c) ∈ localAdmissibleExponents K x₀`. The integrability
components agree (`negPow_powGerm`); the signs `0 ≤ c` and `0 ≤ k·c` agree since `k > 0`. -/
lemma mem_localAdmissibleExponents_powGerm {K : (Fin n → ℝ) → ℝ} {x₀ : Fin n → ℝ}
    (hK : ∀ x, 0 ≤ K x) {k : ℕ} (hk : 1 ≤ k) {c : ℝ} :
    c ∈ localAdmissibleExponents (powGerm K k) x₀ ↔
      ((k : ℝ) * c) ∈ localAdmissibleExponents K x₀ := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  rw [mem_localAdmissibleExponents, mem_localAdmissibleExponents, negPow_powGerm hK]
  constructor
  · rintro ⟨hc0, hint⟩
    exact ⟨by positivity, hint⟩
  · rintro ⟨hc0, hint⟩
    refine ⟨?_, hint⟩
    -- `0 ≤ k·c` and `k > 0` ⟹ `0 ≤ c`.
    exact (mul_nonneg_iff_of_pos_left hkpos).1 hc0

/-- **The power-germ admissible set is `(1/k)` times the base admissible set.** For `0 ≤ K`,
`k ≥ 1`, `localAdmissibleExponents (K^k) x₀ = (1/k : ℝ) • localAdmissibleExponents K x₀`. From the
transfer `c ∈ LHS ↔ k·c ∈ base set`, rescaled by the bijection `c ↦ k·c`. -/
lemma localAdmissibleExponents_powGerm {K : (Fin n → ℝ) → ℝ} {x₀ : Fin n → ℝ}
    (hK : ∀ x, 0 ≤ K x) {k : ℕ} (hk : 1 ≤ k) :
    localAdmissibleExponents (powGerm K k) x₀
      = ((k : ℝ)⁻¹) • localAdmissibleExponents K x₀ := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  have hkne : (k : ℝ) ≠ 0 := ne_of_gt hkpos
  ext c
  rw [mem_localAdmissibleExponents_powGerm hK hk, Set.mem_smul_set]
  constructor
  · intro hmem
    refine ⟨(k : ℝ) * c, hmem, ?_⟩
    rw [smul_eq_mul]; field_simp
  · rintro ⟨d, hd, rfl⟩
    rw [smul_eq_mul]
    rwa [show (k : ℝ) * ((k : ℝ)⁻¹ * d) = d by field_simp]

/-- **B4 — the power rule: `rlctAt (K^n) x₀ = rlctAt K x₀ / n`.** For a nonnegative germ `K`
(`0 ≤ K`) and a natural power `k ≥ 1`, raising the germ to the `k`-th power scales the local RLCT by
`1/k`. Unconditional in the germ (holds in both the pole regime and the regular/junk regime — the
`sSup` scaling `Real.sSup_smul_of_nonneg` needs no boundedness). The DLN case is `k = 2`. -/
theorem rlctAt_powGerm {K : (Fin n → ℝ) → ℝ} {x₀ : Fin n → ℝ}
    (hK : ∀ x, 0 ≤ K x) {k : ℕ} (hk : 1 ≤ k) :
    rlctAt (powGerm K k) x₀ = rlctAt K x₀ / k := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  have hnn : (0 : ℝ) ≤ (k : ℝ)⁻¹ := by positivity
  rw [rlctAt_def, rlctAt_def, localAdmissibleExponents_powGerm hK hk,
    Real.sSup_smul_of_nonneg hnn, smul_eq_mul, div_eq_inv_mul]

end RLCT
