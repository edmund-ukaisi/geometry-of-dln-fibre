/-
Copyright (c) 2026. Released under Apache 2.0; see LICENSE.
-/
import DLNFibre.Core.CThetaThetaBridge
import DLNFibre.Core.CCodimZeroStrict

/-!
# `DLNFibre.Core.CThetaShiftCount` — the closed form for the rank-`r` component count

Assembles the three LANDED combinatorial bricks into the closed form for the rank-`r`
top-dimensional component count of `Σ̄^r`, in terms of the **shifted** dimension vector `d − r`:

* `CTheta.numTop_rankShift` — `numTop (d − r) 0 = numTop d r` (Lehalleur–Rimányi Lemma 4.5);
* `CThetaThetaBridge.numTop_zero_eq_cTheta` — `numTop e 0 = cTheta e = C(m, |δ|)` (Thm 7.10,
  `r = 0`), for weakly-increasing `e`;
* `CCodimZeroStrict.numTop_eq_ncard_topComponents` — `numTop d r = #{top-dim components of Σ̄^r}`
  (unconditional, over `[IsAlgClosed][CharZero]`).

The combinatorial conclusion `cTheta (d − r) = numTop d r` needs only `Monotone (d − r)` (which
follows from `Monotone d`) and `r ≤ d k` everywhere; it is field-free. Stacking the geometric
headline gives `#{top-dim components of Σ̄^r} = cTheta (d − r) = C(m, |δ|)` over an algebraically
closed field of characteristic `0`. This is the **`Σ̄^r` side** of the expedition's fibre-`θ`
headline (the fibre transport — `Core.ChartLocalizedAlgEquiv` + `IsLocalization.orderIsoOfPrime`,
reducedness removed by `Core.FibreDetUnit` — is the separate Route-A step).

**Scope (name = content).** `cTheta (dminus d r)` is the closed-form component count `C(m, |δ|)`
for the rank-`r` locus; the `Monotone d` hypothesis is genuine (`cTheta` reads the order-sensitive
prefix data, so the closed form is stated on a weakly-increasing vector — permutation invariance is
the separate `Core.CThetaPermInvariance`). The `r = 0` instance recovers `numTop d 0 = cTheta d`.

**Dependency rule:** `Core` only — never import `DLNFibre.DLN`.
-/

namespace DLNFibre.Core

variable {N : ℕ}

/-- **The shift preserves weak monotonicity.** If `d` is weakly increasing then so is `d − r`
(`(d − r) k = d k - r`, and `Nat.sub` is monotone in its first argument). -/
theorem monotone_dminus {d : Fin (N + 1) → ℕ} (hd : Monotone d) (r : ℕ) :
    Monotone (dminus d r) := fun _ _ hij ↦ Nat.sub_le_sub_right (hd hij) r

/-- **The rank-`r` component count is the shifted closed form (combinatorial).** For
weakly-increasing `d` with `r ≤ d k` everywhere, the minimiser count `numTop d r` equals
`cTheta (d − r) = C(m, |δ|)`
of the shifted vector. Field-free: `numTop_rankShift` (Lemma 4.5) carries `numTop d r` to
`numTop (d − r) 0`, then `numTop_zero_eq_cTheta` (Thm 7.10) gives the closed form. -/
theorem numTop_eq_cTheta_dminus {d : Fin (N + 1) → ℕ} {r : ℕ} (hd : Monotone d)
    (hr : ∀ k, r ≤ d k)
    (h₀ : (kostantPartitions (dminus d r) 0).Nonempty)
    (hr' : (kostantPartitions d r).Nonempty) :
    numTop d r hr' = cTheta (dminus d r) := by
  rw [← numTop_rankShift hr h₀ hr', numTop_zero_eq_cTheta (dminus d r) (monotone_dminus hd r) h₀]

/-- **The `Σ̄^r` top-component count is the shifted closed form (geometric).** Over an algebraically
closed field of characteristic `0`, for weakly-increasing `d` with `r ≤ d k` everywhere, the number
of top-dimensional irreducible components of the closed rank-`≤ r` product locus `Σ̄^r` equals
`cTheta (d − r) = C(m, |δ|)`. Stacks the unconditional geometric headline
`numTop_eq_ncard_topComponents` onto the combinatorial closed form `numTop_eq_cTheta_dminus`. -/
theorem ncard_topComponents_sigma_eq_cTheta_dminus {k : Type*} [Field k] [CharZero k] [Infinite k]
    {d : Fin (N + 1) → ℕ} {r : ℕ} (hd : Monotone d) (hr : ∀ k, r ≤ d k)
    (h₀ : (kostantPartitions (dminus d r) 0).Nonempty)
    (hr' : (kostantPartitions d r).Nonempty) :
    (topComponents (k := k) d r hr').ncard = cTheta (dminus d r) := by
  rw [← numTop_eq_ncard_topComponents d r hr', numTop_eq_cTheta_dminus hd hr h₀ hr']

end DLNFibre.Core
