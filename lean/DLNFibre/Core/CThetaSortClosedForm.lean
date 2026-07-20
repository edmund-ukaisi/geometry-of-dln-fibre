/-
Copyright (c) 2026. Released under Apache 2.0; see LICENSE.
-/
import DLNFibre.Core.CThetaShiftCount
import DLNFibre.Core.CThetaPermInvariance

/-!
# `DLNFibre.Core.CThetaSortClosedForm` — closed form `cTheta` for ARBITRARY (non-monotone) `d`

`Core.CThetaShiftCount.numTop_eq_cTheta_dminus` evaluates the minimiser count `numTop d r` to the
closed form `cTheta (d − r) = C(m, |δ|)` **only for `Monotone d`** (`cTheta` reads the
order-sensitive prefix data). This module removes the monotonicity restriction by routing through
the LANDED permutation invariance of `(C, θ)`:

> `numTop d r = numTop (d ∘ Tuple.sort d) r`  (`CThetaPermInvariance.numTop_comp_sort`, Cor 5.10)

and `d ∘ Tuple.sort d` is the **monotone rearrangement** of `d` (`Tuple.monotone_sort`), on which
the closed form applies. So for any `d`:

> `numTop d r = cTheta ((d ∘ Tuple.sort d) − r)`.

This is the *computable* closed form for non-monotone `d`: evaluate `cTheta` on the sorted vector.
It carries `hr : ∀ k, r ≤ d k` and `1 ≤ N` — the hypotheses permutation invariance itself needs (Cor
5.10's `Qseries` symmetry lever, and `kostantPartitions_nonempty_of_le` for the sorted-side
nonemptiness) — but NOT `Monotone d`.

**Dependency rule:** `Core` only — never import `DLNFibre.DLN`.
-/

namespace DLNFibre.Core

variable {N : ℕ}

/-- **The closed form `cTheta` on the sorted vector, for an ARBITRARY `d`.** The minimiser count
`numTop d r` of any dimension vector equals `cTheta` of its monotone rearrangement's shift:
`numTop d r = cTheta ((d ∘ Tuple.sort d) − r)`. Routes `numTop d r` to the sorted representative by
permutation invariance (`numTop_comp_sort`, Cor 5.10), then applies the `Monotone` closed form
`numTop_eq_cTheta_dminus` — valid because `d ∘ Tuple.sort d` is monotone (`Tuple.monotone_sort`). No
monotonicity on `d`; carries only `1 ≤ N` and `r ≤ d k` (the perm-invariance hypotheses). -/
theorem numTop_eq_cTheta_dminus_sort (d : Fin (N + 1) → ℕ) (r : ℕ) (hN : 1 ≤ N)
    (hr : ∀ k, r ≤ d k) (h' : (kostantPartitions d r).Nonempty) :
    numTop d r h' = cTheta (dminus (d ∘ _root_.Tuple.sort d) r) := by
  have hr_s : ∀ k, r ≤ (d ∘ _root_.Tuple.sort d) k := fun k ↦ hr (_root_.Tuple.sort d k)
  have h_s : (kostantPartitions (d ∘ _root_.Tuple.sort d) r).Nonempty :=
    kostantPartitions_nonempty_of_le hN hr_s
  have h0_s : (kostantPartitions (dminus (d ∘ _root_.Tuple.sort d) r) 0).Nonempty :=
    kostantPartitions_nonempty_of_le hN (fun _ ↦ Nat.zero_le _)
  rw [← numTop_comp_sort d r hr h_s h',
    numTop_eq_cTheta_dminus (Tuple.monotone_sort d) hr_s h0_s h_s]

end DLNFibre.Core
