import DLNFibre.Core.QSeriesShift
import DLNFibre.Core.QSeriesOrth

/-!
# `DLNFibre.Core.QSeriesThm55` — Theorem 5.5 (M4)

The closed form of the corner-graded generating function:

`thm55 : Qseries d r = P r · ∑_{s=0}^{min d − r} altP s · Pmult (d − r − s)` (for `r ≤ d k` at every
vertex), with the only `d`-dependent factor `Pmult (d − r − s) = ∏ᵢ P (dᵢ − r − s)` **manifestly
multiset-symmetric** — the engine of Cor 5.10 (M6).

Two legs:
* **S3 (`thm55_zero`)** — the `r = 0` case `Qseries d 0 = ∑_{s=0}^{min d} altP s · Pmult (d − s)`. The
  4-line substitution chain of the cert: substitute S2 (`Pmult_eq_sum_corner`) into the RHS, recognise
  the triangle double-sum, reindex `(s,t) ↦ (s+t, s)` (`sum_triangle_reindex`), factor the
  `k`-independent `Qseries (d−u) 0` out, and collapse by `orth` (`∑_k altP k · P (u−k) = [u=0]`).
* **S4 (`thm55`)** — general `r`: apply S1' (`Qseries_corner_shift`) to reduce `Qseries d r` to
  `P r · Qseries (d − r) 0`, then S3 at `d − r` and `(d−r)−s = d−(r+s)` (`dminus_dminus`).
-/

namespace DLNFibre.Core

open PowerSeries Finset

variable {N : ℕ}

/-- `dminus (dminus d s) t = dminus d (s + t)` (iterated truncated shift, `Nat.sub_sub`). -/
theorem dminus_dminus (d : Fin (N + 1) → ℕ) (s t : ℕ) :
    dminus (dminus d s) t = dminus d (s + t) := by
  funext k; simp only [dminus, Nat.sub_sub]

/-- **The triangle reindex** (the S3 convolution): summing a kernel over the lower triangle
`{(s,t) : s + t ≤ n}` as `∑_{s≤n} ∑_{t≤n−s}` equals the antidiagonal form `∑_{u≤n} ∑_{k≤u}` with
`u = s+t`, `k = s` (so `s = k`, `t = u−k`). A `Finset.sum_bij'` between the two sigma index sets. -/
theorem sum_triangle_reindex {M : Type*} [AddCommMonoid M] (n : ℕ) (f : ℕ → ℕ → M) :
    (∑ s ∈ Finset.range (n + 1), ∑ t ∈ Finset.range (n + 1 - s), f s t)
      = ∑ u ∈ Finset.range (n + 1), ∑ k ∈ Finset.range (u + 1), f k (u - k) := by
  rw [Finset.sum_sigma', Finset.sum_sigma']
  refine Finset.sum_bij'
    (fun p _ ↦ (⟨p.1 + p.2, p.1⟩ : Σ _ : ℕ, ℕ))
    (fun q _ ↦ (⟨q.2, q.1 - q.2⟩ : Σ _ : ℕ, ℕ)) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨s, t⟩ hp
    simp only [Finset.mem_sigma, Finset.mem_range] at hp ⊢
    obtain ⟨hs, ht⟩ := hp
    exact ⟨by omega, by omega⟩
  · rintro ⟨u, k⟩ hq
    simp only [Finset.mem_sigma, Finset.mem_range] at hq ⊢
    obtain ⟨hu, hk⟩ := hq
    exact ⟨by omega, by omega⟩
  · rintro ⟨s, t⟩ hp
    simp only [Finset.mem_sigma, Finset.mem_range] at hp
    obtain ⟨hs, ht⟩ := hp
    simp only [Sigma.mk.injEq, Nat.add_sub_cancel_left, heq_eq_eq, and_true, true_and]
  · rintro ⟨u, k⟩ hq
    simp only [Finset.mem_sigma, Finset.mem_range] at hq
    obtain ⟨hu, hk⟩ := hq
    have : k + (u - k) = u := Nat.add_sub_cancel' (by omega : k ≤ u)
    simp only [this]
  · rintro ⟨s, t⟩ _; simp

/-- `dminus d 0 = d` (the empty shift). -/
@[simp] theorem dminus_zero (d : Fin (N + 1) → ℕ) : dminus d 0 = d := by
  funext k; simp [dminus]

/-- **S3 — Theorem 5.5 at `r = 0`:** `Qseries d 0 = ∑_{s=0}^{min d} altP s · Pmult (d − s)`. Substitute
S2 (`Pmult_eq_sum_corner`) into the RHS, recognise the triangle double-sum, reindex `(s,t) ↦ (s+t, s)`
(`sum_triangle_reindex`), factor the `k`-independent `Qseries (d−u) 0`, and collapse by `orth`. -/
theorem thm55_zero (d : Fin (N + 1) → ℕ) :
    Qseries d 0 = ∑ s ∈ Finset.range (minDim d + 1), altP s * Pmult (dminus d s) := by
  set n := minDim d with hn
  -- Step 1: substitute S2 into each `Pmult (d − s)`, normalise inner range and the iterated shift
  have hstep1 : (∑ s ∈ Finset.range (n + 1), altP s * Pmult (dminus d s))
      = ∑ s ∈ Finset.range (n + 1), ∑ t ∈ Finset.range (n + 1 - s),
          altP s * P t * Qseries (dminus d (s + t)) 0 := by
    refine Finset.sum_congr rfl fun s hs ↦ ?_
    rw [Finset.mem_range, Nat.lt_succ_iff] at hs
    rw [Pmult_eq_sum_corner, minDim_dminus, hn, Finset.mul_sum,
      show n - s + 1 = n + 1 - s from by omega]
    refine Finset.sum_congr rfl fun t _ ↦ ?_
    rw [dminus_dminus]; ring
  -- Step 2: triangle reindex `(s,t) ↦ (u = s+t, k = s)`, then `k + (u−k) = u`
  rw [hstep1, sum_triangle_reindex n (fun s t ↦ altP s * P t * Qseries (dminus d (s + t)) 0)]
  have hstep2 : (∑ u ∈ Finset.range (n + 1), ∑ k ∈ Finset.range (u + 1),
        altP k * P (u - k) * Qseries (dminus d (k + (u - k))) 0)
      = ∑ u ∈ Finset.range (n + 1), orthSum u * Qseries (dminus d u) 0 := by
    refine Finset.sum_congr rfl fun u _ ↦ ?_
    rw [orthSum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k hk ↦ ?_
    rw [Finset.mem_range, Nat.lt_succ_iff] at hk
    rw [Nat.add_sub_cancel' hk]
  rw [hstep2]
  -- Step 3: `orthSum u = [u = 0]`, so only `u = 0` survives → `Qseries d 0`
  rw [Finset.sum_congr rfl (fun u _ ↦ by rw [orth])]
  rw [Finset.sum_eq_single 0]
  · simp
  · intro u _ hu; rw [if_neg hu, zero_mul]
  · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h

/-- **S4 — Theorem 5.5 (general `r`):** `Qseries d r = P r · ∑_{s=0}^{min d − r} altP s · Pmult (d − r − s)`
(for `r ≤ d k` at every vertex). Apply S1' (`Qseries_corner_shift`) to peel `P r`, then S3 at `d − r`
with `(d − r) − s = d − (r + s)` (`dminus_dminus`). The only `d`-dependent factor `Pmult (d − r − s)` is
manifestly multiset-symmetric — the engine of Cor 5.10. -/
theorem thm55 (d : Fin (N + 1) → ℕ) (r : ℕ) (hr : ∀ k, r ≤ d k) :
    Qseries d r
      = P r * ∑ s ∈ Finset.range (minDim d - r + 1), altP s * Pmult (dminus d (r + s)) := by
  rw [Qseries_corner_shift d r hr, thm55_zero (dminus d r), minDim_dminus]
  congr 1
  refine Finset.sum_congr rfl fun s _ ↦ ?_
  rw [dminus_dminus]

end DLNFibre.Core
