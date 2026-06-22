import DLNFibre.Core.QSeriesExtraction
import DLNFibre.Core.QSeriesThm55

/-!
# `DLNFibre.Core.CThetaPermInvariance` — permutation invariance of `(C, θ)` (M6, Cor 5.10)

The capstone. Once Thm 5.5 (M4) writes `Qseries d r` as `P r · ∑_s (−1)^s q^{C(s,2)} P s · Pmult(d−r−s)`
with `Pmult(d−r−s) = ∏ᵢ P(dᵢ−r−s)` **manifestly symmetric in the multiset of `d`**, the M5 bridge
(`cCodim_eq_of_Qseries_eq` / `numTop_eq_of_Qseries_eq`) turns that symmetry into
`cCodim (d∘σ) r = cCodim d r` and `numTop (d∘σ) r = numTop d r` for every permutation `σ` — Cor 5.10.

This file collects the symmetry ingredients that do not depend on Thm 5.5. The headline `cCodim`/`numTop`
invariance is assembled here once M4 lands.
-/

namespace DLNFibre.Core

open PowerSeries Finset

variable {N : ℕ}

/-- **`Pmult` is symmetric under permutation of the dimension vector.** `Pmult (h ∘ σ) = Pmult h` —
a product over `Fin (N+1)` reindexed by the permutation `σ`. This is the manifest symmetry that, via
Thm 5.5's product form, yields permutation invariance of `(C, θ)`. -/
theorem Pmult_comp_perm (σ : Equiv.Perm (Fin (N + 1))) (h : Fin (N + 1) → ℕ) :
    Pmult (h ∘ σ) = Pmult h := by
  unfold Pmult
  exact Equiv.prod_comp σ (fun i ↦ P (h i))

/-- The pointwise shift commutes with permutation: `(d ∘ σ) i − c = ((fun k ↦ d k − c) ∘ σ) i`. -/
theorem comp_perm_sub (σ : Equiv.Perm (Fin (N + 1))) (d : Fin (N + 1) → ℕ) (c : ℕ) :
    (fun i ↦ (d ∘ σ) i - c) = (fun k ↦ d k - c) ∘ σ := rfl

/-- Hence the shifted product factor is permutation-invariant: `Pmult (fun i ↦ (d∘σ) i − c) =
Pmult (fun k ↦ d k − c)`. This is the exact term appearing in Thm 5.5's product form. -/
theorem Pmult_sub_comp_perm (σ : Equiv.Perm (Fin (N + 1))) (d : Fin (N + 1) → ℕ) (c : ℕ) :
    Pmult (fun i ↦ (d ∘ σ) i - c) = Pmult (fun k ↦ d k - c) := by
  rw [comp_perm_sub]; exact Pmult_comp_perm σ (fun k ↦ d k - c)

/-! ## The capstone — Cor 5.10 (permutation invariance of `(C, θ)`)

Thm 5.5 (`thm55`) writes `Qseries d r = P r · ∑_s altP s · Pmult (d − r − s)`; the only `d`-dependent
factor is the manifestly multiset-symmetric `Pmult (d − r − s)`, and the corner range `min d − r` is a
multiset invariant. Hence `Qseries (d ∘ σ) r = Qseries d r`, and the M5 bridge
(`cCodim_eq_of_Qseries_eq` / `numTop_eq_of_Qseries_eq`) turns that into invariance of `(C, θ)`. -/

/-- `minDim` is permutation-invariant: `minDim (d ∘ σ) = minDim d` (a min over a reindexed `univ`). -/
theorem minDim_comp_perm (σ : Equiv.Perm (Fin (N + 1))) (d : Fin (N + 1) → ℕ) :
    minDim (d ∘ σ) = minDim d := by
  refine le_antisymm ?_ ?_
  · obtain ⟨k, hk⟩ := exists_minDim_eq d
    calc minDim (d ∘ σ) ≤ (d ∘ σ) (σ.symm k) := minDim_le _ _
      _ = d k := by simp
      _ = minDim d := hk.symm
  · obtain ⟨k, hk⟩ := exists_minDim_eq (d ∘ σ)
    calc minDim d ≤ d (σ k) := minDim_le _ _
      _ = (d ∘ σ) k := rfl
      _ = minDim (d ∘ σ) := hk.symm

/-- **`Qseries` is permutation-invariant** (the Thm 5.5 corollary): `Qseries (d ∘ σ) r = Qseries d r`.
Both sides equal Thm 5.5's `P r · ∑_s altP s · Pmult (· − r − s)`; the corner range `min d − r` is a
multiset invariant (`minDim_comp_perm`) and the `d`-dependent factor is symmetric (`Pmult_sub_comp_perm`,
with `Nat.sub_sub : d i − r − s = d i − (r + s)`). -/
theorem Qseries_comp_perm (σ : Equiv.Perm (Fin (N + 1))) (d : Fin (N + 1) → ℕ) (r : ℕ)
    (hr : ∀ k, r ≤ d k) : Qseries (d ∘ σ) r = Qseries d r := by
  have hr' : ∀ k, r ≤ (d ∘ σ) k := fun k ↦ hr (σ k)
  rw [thm55 (d ∘ σ) r hr', thm55 d r hr, minDim_comp_perm]
  congr 1
  refine Finset.sum_congr rfl fun s _ ↦ ?_
  -- the `Pmult` factor is the perm-invariant `Pmult_sub_comp_perm` with `c = r + s`
  congr 1
  have h1 : dminus (d ∘ σ) (r + s) = fun i ↦ (d ∘ σ) i - (r + s) := rfl
  have h2 : dminus d (r + s) = fun k ↦ d k - (r + s) := rfl
  rw [h1, h2, Pmult_sub_comp_perm σ d (r + s)]

/-- **Cor 5.10 (combinatorial codimension is permutation-invariant):** `cCodim (d ∘ σ) r = cCodim d r`.
The `Qseries` invariance (`Qseries_comp_perm`) feeds the M5 bridge `cCodim_eq_of_Qseries_eq`. The
nonemptiness hypotheses are supplied on both sides where `(C, θ)` is defined. (This is a *combinatorial*
codimension; the `rlct = ½·codim` reading stays Cited — Aoyagi/Watanabe.) -/
theorem cCodim_comp_perm (σ : Equiv.Perm (Fin (N + 1))) (d : Fin (N + 1) → ℕ) (r : ℕ)
    (hr : ∀ k, r ≤ d k) (h : (kostantPartitions (d ∘ σ) r).Nonempty)
    (h' : (kostantPartitions d r).Nonempty) :
    cCodim (d ∘ σ) r h = cCodim d r h' :=
  cCodim_eq_of_Qseries_eq h h' (Qseries_comp_perm σ d r hr)

/-- **Cor 5.10 (combinatorial component count is permutation-invariant):** `numTop (d ∘ σ) r =
numTop d r`. Same lever: `Qseries_comp_perm` + the M5 bridge `numTop_eq_of_Qseries_eq`. -/
theorem numTop_comp_perm (σ : Equiv.Perm (Fin (N + 1))) (d : Fin (N + 1) → ℕ) (r : ℕ)
    (hr : ∀ k, r ≤ d k) (h : (kostantPartitions (d ∘ σ) r).Nonempty)
    (h' : (kostantPartitions d r).Nonempty) :
    numTop (d ∘ σ) r h = numTop d r h' :=
  numTop_eq_of_Qseries_eq h h' (Qseries_comp_perm σ d r hr)

end DLNFibre.Core
