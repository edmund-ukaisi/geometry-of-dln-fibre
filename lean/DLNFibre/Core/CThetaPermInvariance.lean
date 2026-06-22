import DLNFibre.Core.QSeriesExtraction

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

end DLNFibre.Core
