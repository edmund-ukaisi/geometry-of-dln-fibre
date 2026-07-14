import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Data.Real.StarOrdered
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

/-!
# `RouteMSJShellCover` — the single-`ε` count-shell cover of the off-sector `Z`-stratification

**Thread `genm-sj5-domination`, T-Obl3b mountain, build tile #2.** The re-formulation cert
(`tobl3b-reformulation-cert.md` §4) + pin cert (`tobl3b-pin-cert.md` §5, §7 OWED #2) fix the
stratification of the deep product `Z` for the off-sector integrand: a **single threshold `ε`**
count-shell cover (NOT distinct decreasing `εⱼ`, which leaves a proven intermediate-band gap). Shell
`j` = "exactly `j` singular values of `Z` are `< ε`", lumped at the top into `Sᵣ` = "`≥ r` small".

## The measurability question is a non-issue for the assembly

The cover-subadditivity `∫ over box ≤ ∑ⱼ ∫ over Sⱼ` needs only **exhaustiveness** (`box ⊆ ⋃ⱼ Sⱼ`, a
set fact) — NOT that each `Sⱼ` is a measurable set. `MeasureTheory.lintegral_mono_set` (monotone in
the set, `s ⊆ t`) and `lintegral_union_le` (binary subadditivity) are both measurability-free, so
the finite cover bound goes through for arbitrary shell sets. (Individual `Sⱼ`-measurability would
reduce to measurability of the ordered eigenvalues of `ZZᵀ` in `Z`, which Mathlib lacks — but the
assembly does not need it.)

## What lands here (sorry-free)

* **`lintegral_biUnion_finset_le`** — generic finite-`biUnion` subadditivity of `∫⁻`,
  measurability-free.
* **`lintegral_le_sum_finCover`** — the assembly: `box ⊆ ⋃ⱼ Sⱼ` (`j : Fin (r+1)`) gives
  `∫⁻ over box, f ≤ ∑ⱼ ∫⁻ over Sⱼ, f`. Reusable; consumed by the mountain `deeperFlag_shell_le`.
* **`iUnion_clampedShell`** — the clamped-count cover `⋃ⱼ {x | min (c x) r = j} = univ` is
  exhaustive, for any `ℕ`-valued `c` (the lumping at `r` is `min (c x) r`).
* **`weakEigCount`** — the count `#{i : eigenvalue i of ZZᵀ < ε²}` = number of singular values of
  `Z` below `ε` (via `IsHermitian.eigenvalues₀`, the sorted eigenvalue tuple).
* **`singularShell`** + **`singularShell_iUnion`** — the concrete single-`ε` shells `Sⱼ` and their
  exhaustiveness `⋃ⱼ Sⱼ = univ`.
-/

namespace DLNFibre.DLN.RLCT

open Matrix MeasureTheory
open scoped ENNReal BigOperators

/-- **Generic finite-`biUnion` subadditivity of `∫⁻`** (measurability-free). For a finset `s` of
index sets `S i`, the integral over their union is at most the sum of the integrals over pieces. -/
theorem lintegral_biUnion_finset_le {X : Type*} {mX : MeasurableSpace X} {μ : Measure X}
    {ι : Type*} (s : Finset ι) (S : ι → Set X) (f : X → ℝ≥0∞) :
    ∫⁻ x in ⋃ i ∈ s, S i, f x ∂μ ≤ ∑ i ∈ s, ∫⁻ x in S i, f x ∂μ := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.set_biUnion_insert, Finset.sum_insert ha]
      refine le_trans (lintegral_union_le f _ _) ?_
      gcongr

/-- **The finite-cover assembly.** If `box ⊆ ⋃ⱼ Sⱼ` (a `Fin (r+1)`-indexed cover), then
`∫⁻ over box, f ≤ ∑ⱼ ∫⁻ over Sⱼ, f`. Measurability of the shells is NOT required — only
exhaustiveness. This is the assembly the mountain `deeperFlag_shell_le` uses over the single-`ε`
shell cover. -/
theorem lintegral_le_sum_finCover {X : Type*} {mX : MeasurableSpace X} {μ : Measure X}
    {box : Set X} {r : ℕ} (S : Fin (r + 1) → Set X) (f : X → ℝ≥0∞)
    (hcov : box ⊆ ⋃ j, S j) :
    ∫⁻ x in box, f x ∂μ ≤ ∑ j, ∫⁻ x in S j, f x ∂μ := by
  classical
  have hcov' : box ⊆ ⋃ j ∈ (Finset.univ : Finset (Fin (r + 1))), S j := by
    simpa only [Finset.mem_univ, Set.iUnion_true] using hcov
  calc ∫⁻ x in box, f x ∂μ
      ≤ ∫⁻ x in ⋃ j ∈ (Finset.univ : Finset (Fin (r + 1))), S j, f x ∂μ :=
        lintegral_mono_set hcov'
    _ ≤ ∑ j ∈ (Finset.univ : Finset (Fin (r + 1))), ∫⁻ x in S j, f x ∂μ :=
        lintegral_biUnion_finset_le _ S f

/-- **The clamped-count cover is exhaustive.** For any `ℕ`-valued `c`, the shells
`{x | min (c x) r = j}` for `j : Fin (r+1)` cover the whole space (`min (c x) r ∈ {0,…,r}`). -/
theorem iUnion_clampedShell {X : Type*} (c : X → ℕ) (r : ℕ) :
    ⋃ j : Fin (r + 1), {x : X | min (c x) r = (j : ℕ)} = Set.univ := by
  ext x
  simp only [Set.mem_iUnion, Set.mem_setOf_eq, Set.mem_univ, iff_true]
  exact ⟨⟨min (c x) r, Nat.lt_succ_of_le (min_le_right _ _)⟩, rfl⟩

variable {M₂ nn : ℕ}

/-- **The weak-singular-value count** of `Z`: the number of eigenvalues of the Gram matrix `Z Zᴴ`
below `ε²`, i.e. the number of singular values of `Z` below `ε` (for real `Z`, `Zᴴ = Zᵀ`). Uses
`IsHermitian.eigenvalues₀`, the sorted (antitone) eigenvalue tuple of the positive-semidefinite
Gram `Z Zᴴ`. -/
noncomputable def weakEigCount (ε : ℝ) (Z : Matrix (Fin M₂) (Fin nn) ℝ) : ℕ :=
  (Finset.univ.filter
    fun i => (posSemidef_self_mul_conjTranspose Z).isHermitian.eigenvalues₀ i < ε ^ 2).card

/-- **The single-`ε` count-shell `Sⱼ`.** For `j : Fin (r+1)`: exactly `j` singular values of `Z`
are `< ε` when `j < r`; at least `r` are `< ε` when `j = r` (the lumped/saturated shell). Encoded as
`min (weakEigCount ε Z) r = j`. -/
def singularShell (ε : ℝ) (r : ℕ) (j : Fin (r + 1)) :
    Set (Matrix (Fin M₂) (Fin nn) ℝ) :=
  {Z | min (weakEigCount ε Z) r = (j : ℕ)}

/-- **The single-`ε` cover is exhaustive** (`⋃ⱼ Sⱼ = univ`), the single-threshold correction that
avoids the distinct-`εⱼ` intermediate-band gap (pin cert §5). From `iUnion_clampedShell`. -/
theorem singularShell_iUnion (ε : ℝ) (r : ℕ) :
    ⋃ j : Fin (r + 1), singularShell (M₂ := M₂) (nn := nn) ε r j = Set.univ :=
  iUnion_clampedShell (weakEigCount ε) r

end DLNFibre.DLN.RLCT
