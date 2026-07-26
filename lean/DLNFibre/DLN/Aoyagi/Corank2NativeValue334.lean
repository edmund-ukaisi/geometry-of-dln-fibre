import DLNFibre.DLN.Aoyagi.Corank2NativeFan334

/-!
# `DLN.Aoyagi.Corank2NativeValue334` — the (C)-seat value data: pivot-cross `ek₀`, binding contract

The (C)-seat shared value data for the whole-conjugate born-native fan (`Corank2NativeFan334`), against
which the (B) seat builds the entry-equality `hentry`. Per leaf `c` (pivot-path `(p1, p2, p3)`), the
**pivot-cross** survivor exponent `ek₀ c = 1@p1 + 1@p2` (`pivot1 c = p1` the node-1 pivot, `pivot2 c =
p2` the node-2 native pivot). This is the survivor monomial of the CLEAN-144 leaves (single-entry
pivot-cross, `whole_conjugate_all288.out`: `divisorMin = 8`, survivor on `jac ≥ 7` coords). The
over-vanishing 144 (still `rlct ≥ 4`, higher monomial) are routed separately — see the scope note.

## Scope
- IN: `pivot1`/`pivot2`/`pivot3` (the leaf pivots via `idxEquiv`); `ek₀` (the pivot-cross exponent);
  `pivots_distinct` (`p1 ≠ p2`, so `ek₀` has exactly the two binding axes `{p1, p2}`); the reduction's
  `hbind` (`bindingAxes (ek₀ c)` nonempty) + `hunit_mult` (`ek₀ = 1` on its binding axes).
- OUT: `hentry` (the (B) seat, built against `ek₀`/`k0`); `k0` + the per-leaf `jac`/`unit` +
  `divisorMin ≥ 8` (the (C) tail); the over-vanishing feeder routing.
-/

open MeasureTheory Set Metric
open DLNFibre.Core.Aoyagi
open DLNFibre.DLN.Aoyagi.NativeFan334

namespace DLNFibre.DLN.Aoyagi.NativeValue334

/-- The node-1 pivot `p1 ∈ S1` of leaf `c`. -/
noncomputable def pivot1 (c : Fin numCharts) : Fin 21 := (idxEquiv c).1.1

/-- The node-2 native pivot `p2 ∈ σC1(p1)` of leaf `c`. -/
noncomputable def pivot2 (c : Fin numCharts) : Fin 21 := (idxEquiv c).2.1.1

/-- The node-3 native pivot `p3 ∈ σC2(p1)` of leaf `c`. -/
noncomputable def pivot3 (c : Fin numCharts) : Fin 21 := (idxEquiv c).2.2.1

/-- **The pivot-cross survivor exponent** `ek₀ c = 1@p1 + 1@p2` — the CLEAN-144 survivor monomial
`u_{p1}·u_{p2}` (squarefree, mult-1; the (B) seat proves `coreGen (k0 c) (gFin c w) = ∏ w^{ek₀ c}`
equals this exactly). -/
noncomputable def ek₀ (c : Fin numCharts) : Fin 21 → ℕ :=
  fun d => if d = pivot1 c ∨ d = pivot2 c then 1 else 0

theorem ek₀_pivot1 (c : Fin numCharts) : ek₀ c (pivot1 c) = 1 := by
  simp only [ek₀, or_true, true_or, if_true]

theorem ek₀_le_one (c : Fin numCharts) (d : Fin 21) : ek₀ c d ≤ 1 := by
  simp only [ek₀]; split_ifs <;> simp

/-- No `p ∈ S1` lies in its own permuted node-2 centre `σC1(p)` (`p = σ(20) ∉ σ(C1)`; `by decide`
over the 9 dominants). -/
theorem p1_notMem_sigmaC1Fs : ∀ p : Fin 21, p ∈ S1 → p ∉ sigmaC1Fs p := by decide

/-- **`p1 ≠ p2`** — the node-1 pivot is `σ(20) ∉ σ(C1) ∋ p2`, so the pivot-cross has two distinct
binding axes. -/
theorem pivots_distinct (c : Fin numCharts) : pivot1 c ≠ pivot2 c := by
  have hmem : pivot2 c ∈ sigmaC1Fs (pivot1 c) := (idxEquiv c).2.1.2
  have hS1 : pivot1 c ∈ S1 := (idxEquiv c).1.2
  intro h
  rw [← h] at hmem
  exact p1_notMem_sigmaC1Fs (pivot1 c) hS1 hmem

/-- **`hbind`** — the pivot-cross exponent has a binding axis (`p1`), so `bindingAxes` is nonempty. -/
theorem hbind (c : Fin numCharts) : (bindingAxes (ek₀ c)).Nonempty := by
  refine ⟨pivot1 c, ?_⟩
  rw [bindingAxes, Finset.mem_filter]
  exact ⟨Finset.mem_univ _, by rw [ek₀_pivot1]; exact Nat.one_pos⟩

/-- **`hunit_mult`** — `ek₀` is `1` on each of its binding axes (mult-1 / squarefree survivor). -/
theorem hunit_mult (c : Fin numCharts) (d : Fin 21) (hd : d ∈ bindingAxes (ek₀ c)) : ek₀ c d = 1 := by
  rw [bindingAxes, Finset.mem_filter] at hd
  exact le_antisymm (ek₀_le_one c d) hd.2

/-- **The binding axes are exactly the pivot-cross `{p1, p2}`.** -/
theorem bindingAxes_ek₀ (c : Fin numCharts) :
    bindingAxes (ek₀ c) = {pivot1 c, pivot2 c} := by
  ext d
  rw [bindingAxes, Finset.mem_filter]
  simp only [Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton, ek₀]
  constructor
  · intro h; by_contra hc; push_neg at hc; rw [if_neg (by tauto)] at h; exact absurd h (lt_irrefl 0)
  · intro h; rw [if_pos h]; exact Nat.one_pos

-- Forced axiom gate: the (C)-seat value data rests only on `[propext, Classical.choice, Quot.sound]`.
#assert_banked_clean_batch [ek₀_pivot1, ek₀_le_one, pivots_distinct, hbind, hunit_mult, bindingAxes_ek₀]

end DLNFibre.DLN.Aoyagi.NativeValue334
