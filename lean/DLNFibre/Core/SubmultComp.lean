import DLNFibre.Core.Submult

/-!
# `DLNFibre.Core.SubmultComp` — interval composition of the sub-product

The rank-pattern sub-products compose over a middle index: for `i ≤ j ≤ k`,
`submult d A i k = submult d A j k * submult d A i j` (splitting `A_k ⋯ A_{i+1}` at layer `j`). Both
factors' shared middle dimension is `d j` (the *same* expression on both sides), so the product is
well-typed with no `succ`/`castSucc` cast friction. The `i = 0`, `j = 1`, `k = last` instance is the
innermost-factor peel `mult = (A_{N-1} ⋯ A_1) · A_0` that the layer-0 residual decomposition rides.

Network-free (`DLNFibre.Core`); never imports `DLNFibre.DLN`.
-/

namespace DLNFibre.Core

open Matrix

universe u

variable {k : Type u} [CommRing k] {N : ℕ}

/-- **Interval composition.** `submult d A i k = submult d A j k * submult d A i j` for `i ≤ j ≤ k`
(split the sub-product at the middle layer `j`). By induction on the upper index `k` through
`submult_succ`; the split point `j = k.succ` vs `j ≤ k.castSucc` dispatches the successor step. -/
theorem submult_comp (d : Fin (N + 1) → ℕ) (A : Tuple (k := k) d) (i j : Fin (N + 1))
    (hij : i ≤ j) :
    ∀ (m : Fin (N + 1)) (hjm : j ≤ m),
      submult d A i m (hij.trans hjm) = submult d A j m hjm * submult d A i j hij := by
  intro m
  induction m using Fin.induction with
  | zero =>
    intro hjm
    obtain rfl : j = 0 := le_antisymm hjm (Fin.zero_le _)
    obtain rfl : i = 0 := le_antisymm hij (Fin.zero_le _)
    rw [submult_self, one_mul]
  | succ p ih =>
    intro hjm
    rcases eq_or_lt_of_le hjm with hje | hjlt
    · -- j = p.succ: the left factor is the empty (identity) product
      subst hje
      rw [show submult d A p.succ p.succ hjm = 1 from submult_self d A p.succ, Matrix.one_mul]
    · -- j ≤ p.castSucc: peel `A_p` off both `i`-side and `j`-side, then reassociate
      have hjc : j ≤ p.castSucc := Fin.le_castSucc_iff.mpr hjlt
      rw [submult_succ d A i p (hij.trans hjc), submult_succ d A j p hjc, ih hjc,
        Matrix.mul_assoc]
end DLNFibre.Core
