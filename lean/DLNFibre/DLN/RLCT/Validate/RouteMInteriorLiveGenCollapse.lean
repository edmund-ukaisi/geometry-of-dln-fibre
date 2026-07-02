import DLNFibre.DLN.RLCT.Validate.RouteMBdetMonomial

/-!
# `RouteMInteriorLiveGenCollapse` — the multi-boundary LHS collapse (decode task-iv infrastructure)

The signature-independent algebraic core of the general-`L` `BdetMonomial` decode (task iv). The
general-`L` boundary-factor determinant chain-rule split is

  `|det D(BchartLeaf ∘ kLDU)(pbo u)| = (Factor 1) · (Factor 2)`

with, per boundary `s : Fin L`,

  * Factor 1 = `∏_s |∏_i q_{s,i}|^{r_s + c_s}` (the Schur staircase det, each `det K_s = ∏_i q_{s,i}`),
  * Factor 2 = `∏_s ∏_i |q_{s,i}|^{2(t_s − 1 − i)}` (the ambient lens det, `kLDU_ambient_det_pbo_gen`).

This module proves the multi-boundary LHS collapse folding them to a single per-pivot monomial

  `∏_s ∏_i |q_{s,i}|^{(r_s + c_s) + 2(t_s − 1 − i)}`,

purely by `Finset.prod` distributivity + the banked single-boundary `lhs_collapse` (`RouteMBdetMonomial`,
generic in `τ r c q`) applied per boundary. NO `Fin.prod_univ_two`, NO leaf special-casing — the fold
runs over ALL boundaries `k : Fin L`. Signature-independent: it takes the per-boundary K-pivots
`q : ∀ s, Fin (t s) → ℝ` and block widths `t r c : Fin L → ℕ` abstractly, so it composes with whatever
concrete Factor-1 / Factor-2 the downstream decode supplies.

* `lhs_collapse_multiboundary` — the per-boundary product fold.

Axiom-clean `[propext, Classical.choice, Quot.sound]` (finite products; no analysis).
-/

namespace DLNFibre.DLN.RLCT

open scoped BigOperators

variable {L : ℕ}

/-- **The multi-boundary LHS collapse** — for per-boundary K-pivots `q s : Fin (t s) → ℝ` and block
exponents `r s`, `c s`, the Factor-1 × Factor-2 product folds to the single per-pivot monomial:

  `(∏_s |∏_i q s i|^{r s + c s}) · (∏_s ∏_i |q s i|^{2(t s − 1 − i)})`
    `= ∏_s ∏_i |q s i|^{(r s + c s) + 2(t s − 1 − i)}`.

`Finset.prod_mul_distrib` merges the two `∏_s` products; per boundary `s` the banked single-boundary
`lhs_collapse (t s) (r s) (c s) (q s)` closes the fold. -/
theorem lhs_collapse_multiboundary (t r c : Fin L → ℕ) (q : ∀ s : Fin L, Fin (t s) → ℝ) :
    (∏ s : Fin L, |∏ i, q s i| ^ (r s + c s))
        * (∏ s : Fin L, ∏ i, |q s i| ^ (2 * ((t s : ℕ) - 1 - (i : ℕ))))
      = ∏ s : Fin L, ∏ i : Fin (t s),
          |q s i| ^ ((r s + c s) + 2 * ((t s : ℕ) - 1 - (i : ℕ))) := by
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl (fun s _ => ?_)
  exact lhs_collapse (t s) (r s) (c s) (q s)

end DLNFibre.DLN.RLCT
