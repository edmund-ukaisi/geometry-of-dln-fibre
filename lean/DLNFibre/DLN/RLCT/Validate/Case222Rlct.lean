import DLNFibre.DLN.RLCT.Validate.Case222CoverGETail
import DLNFibre.DLN.RLCT.Validate.Case222Algebra
import DLNFibre.DLN.RLCT.Validate.Case222Value

/-!
# `DLNFibre.DLN.RLCT.Validate.Case222Rlct` — the `(2,2,2)` RLCT headline (ladder 3/3)

The `(2,2,2)` deep-linear square-Frobenius loss at the deepest point of the `B = 0` fibre has real
log-canonical threshold `3/2`. This file composes the two halves into the network-loss headline:

- the cover value `rlctAtOn myF222 0 = 3/2` (`rlctAtOn_myF222_eq`, `Case222CoverGETail`: the geometric
  `≥`-cover — clean-three, S2-free — antisymmetric with the cited `≤`-half `rlctAtOn_myF222_le`);
- the loss-identity seam `dlnLoss H222 0 = myF222 ∘ e222` (`dlnLoss222_eq_myF222`, `Case222Algebra`);
- the measure-preserving transport `rlctAtOn (dlnLoss H222 0) deepest222 = rlctAtOn myF222 0`
  (`rlctAtOn_dlnLoss222_transport`, `ParamsFlat222`).

Mirrors the `(1,1,1)` wrapper (`resolution_charts_case111`): the `⨅` over the cover index `Unit`
collapses (`iInf_unique`) to the single unit-leaf threshold `monomialThreshold 2 ![1,1] ![3,2] = 3/2`
(`case222_unit_leaf_threshold`). The third rung of the validation ladder `(1,1,1) → (2,1,2) → (2,2,2)`.
-/

open MeasureTheory
open scoped ENNReal
namespace DLNFibre.DLN.RLCT

/-- **The `(2,2,2)` core RLCT (on `Params`).** `rlctAtOn (dlnLoss H222 0) deepest222 = 3/2`: the
loss-identity seam (`dlnLoss222_eq_myF222`) + the measure-preserving transport
(`rlctAtOn_dlnLoss222_transport`) carry the cover value (`rlctAtOn_myF222_eq`) from `Fin 8 → ℝ` to the
network loss at the deepest point. -/
theorem case222_rlctAtOn_eq : rlctAtOn (dlnLoss H222 0) deepest222 = 3 / 2 := by
  rw [rlctAtOn_dlnLoss222_transport myF222 dlnLoss222_eq_myF222, rlctAtOn_myF222_eq]

/-- **The `(2,2,2)` headline (value form).** `rlctAt H222 (dlnLoss H222 0) deepest222 = 3/2` — the
local RLCT of the deep-linear loss at the deepest point of the `B = 0` fibre. The `≥`-half
(`rlctAtOn_myF222_ge'`) is axiom-clean (S2-free); the value rests on the cited `≤`-bound (`monomial_rlct`,
Aoyagi/Watanabe) via `rlctAtOn_myF222_le`. Mirror of `case111_rlct`. -/
theorem case222_rlct : rlctAt H222 (dlnLoss H222 0) deepest222 = 3 / 2 := by
  rw [← rlctAtOn_eq_rlctAt, case222_rlctAtOn_eq]

/-- **The `(2,2,2)` instance of `resolution_charts` (ladder 3/3).** Matches the general
`resolution_charts` (core form): `rlctAtOn (dlnLoss M 0) deepest = ⨅ monomialThreshold (d i)(k i)(h i)`.
For `M = (2,2,2)` the cover value is `3/2 = ⨅`, witnessed here by the single index `ι = Unit` with the
unit-leaf datum `d = 2`, `k = (1,1)`, `h = (3,2)` (`monomialThreshold = 3/2 = case222_unit_leaf_threshold`);
the `⨅`-over-`Unit` collapses (`iInf_unique`). (The full cover has 24 leaves, all threshold `3/2`; the
`⨅`-value `3/2` is what `resolution_charts` records, so the single-leaf witness suffices.) Mirror of
`resolution_charts_case111`. -/
theorem resolution_charts_case222 :
    ∃ (ι : Type) (_ : Fintype ι) (d : ι → ℕ) (k h : (i : ι) → Fin (d i) → ℕ),
      rlctAtOn (fun A : Params H222 =>
          dlnLoss H222 (0 : Matrix (Fin (H222 0)) (Fin (H222 (Fin.last 2))) ℝ) A) deepest222
        = ⨅ i : ι, monomialThreshold (d i) (k i) (h i) :=
  ⟨Unit, inferInstance, fun _ => 2, fun _ => (![1, 1] : Fin 2 → ℕ), fun _ => (![3, 2] : Fin 2 → ℕ),
    by rw [show (fun A : Params H222 =>
              dlnLoss H222 (0 : Matrix (Fin (H222 0)) (Fin (H222 (Fin.last 2))) ℝ) A)
            = dlnLoss H222 0 from rfl,
          case222_rlctAtOn_eq, iInf_unique, case222_unit_leaf_threshold]⟩

end DLNFibre.DLN.RLCT
