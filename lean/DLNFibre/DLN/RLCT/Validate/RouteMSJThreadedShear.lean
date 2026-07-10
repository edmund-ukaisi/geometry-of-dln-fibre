import DLNFibre.Core.SchurChartIff
import DLNFibre.DLN.RLCT.Validate.RouteMSJChartAlgebra

/-!
# `DLNFibre.DLN.RLCT.Validate.RouteMSJThreadedShear` — threaded normal-slice bricks

The **opaque-width matrix-algebra bricks** for the front-peel normal-slice transfer
(`normalSlice_transfer`, `RouteMFrontPeelCarrier`). Network-free, S2-free (pure `Matrix.rank` /
`frobSq` algebra); the measure-theoretic assembly lives in the carrier.

The pen-and-paper witness (`threads/genm-vslice/normalslice-cert.md`, §2–4) is the threaded normal
form of the tail product `P = prod (tailChain M) A'`. Block each tail factor by the corank-`q` split
and thread right-to-left with `K_L = 0`, `α_i = A_i + B_i K_{i+1}`, `K_i = γ_i α_i⁻¹`,
`Y_i = D_i − γ_i α_i⁻¹ B_i`. The unit-triangular shears `M_i = [[I,0],[−K_i,I]]` (det 1) telescope
to

    M_1 · P · (chart) = [[ α_1···α_{L-1}, * ],[ 0, Y_1···Y_{L-1} ]]                    (§2)

with the `α`-product block invertible on the chart. Two consequences the carrier consumes:

* **the rank equation** `rank P = q + rank (Y_1···Y_{L-1})` — so `{rank P ≤ q} ⟺ {reduced product
  = 0}`, and the reduced product is the `prod` of the reduced chain `redTail M q`;
* **the loss split** `frobSq(A₀·P) ≃ ‖R‖² + frobSq(reduced product)` (disjoint blocks) — the
  `L = 2` single-matrix base is the banked `frobSq_schur_block_split` (`RouteMSJChartAlgebra`).

## What is LANDED here

`rank_eq_q_add_of_normalForm` / `rank_eq_q_iff_reduced_zero` — the **abstract rank-transfer core**:
once `P` (block-indexed by the corank-`q` split) is conjugated by units `U, V` to a block-upper form
`fromBlocks α B 0 Z` with `α` an invertible `q × q` block, `rank P = q + rank Z`, and `rank P = q ↔
Z = 0`. Proved from `Core.rank_fromBlocks_invertible₁₁` (the LDU Schur block-rank) + the unit rank
transports `Matrix.rank_mul_eq_{left,right}_of_isUnit_det`. This is the linear-algebra output of
threaded normal form; constructing the conjugating units `U, V` and the reduced factor `Z`
(the threaded shear at opaque widths + its measure-preservation) is the carrier constructor content.
-/

namespace DLNFibre.DLN.RLCT

open Matrix
open scoped BigOperators

/-! ## The abstract rank-transfer core (LANDED) -/

/-- **Rank transfer through a unit conjugation to block-upper form.** If square units `U, V`
conjugate a corank-`q`-split matrix `P` to the block-upper form `fromBlocks α B 0 Z` with `α`
(the `q × q` pivot block) invertible, then `rank P = q + rank Z`. Unit conjugation preserves rank
(`rank_mul_eq_{right,left}_of_isUnit_det`), and the block-upper rank is `q + rank Z` by the LDU
Schur identity `Core.rank_fromBlocks_invertible₁₁` (the off-diagonal `0` kills the Schur correction,
so the complement is `Z` itself). -/
theorem rank_eq_q_add_of_normalForm {q a b : ℕ}
    (P : Matrix (Fin q ⊕ Fin a) (Fin q ⊕ Fin b) ℝ)
    (α : Matrix (Fin q) (Fin q) ℝ) (B : Matrix (Fin q) (Fin b) ℝ) (Z : Matrix (Fin a) (Fin b) ℝ)
    (U : Matrix (Fin q ⊕ Fin a) (Fin q ⊕ Fin a) ℝ)
    (V : Matrix (Fin q ⊕ Fin b) (Fin q ⊕ Fin b) ℝ)
    (hU : IsUnit U.det) (hV : IsUnit V.det) (hα : IsUnit α.det)
    (hnf : U * P * V = fromBlocks α B (0 : Matrix (Fin a) (Fin q) ℝ) Z) :
    P.rank = q + Z.rank := by
  have hrankP : P.rank = (fromBlocks α B (0 : Matrix (Fin a) (Fin q) ℝ) Z).rank := by
    rw [← hnf, Matrix.rank_mul_eq_left_of_isUnit_det _ _ hV,
      Matrix.rank_mul_eq_right_of_isUnit_det _ _ hU]
  rw [hrankP, DLNFibre.Core.rank_fromBlocks_invertible₁₁ α B 0 Z hα]
  simp

/-- **The exact-rank ↔ reduced-product-zero characterisation.** Under the same block-upper normal
form, `rank P = q ↔ Z = 0`: the rank equation gives `rank P = q + rank Z`, and `rank Z = 0 ↔ Z = 0`
(`Matrix.rank_eq_zero_iff`). This is the CoV image of the stratum `{rank P = q}` — it is the
zero-locus of the reduced product `Z = prod (redTail M q) Y`. -/
theorem rank_eq_q_iff_reduced_zero {q a b : ℕ}
    (P : Matrix (Fin q ⊕ Fin a) (Fin q ⊕ Fin b) ℝ)
    (α : Matrix (Fin q) (Fin q) ℝ) (B : Matrix (Fin q) (Fin b) ℝ) (Z : Matrix (Fin a) (Fin b) ℝ)
    (U : Matrix (Fin q ⊕ Fin a) (Fin q ⊕ Fin a) ℝ)
    (V : Matrix (Fin q ⊕ Fin b) (Fin q ⊕ Fin b) ℝ)
    (hU : IsUnit U.det) (hV : IsUnit V.det) (hα : IsUnit α.det)
    (hnf : U * P * V = fromBlocks α B (0 : Matrix (Fin a) (Fin q) ℝ) Z) :
    P.rank = q ↔ Z = 0 := by
  rw [rank_eq_q_add_of_normalForm P α B Z U V hU hV hα hnf]
  constructor
  · intro h
    have hz : Z.rank = 0 := by omega
    exact (Matrix.rank_eq_zero_iff Z).mp hz
  · intro h
    rw [h, (Matrix.rank_eq_zero_iff (0 : Matrix (Fin a) (Fin b) ℝ)).mpr rfl, Nat.add_zero]

end DLNFibre.DLN.RLCT
