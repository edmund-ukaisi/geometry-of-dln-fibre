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

`blockShear_step` — the **per-factor threaded block-shear identity** (vslice §2, the one new brick):
`M_i · X_i · M_{i+1}⁻¹ = [[α_i, B_i], [0, Y_i]]` block-upper-triangular with the `K_{i+1}` threading
`α_i = A_i + B_i K_{i+1}`, `Y_i = D_i − γ_i α_i⁻¹ B_i` (`γ_i = C_i + D_i K_{i+1}`). Bounded block
algebra (`fromBlocks_multiply` + the `⅟α·α = 1` cancellation). Axiom clean-three.

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

/-! ## The threaded block-shear step (the load-bearing new brick, LANDED) -/

/-- **The threaded block-shear identity (vslice §2, the ONE new brick).** With the incoming shear
coefficient `Kp = K_{i+1}` and the corank-`q` block split `X_i = [[A,B],[C,D]]`, define (threading
right-to-left) `α = A + B·Kp` (assumed invertible on the chart), `γ = C + D·Kp`, `K_i = γ·α⁻¹`,
`Y = D − γ·α⁻¹·B`. Then the unit-triangular conjugation `M_i · X_i · M_{i+1}⁻¹` is block-UPPER
triangular with the invertible pivot `α`:

    [[1, 0], [−K_i, 1]] · [[A, B], [C, D]] · [[1, 0], [Kp, 1]] = [[α, B], [0, Y]].

Direct block multiply (`fromBlocks_multiply` twice + `fromBlocks_inj`): the `K_i = γ·α⁻¹` threading
kills the lower-left block (`−K_i·α + γ = 0` via `⅟α·α = 1`), exposing the reduced factor
`Y = D − γ·α⁻¹·B` as the corank block. The `Kp` correction `α = A + B·Kp` is LOAD-BEARING — naive
independent-Schur (`Kp = 0`) is FALSE for `L ≥ 3` (vslice §2 note). This is the per-factor step the
telescoping composes (`M_{i+1}⁻¹` cancels the next factor's `M_{i+1}`) into the tail-product normal
form the rank equation reads off. -/
theorem blockShear_step {q a b : ℕ}
    (A : Matrix (Fin q) (Fin q) ℝ) (B : Matrix (Fin q) (Fin b) ℝ)
    (C : Matrix (Fin a) (Fin q) ℝ) (D : Matrix (Fin a) (Fin b) ℝ)
    (Kp : Matrix (Fin b) (Fin q) ℝ) [Invertible (A + B * Kp)] :
    fromBlocks (1 : Matrix (Fin q) (Fin q) ℝ) 0 (-((C + D * Kp) * ⅟(A + B * Kp))) 1
        * fromBlocks A B C D
        * fromBlocks (1 : Matrix (Fin q) (Fin q) ℝ) 0 Kp 1
      = fromBlocks (A + B * Kp) B 0 (D - (C + D * Kp) * ⅟(A + B * Kp) * B) := by
  rw [fromBlocks_multiply, fromBlocks_multiply, fromBlocks_inj]
  set P : Matrix (Fin a) (Fin q) ℝ := (C + D * Kp) * ⅟(A + B * Kp) with hP
  have hα : ⅟(A + B * Kp) * (A + B * Kp) = 1 := invOf_mul_self _
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp
  · simp
  · -- lower-left: `−P·A + C + (−P·B + D)·Kp = 0`, `P = (C+D·Kp)·⅟(A+B·Kp)`.
    simp only [Matrix.one_mul, Matrix.mul_one, Matrix.zero_mul, Matrix.mul_zero, zero_add,
      add_zero, Matrix.neg_mul, Matrix.add_mul]
    rw [Matrix.mul_assoc P B Kp]
    have hfac : P * A + P * (B * Kp) = C + D * Kp := by
      rw [← Matrix.mul_add, hP, Matrix.mul_assoc, hα, Matrix.mul_one]
    have hrw : -(P * A) + C + (-(P * (B * Kp)) + D * Kp)
        = (C + D * Kp) - (P * A + P * (B * Kp)) := by abel
    rw [hrw, hfac, sub_self]
  · -- lower-right: `−P·B + D = D − P·B = Y`.
    simp only [Matrix.one_mul, Matrix.mul_one, Matrix.zero_mul, Matrix.mul_zero, zero_add,
      add_zero, Matrix.neg_mul]
    rw [neg_add_eq_sub]

end DLNFibre.DLN.RLCT
