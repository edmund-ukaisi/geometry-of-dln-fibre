import DLNFibre.DLN.RLCT.Validate.RouteMSchurFiring

/-!
# `DLNFibre.DLN.RLCT.Validate.RouteMSchurDirectMorseP` — the shared `Fin p` chart plumbing + cap-B branch

The output-width-`p` generalisation of the per-chart angular machinery (`RouteMSchurFiring`'s `Fin 4`
top-row identity / shear), used by BOTH the cap-B `directMorse` branch and the cap-A carve-peel branch of
`schurRecStep_p` (task #146). This file builds the SHARED `Fin p` plumbing first, then the cap-B branch.

The `Fin 4 → Fin p` swap in these lemmas is mechanical (the `4` is the S-column width, summed opaquely),
but it is genuinely load-bearing (Codex flagged the directMorse angular bound — a naive `frobSq(R·S) ≥
c₀·frobSq(S)` is FALSE, since `R` can annihilate `S`; the correct bound is the carve's own N2b one-pivot
Schur/Morse lower bound, with the residual term DROPPED in the cap-B regime).

## Shared plumbing
* `frobSqTopRowP_eq_shearP` — the top-row identity `frobSq(top row of R·S) = ∑_q (sheared top row)²`, the
  `Fin p` analog of `frobSqTopRow_eq_shear`. The pivot `R₀₀ = 1` makes the `j = 1` block read off `S₀ q`;
  the rest is the shear `S₀q + ∑_a R₀,₁₊ₐ · S₁₊ₐ,q`.
-/

open MeasureTheory
namespace DLNFibre.DLN.RLCT

/-! ## Shared `Fin p` chart plumbing -/

/-- **The `Fin p` top-row identity** (`Fin p` analog of `frobSqTopRow_eq_shear`). For an angular matrix `R`
with pivot `R ⟨0⟩ ⟨0⟩ = 1`, the squared norm of the TOP ROW of `R·S` equals the sum over the `Fin p`
columns of the squared SHEARED entry `S₀q + ∑_a R₀,₁₊ₐ · S₁₊ₐ,q`. The `4 → p` swap is verbatim: the `p`
appears only as the opaque `∑ q : Fin p` column sum. -/
theorem frobSqTopRowP_eq_shearP (r p : ℕ) (hr : 3 ≤ r) (R : Fin r → Fin r → ℝ)
    (hpiv : R ⟨0, by omega⟩ ⟨0, by omega⟩ = 1) (S : Fin r → Fin p → ℝ) :
    frobSq (fun a : Fin 1 => rmatMul R S ⟨(a : ℕ), by omega⟩)
      = ∑ q, (S ⟨0, by omega⟩ q
          + ∑ a : Fin (r - 1), R ⟨0, by omega⟩ ⟨1 + (a : ℕ), by omega⟩ * S ⟨1 + (a : ℕ), by omega⟩ q) ^ 2 := by
  unfold frobSq
  rw [Fin.sum_univ_one]
  refine Finset.sum_congr rfl (fun q _ => ?_)
  congr 1
  show rmatMul R S ⟨0, by omega⟩ q = _
  unfold rmatMul
  rw [fin_sum_block_split 1 (show (1 : ℕ) ≤ r by omega) (fun k : Fin r => R ⟨0, by omega⟩ k * S k q)]
  congr 1
  · rw [Fin.sum_univ_one]
    have h0 : (⟨(0 : Fin 1), lt_of_lt_of_le (0 : Fin 1).2 (show (1:ℕ) ≤ r by omega)⟩ : Fin r)
        = ⟨0, by omega⟩ := rfl
    rw [h0, hpiv, one_mul]

end DLNFibre.DLN.RLCT
