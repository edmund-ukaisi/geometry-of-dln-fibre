import DLNFibre.Core.CascadeAchiever
import DLNFibre.Core.CTheta
import DLNFibre.DLN.RLCT.Foundations.Lambda

/-!
# `MvalMultSum` — Aoyagi's `Mval` = the LR quadratic form, as a SIGNED ring identity (#136, SPECIFY)

The Le Halleur–Rimányi "geometric codim is the new content" identity, stated at its TRUE scope. The
combinatorial bridge: Aoyagi's single-sum `Mval M T` equals the LR quadratic form `codimForm` evaluated
on the finite-difference array `diff (cascadeRank M T)` of the cascade's resolution rank pattern.

**Scope (Codex xhigh, decorrelated, 2026-06-23 — the honesty boundary).** This is the SIGNED integer
ring identity: it holds for ALL `M, T` with NO admissibility/realizability hypothesis (the collapse uses
only the additive structure of `r_{ij} = ρ_j + (M_i − ρ_i)`). It is STRICTLY BROADER than the geometric
reading: `codimForm (diff r) = codim of the orbit closure` (Voigt) requires `diff r ≥ 0` — a realizable
nonneg Kostant partition = **width-monotone `M`** — which FAILS on width-spike `M` (negative `diff r`
entries; the spike-witness 7310/10820). On width-spike `M` the ring identity STILL holds, but `codimForm`
is no longer a geometric codimension. So this file proves the RING ALGEBRA only; the geometric corollary
(under `diff r ≥ 0`) is a separate, scoped statement (NOT here).

The collapse (boundary-supported `diff r`): with `ρ = expSurvivor` (`ρ_0 = M_0`, `ρ_{j+1} = T_j`) and
`q_a := M_a − ρ_a`, the second difference `diff (cascadeRank) a b` vanishes in the interior; it is nonzero
only on the top row (`= ρ_b − ρ_{b+1}`) and the right column (`= q_a − q_{a-1}`). In `codimForm`'s
quadruple sum, the first factor forces the row index, the second forces the right column; the surviving
double sum telescopes (`q_0 = 0`) to `Mval`.

**STATUS: SPECIFY** — statement stated, body `sorry`, signature validated. The PROVE (the boundary-support
lemmas + triangular `Icc` reindex + telescope, ~60–100 LoC) is gated on the controller's priority call
(#136 is off the binding `½·minAdm` path). The `sorry` here is a building block under a (to-be-reviewed)
correct statement, NOT a claim of proof.
-/

open DLNFibre.Core

namespace DLNFibre.DLN.RLCT

variable {L : ℕ}

/-- The cascade's **resolution rank pattern** `r_{ij} = ρ_j + (M_i − ρ_i)` as a `ℤ → ℤ → ℤ` array (so the
finite-difference `diff` applies), `ρ = expSurvivor M T` the running rank. Out-of-range indices clamp to
`0` (the `diff` boundary convention). The lift reads `ρ`/`M` at `Fin (L+1)` indices via `Int.toNat`,
guarded to `[0, L]`; outside the square the entry is `0`. -/
noncomputable def cascadeRank (M : Fin (L + 1) → ℕ) (T : Fin L → ℕ) : ℤ → ℤ → ℤ :=
  fun i j =>
    if hi : 0 ≤ i ∧ i ≤ (L : ℤ) then
      if hj : 0 ≤ j ∧ j ≤ (L : ℤ) then
        let iF : Fin (L + 1) := ⟨i.toNat, by omega⟩
        let jF : Fin (L + 1) := ⟨j.toNat, by omega⟩
        (expSurvivor M T jF : ℤ) + ((M iF : ℤ) - (expSurvivor M T iF : ℤ))
      else 0
    else 0

/-- **#136 SIGNED ring identity (SPECIFY).** Aoyagi's `Mval M T` equals the LR quadratic form `codimForm`
on the finite-difference array of the cascade resolution pattern — a ring identity, NO admissibility. The
geometric reading (`codimForm = codim Ō`) is the separate width-monotone-scoped corollary. -/
theorem Mval_eq_codimForm_diff_cascadeRank (M : Fin (L + 1) → ℕ) (T : Fin L → ℕ) :
    Mval M T = codimForm L (diff (cascadeRank M T)) := by
  sorry

end DLNFibre.DLN.RLCT
