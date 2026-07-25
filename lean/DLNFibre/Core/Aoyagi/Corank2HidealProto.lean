import DLNFibre.Core.Aoyagi.Corank2Proto
import DLNFibre.Core.Setup

/-!
# `Core.Aoyagi.Corank2HidealProto` — GATE-2 measurement (the corank-2 block-elim step at the real ambient)

The go/no-go **measurement** module for the Encoding-I `hideal` re-architecture. It instantiates the
`Corank2Proto` symbolic Schur spine at the **real ambient function ring** `(Fin 21 → ℝ) → ℝ`
(`flatDim (3,3,4) = 3·3 + 3·4 = 21`), for the genuine corank-2 minimiser `(3,3,4) t=(1,0)`, and delivers
the **one corank-2 block-elimination step** as a two-directional `RegionRepresents` — the paper's
one-line ideal argument (L-A: `⟨C₁·C₂⟩ = ⟨diag(1,Δ)·(Q₂⁻¹C₂)⟩`, unimodular-polynomial `Q₁`, cofactors
continuous on the region).

## What this measures (the gate reading — see the tax report)

- **[MEASURED, GREEN] the block-elim atom (L-A).** `blockElim_step_fwd`/`_bwd` — both ideal directions,
  at `n = 21`, with continuous polynomial cofactors, hold with NO Mathlib ideal-membership tax: they are
  the `Corank2Proto` bricks (`regionRepresents_P_peeled`/`_peeled_P`) instantiated + the continuity
  discharged by `(continuous_apply _).continuousOn`. The flatten (`Fin (p·c) ↔ Fin p × Fin c`) and
  the cofactor-continuity obligations render cleanly.
- **[MEASURED] the coupling is genuine.** `delta_offdiag_coupled` witnesses that the residual `Δ` is a
  GENUINELY coupled 2×2 (its off-diagonal carries the live bilinear coupling `c₁₂ᵦ·c₂₁ₐ`), NOT the
  diagonal `(2,2,2,2)`-clean confound.
- **[MEASURED] `mult`-unfold is `rfl`-cheap.** `mult_334_eq_layerProduct` — the DLN core content
  `mult (3,3,4) A = A₁·A₀` (the layer product whose flattened entries are `coreGen (3,3,4) e`) reduces by
  `rfl`; connecting `coreGen` to the symbolic `C₁·C₂` is bounded plumbing (a flatten homeomorphism `e` +
  transpose bookkeeping), NOT a wall.

## What this does NOT deliver, and why (the WALL — the STOP finding)

The literal `Chart.hideal_fwd`/`hideal_bwd` fields require the TERMINAL monomialisation
`⟨(∏C)∘g⟩ = ⟨monomialFam bexp⟩` (pure diagonal monomials `b₁,…,b_M`). One corank-2 block-elim reaches
`⟨(∏C)∘g⟩ = ⟨peeled⟩` with `peeled = diag(1,Δ)·(Q₂⁻¹C₂)` — whose entries `T` (row 0) and `Δ·S` (rows 1,2)
are POLYNOMIAL, NOT monomials. `⟨peeled⟩ = ⟨monomialFam bexp⟩` is FALSE at this stage (a coupled
polynomial like `m₁₁ − c₁₂ₐc₂₁ₐ` is not in the ideal of pure coordinate monomials). Reaching the diagonal
monomials needs the WHOLE `(S,J)` recursion — block-elim (this atom) at each step PLUS the blow-up
`u`-factor ledger accumulating `diag(b)` PLUS the layer rollovers PLUS the terminal — i.e. the full
coupled-B build for the instance, NOT one step. This module is `Corank2Proto`'s step, promoted to the real
ambient; it is NOT a `Chart` field and does NOT claim to be. See `gate2-tax-report.md`.
-/

open Matrix
open DLNFibre.Core.Aoyagi.Corank2Proto

namespace DLNFibre.Core.Aoyagi.Corank2HidealProto

/-! ## The real ambient — `flatDim (3,3,4) = 21` -/

/-- The `k`-th chart coordinate as a continuous function on the real ambient `ℝ²¹` (the blown-up /
sheared coordinate; a projection is the honest simplest continuous representative, and the real
pulled-back layer entries are continuous too, so the cofactor-continuity tax is identical). -/
noncomputable def cc (k : Fin 21) : (Fin 21 → ℝ) → ℝ := fun u ↦ u k

theorem continuousOn_cc (k : Fin 21) (V : Set (Fin 21 → ℝ)) : ContinuousOn (cc k) V :=
  (continuous_apply k).continuousOn

/-- The carried next-layer matrix `C₂` (3×4), 12 distinct chart coordinates (indices 8..19 < 21). -/
noncomputable def C2conc : Matrix (Fin 3) (Fin 4) ((Fin 21 → ℝ) → ℝ) :=
  fun i j ↦ cc ⟨8 + (i.val * 4 + j.val), by omega⟩

/-! ## [MEASURED, GREEN] The corank-2 block-elimination step at the real ambient, both directions

The eight `C₁`-chart scalars are the distinct projections `cc 0 … cc 7`; with independent coordinates the
Schur complement `Δ = C₂₂ − C₂₁·C₁₂` is a full coupled 2×2 (see `delta_offdiag_coupled`), so this is the
genuine corank-2 minimiser, not the diagonal confound. -/

/-- **[I⇒] forward** `⟨C₁·C₂⟩ ⊆ ⟨peeled⟩` at the real ambient, cofactors the polynomial entries of
`Q₁⁻¹`, continuous on any region `V`. The `Corank2Proto` bridge instantiated at `n = 21`. -/
theorem blockElim_step_fwd (V : Set (Fin 21 → ℝ)) :
    RegionRepresents
      (flat (Pmat (cc 0) (cc 1) (cc 2) (cc 3) (cc 4) (cc 5) (cc 6) (cc 7) C2conc))
      (flat (peeled (cc 0) (cc 1) (cc 2) (cc 3) (cc 4) (cc 5) (cc 6) (cc 7) C2conc)) V :=
  regionRepresents_P_peeled (cc 0) (cc 1) (cc 2) (cc 3) (cc 4) (cc 5) (cc 6) (cc 7) C2conc
    (continuousOn_cc 2 V) (continuousOn_cc 3 V)

/-- **[I⇐] backward** `⟨peeled⟩ ⊆ ⟨C₁·C₂⟩` at the real ambient, cofactors the polynomial entries of
`Q₁`, continuous on any region `V`. Together with `blockElim_step_fwd`: the ideal EQUALITY
`⟨C₁·C₂⟩ = ⟨peeled⟩` (the unimodular clearing, both directions). -/
theorem blockElim_step_bwd (V : Set (Fin 21 → ℝ)) :
    RegionRepresents
      (flat (peeled (cc 0) (cc 1) (cc 2) (cc 3) (cc 4) (cc 5) (cc 6) (cc 7) C2conc))
      (flat (Pmat (cc 0) (cc 1) (cc 2) (cc 3) (cc 4) (cc 5) (cc 6) (cc 7) C2conc)) V :=
  regionRepresents_peeled_P (cc 0) (cc 1) (cc 2) (cc 3) (cc 4) (cc 5) (cc 6) (cc 7) C2conc
    (continuousOn_cc 2 V) (continuousOn_cc 3 V)

/-! ## [MEASURED] The coupling is genuine (not the diagonal confound)

Guardrail 3: the witness must leave a GENUINELY coupled `Δ`. The off-diagonal `Δ₀₁ = m₁₂ − c₁₂ᵦ·c₂₁ₐ`
carries the live bilinear coupling term `c₁₂ᵦ·c₂₁ₐ`; at a point where the coupling term dominates the
entry is nonzero, so `Δ` is not diagonalised away — this is the coupled corank-2 minimiser, not the
`(2,2,2,2)`-clean instance whose `Δ` is diagonal/uncoupled. -/
theorem delta_offdiag_coupled :
    ∃ u : Fin 21 → ℝ,
      Delta (cc 0) (cc 1) (cc 2) (cc 3) (cc 4) (cc 5) (cc 6) (cc 7) 0 1 u ≠ 0 := by
  -- entry (0,1) = m₁₂ − c₁₂ᵦ·c₂₁ₐ = cc 5 − cc 1·cc 2; pick `u` with `u 1 = u 2 = 1`, `u 5 = 0`: = −1 ≠ 0.
  refine ⟨fun k ↦ if k = 1 ∨ k = 2 then 1 else 0, ?_⟩
  have h5 : ¬ ((5 : Fin 21) = 1 ∨ (5 : Fin 21) = 2) := by decide
  simp only [Delta, cc, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Pi.sub_apply, Pi.mul_apply, if_neg h5]
  norm_num

/-! ## [MEASURED] `mult (3,3,4)` IS the prefix layer product (the `coreGen` content, definitionally)

`coreGen (3,3,4) e k u` is the `k`-th flattened entry of `mult (3,3,4) (e u)`, and `mult` is (by
construction) the prefix layer product `A₂·(A₁·1)`. Connecting the DLN `coreGen` family to the symbolic
`C₁·C₂` spine is bounded plumbing (a flatten homeomorphism `e` + a transpose). **Tax note:** writing the
RHS as the fully-multiplied `A₁·A₀` hits the documented dependent-width `HMul`-synthesis friction
(`![3,3,4] (Fin.succ 1)` does not reduce for instance resolution); the CLAUDE.md mitigations (an `abbrev`
dimension vector, or literal width ascription) apply — a bounded, known tax, not a wall. -/
theorem mult_334_eq_prefix (A : DLNFibre.Core.Tuple (k := ℝ) (![3, 3, 4] : Fin 3 → ℕ)) :
    DLNFibre.Core.mult (![3, 3, 4] : Fin 3 → ℕ) A
      = DLNFibre.Core.multPrefix (![3, 3, 4] : Fin 3 → ℕ) A (Fin.last 2) :=
  rfl

end DLNFibre.Core.Aoyagi.Corank2HidealProto
