import DLNFibre.DLN.RLCT.Validate.RouteMLayerSplit

/-!
# `DLNFibre.DLN.RLCT.Validate.RouteMSJDecoratedCharge` — the decorated peel-charge soundness

**Thread `genm-sjnative`, the native decorated R-BLOWUP route → `sjJointResolution`.** The FIRST
combinatorial brick of the decorated `(S,J)` recursion contract (design certificate
`expeditions/2026-06-20-aoyagi-full/threads/genm-r1decorated/cert.md`, deliverable A; STEP-0 gate
`threads/genm-sjnative/step0-derisk.md`, PASS). The decorated finiteness predicate carries an accumulated
charge inside the induction so the peel is threshold-monotone; this module proves the **soundness** of one
peel — the threshold-monotonicity inequality the certificate names `carrierThreshold_mono` (exact-verified
`0/171`, cert DATA-C).

## The peel and its soundness

One decorated peel resolves the leading layer at a legal cut `u ≤ min(M₀,M₁)`, emitting the Case-2 block
charge `peelCharge M u = (M₀−u)(M₁−u)` and advancing to the reduced chain `redChain u M` (one fewer
layer). Soundness = the accumulated threshold never over-runs: the reduced chain's threshold plus the
emitted charge dominates the parent threshold,

    minAdm M  ≤  peelCharge M u  +  minAdm (redChain u M).

Equivalently over `ℝ`, `½·minAdm M − ½·peelCharge M u ≤ ½·minAdm (redChain u M)`: the exponent shift
`c' ↦ c' − ½·peelCharge` on the reduced chain keeps `c'` below the reduced threshold whenever it was below
the parent threshold. This is the soundness `decorated_peel_step` reduces to (the analytic peel — the
radial Morse charge and the measure change of variables — is the deferred mountain; this is its
combinatorial gate).

It is IMMEDIATE from the banked value-fold `LayerSplit_value_eq_minAdm`: the RHS is a member of the
`inf'` whose value is `minAdm M`, so `minAdm M ≤ RHS`. The binding cut (where equality holds) is the
achiever of that `inf'` — recorded here for non-vacuity.

S2-FREE: pure `ℕ`/`ℝ` order algebra on the banked `minAdm`/`redChain`; axiom-clean
`[propext, Classical.choice, Quot.sound]`. No measure theory.
-/

namespace DLNFibre.DLN.RLCT

open Finset

variable {L : ℕ}

/-- **The Case-2 block charge of one decorated peel at cut `u`**: `(M₀−u)(M₁−u)`, the block codimension
read directly off the blow-up centre (the exponent the radial contributes; `= LayerSplit.codim`). -/
def peelCharge (M : Fin (L + 1) → ℕ) (u : ℕ) : ℕ := (M 0 - u) * (M 1 - u)

/-- **The decorated peel-charge soundness (the `ℕ` form).** For a `≥ 3`-width chain `M` and a legal cut
`u ≤ min(M₀,M₁)`, the parent threshold-count is dominated by the emitted block charge plus the reduced
chain's threshold-count: `minAdm M ≤ peelCharge M u + minAdm (redChain u M)`. Immediate from the banked
value-fold `LayerSplit_value_eq_minAdm` (the RHS is a member of the `inf'` equal to `minAdm M`). This is
the certificate's `carrierThreshold_mono` (threshold monotonicity, `0/171`). -/
theorem minAdm_le_peelCharge_add_redChain (M : Fin (L + 1 + 1 + 1) → ℕ) (u : ℕ)
    (hu : u ≤ min (M 0) (M 1)) :
    minAdm M ≤ peelCharge M u + minAdm (redChain u M) := by
  rw [← LayerSplit_value_eq_minAdm M]
  exact Finset.inf'_le (fun t => (M 0 - t) * (M 1 - t) + minAdm (redChain t M))
    (by rw [Finset.mem_range]; omega)

/-- **The decorated peel-charge soundness (the `ℝ` threshold form).** The exponent-shift version: half
the parent threshold minus half the peel charge is `≤` half the reduced-chain threshold,

    (minAdm M : ℝ)/2 − (peelCharge M u : ℝ)/2  ≤  (minAdm (redChain u M) : ℝ)/2.

So a coupling exponent `c' < ½·minAdm M` shifted by `½·peelCharge` stays `< ½·minAdm(redChain u M)` — the
subordination the decorated recursion hands to the strong IH at the reduced chain. Cast of the `ℕ`
inequality. -/
theorem half_minAdm_sub_half_peelCharge_le (M : Fin (L + 1 + 1 + 1) → ℕ) (u : ℕ)
    (hu : u ≤ min (M 0) (M 1)) :
    (minAdm M : ℝ) / 2 - (peelCharge M u : ℝ) / 2 ≤ (minAdm (redChain u M) : ℝ) / 2 := by
  have h := minAdm_le_peelCharge_add_redChain M u hu
  have hcast : (minAdm M : ℝ) ≤ (peelCharge M u : ℝ) + (minAdm (redChain u M) : ℝ) := by
    exact_mod_cast h
  linarith

/-- **Non-vacuity — the binding cut achieves equality.** There is a legal cut `u ≤ min(M₀,M₁)` at which
the soundness inequality is an EQUALITY: `minAdm M = peelCharge M u + minAdm (redChain u M)`. This is the
achiever of the `inf'` `LayerSplit_value_eq_minAdm` — the binding branch the decorated recursion follows,
witnessing that the threshold-monotone peel is tight (not a slack over-estimate). -/
theorem exists_binding_cut (M : Fin (L + 1 + 1 + 1) → ℕ) :
    ∃ u, u ≤ min (M 0) (M 1) ∧ minAdm M = peelCharge M u + minAdm (redChain u M) := by
  obtain ⟨u, hu, heq⟩ := Finset.exists_mem_eq_inf' (s := Finset.range (min (M 0) (M 1) + 1))
    (by simp) (fun t => (M 0 - t) * (M 1 - t) + minAdm (redChain t M))
  rw [Finset.mem_range] at hu
  refine ⟨u, by omega, ?_⟩
  rw [← LayerSplit_value_eq_minAdm M, heq]
  rfl

end DLNFibre.DLN.RLCT
