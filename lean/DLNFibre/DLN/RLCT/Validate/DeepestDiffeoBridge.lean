import DLNFibre.DLN.RLCT.Validate.DeepestRegAbsorbIFT
import DLNFibre.DLN.RLCT.Validate.GeneralR1Recursion

/-!
# `DLNFibre.DLN.RLCT.Validate.DeepestDiffeoBridge` — the diffeo-bridge reduction

The L2 producer's residual #2 (the `hstep2` goal in `DeepestGaugeConstruction`) is
`rlctAtOn Φscore wstar = rlctAtOn Φcore wstar`, with `Φscore` carrying the matrix-Schur `Score` and
`Φcore` carrying the absorbed-core `deepestCoreF (coreAbsorb (split ·)).2.1`. The two functions share
the reg term verbatim; they differ only in the core/Score summand.

This module records the CLEAN REDUCTION of that goal to two inputs:
* a reparametrization `Psi` of the flat coordinates that is a **local diffeo at `wstar`** (smooth,
  invertible strict derivative `e`, fixing `wstar`);
* the **eventual composition identity** `Φcore ∘ Psi =ᶠ[𝓝 wstar] Φscore`.

Given those two, `rlctAtOn_diffeo_bridge_of` discharges `hstep2` by germ-locality
(`rlctAtOn_germ_local`) + RLCT-invariance under a local diffeo (`rlctAtOn_comp_localDiffeo`). The proof
is sorry-free; it isolates the two genuine geometric inputs (the joint `(T1,Y1)` Ψ closed form + its
cutoff-smooth global extension, and the LDU composition identity `coreΦ ∘ Ψ = Score`) as named
hypotheses, mirroring the conditional-bridge pattern of `deepest_regular_core_normal_form_of`.

The `Psi` the consumer supplies is built on `DeepestSplitSmooth` (the `split` smooth-affine chart):
`Psi = split⁻¹ ∘ Ψ_split ∘ split` with `Ψ_split` the joint `(T1, Y1)` cutoff action.
-/

open MeasureTheory
open scoped ENNReal BigOperators Topology
namespace DLNFibre.DLN.RLCT

variable {L : ℕ}

/-- **The diffeo-bridge reduction.** If `Psi` is a local diffeo at `wstar` (smooth `ContDiff ⊤`,
strict derivative the CLE `e`, fixing `wstar`) and `Φcore ∘ Psi` eventually equals `Φscore` near
`wstar`, then `rlctAtOn Φscore wstar = rlctAtOn Φcore wstar`. Proof: germ-locality replaces `Φscore`
by `Φcore ∘ Psi`, and `rlctAtOn_comp_localDiffeo` strips `Psi`. This is the exact shape `hstep2`
consumes; the consumer supplies `Psi` (the joint `(T1,Y1)` cutoff action through the `split` chart)
and the composition identity (the LDU `Rcore = S0·(1−K)·S1` + the absorbed `S1' = (1−K)·S1`). -/
theorem rlctAtOn_diffeo_bridge_of {M : Type*}
    [NormedAddCommGroup M] [NormedSpace ℝ M] [MeasureSpace M] [BorelSpace M]
    [FiniteDimensional ℝ M] [(volume : Measure M).IsAddHaarMeasure]
    (Φscore Φcore : M → ℝ) (wstar : M) (Psi : M → M) (e : M ≃L[ℝ] M)
    (hcontdiff : ContDiff ℝ (⊤ : ℕ∞) Psi)
    (hderiv : HasStrictFDerivAt Psi (e : M →L[ℝ] M) wstar)
    (hfix : Psi wstar = wstar)
    (hcomp : (fun x => Φcore (Psi x)) =ᶠ[nhds wstar] Φscore) :
    rlctAtOn Φscore wstar = rlctAtOn Φcore wstar := by
  rw [← rlctAtOn_germ_local (fun x => Φcore (Psi x)) Φscore wstar hcomp]
  exact rlctAtOn_comp_localDiffeo Φcore wstar Psi e hcontdiff hderiv hfix

end DLNFibre.DLN.RLCT
