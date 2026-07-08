import DLNFibre.DLN.RLCT.Validate.RouteMSJDecorated

/-!
# `DLNFibre.DLN.RLCT.Validate.RouteMSJDecoratedMeas` — measurability of the decorated loss / integrand

**Thread `genm-sjassembly`, R1-UPPER.** The measurability primitives the decorated box-integral factoring
(Tonelli, `lintegral_const_mul`, the radial-attach exponent shift) consumes. They are unblocked by the
`SJDecoration.residualMeas` field (`RouteMSJDecorated`): the carrier residual is measurable in the deeper
parameter `z`, and the exceptional-monomial prefix is a polynomial (continuous) in the exceptional
coordinates `u`, so the decorated loss `decLoss` is measurable per-`u` in `z` and JOINTLY in `(z, u)`.

## What lands here

* **`continuous_genMonomial`** — the generator monomial `∏_ℓ |u_ℓ|^{e i ℓ}` is continuous in `u`.
* **`SJDecoration.measurable_decLoss`** — `z ↦ decLoss u z` is measurable (each `u` fixed): the carrier
  loss `∑ᵢ (genMonomial · residual)²` is a finite sum of squares of (constant · residualMeas).
* **`SJDecoration.measurable_decLoss_uncurry`** — `(z, u) ↦ decLoss u z` is JOINTLY measurable: the
  monomial factor rides `measurable_snd`, the residual factor rides `measurable_fst` — the form Tonelli
  needs (`Z` carries only a `MeasurableSpace`, no topology, so the joint proof cannot use continuity on
  the product; it splits the two coordinates by projection).
* **`SJDecoration.measurable_integrand`** — the full decorated integrand
  `ofReal((∏_ℓ |u_ℓ|^{jac_ℓ}) · decLoss(u,z)^{−c'})` is jointly measurable in `(z, u)`.

S2-FREE: pure measurability plumbing over the banked residual-measurability field. Axiom-clean
`[propext, Classical.choice, Quot.sound]`.
-/

namespace DLNFibre.DLN.RLCT

open MeasureTheory Set
open scoped ENNReal BigOperators

variable {L : ℕ}

/-- **The generator monomial is continuous in the exceptional coordinates.** `u ↦ ∏_ℓ |u_ℓ|^{e i ℓ}`
(natural powers of `|u_ℓ|`) is continuous. -/
theorem continuous_genMonomial {ι : Type*} {d : ℕ} (e : SJSupport ι d) (i : ι) :
    Continuous (fun u : Fin d → ℝ => genMonomial e i u) := by
  unfold genMonomial; fun_prop

/-- **The accumulated-Jacobian monomial is continuous.** `u ↦ ∏_ℓ |u_ℓ|^{jac ℓ}` is continuous. -/
theorem continuous_jacMonomial {d : ℕ} (jac : Fin d → ℕ) :
    Continuous (fun u : Fin d → ℝ => ∏ ℓ, |u ℓ| ^ (jac ℓ)) := by
  fun_prop

/-- **The decorated loss is measurable in the deeper parameter (each exceptional coordinate fixed).**
`z ↦ decLoss u z` is measurable: `decLoss u z = ∑ᵢ (genMonomial supp i u · residual (ctx z) i)²`, a
finite sum of squares of `(constant-in-z) · (residualMeas i)`. -/
theorem SJDecoration.measurable_decLoss {M : Fin (L + 1) → ℕ} (D : SJDecoration M)
    (u : Fin D.d → ℝ) :
    letI := D.mZ
    Measurable (fun z : D.Z => D.decLoss u z) := by
  letI := D.mZ; letI := D.fν; letI := D.fι
  unfold SJDecoration.decLoss SJLinGenState.loss SJLinGenState.gen
  refine Finset.measurable_sum Finset.univ (fun i _ => ?_)
  exact ((D.residualMeas i).const_mul (genMonomial D.carrier.supp i u)).pow_const 2

/-- **The decorated loss is JOINTLY measurable in `(z, u)`.** `(z, u) ↦ decLoss u z` is measurable: the
monomial factor `genMonomial supp i u` is continuous in `u` (rides `measurable_snd`), the residual factor
`residual (ctx z) i` is measurable in `z` (rides `measurable_fst`). The form Tonelli / Fubini needs; the
joint proof cannot use continuity on the product `Z × (Fin d → ℝ)` (the spectator space `Z` carries no
topology), so it factors by projection. -/
theorem SJDecoration.measurable_decLoss_uncurry {M : Fin (L + 1) → ℕ} (D : SJDecoration M) :
    letI := D.mZ
    Measurable (fun p : D.Z × (Fin D.d → ℝ) => D.decLoss p.2 p.1) := by
  letI := D.mZ; letI := D.fν; letI := D.fι
  unfold SJDecoration.decLoss SJLinGenState.loss SJLinGenState.gen
  refine Finset.measurable_sum Finset.univ (fun i _ => ?_)
  refine Measurable.pow_const (Measurable.mul ?_ ?_) 2
  · exact ((continuous_genMonomial D.carrier.supp i).measurable).comp measurable_snd
  · exact (D.residualMeas i).comp measurable_fst

/-- **The full decorated integrand is jointly measurable in `(z, u)`.** The integrand
`ofReal((∏_ℓ |u_ℓ|^{jac_ℓ}) · decLoss(u,z)^{−c'})` of `SJDecoration.integral` is measurable: the
Jacobian monomial is continuous in `u`, the loss power `decLoss^{−c'}` rides `measurable_decLoss_uncurry`
through the (measurable) fixed-exponent `rpow`, and `ofReal` preserves measurability. -/
theorem SJDecoration.measurable_integrand {M : Fin (L + 1) → ℕ} (D : SJDecoration M) (c' : ℝ) :
    letI := D.mZ
    Measurable (fun p : D.Z × (Fin D.d → ℝ) =>
      ENNReal.ofReal ((∏ ℓ, |p.2 ℓ| ^ (D.jac ℓ)) * (D.decLoss p.2 p.1) ^ (-c'))) := by
  letI := D.mZ
  apply ENNReal.measurable_ofReal.comp
  refine Measurable.mul ?_ ?_
  · exact ((continuous_jacMonomial D.jac).measurable).comp measurable_snd
  · exact (by fun_prop : Measurable (fun t : ℝ => t ^ (-c'))).comp D.measurable_decLoss_uncurry

end DLNFibre.DLN.RLCT
