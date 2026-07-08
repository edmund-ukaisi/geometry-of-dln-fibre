import DLNFibre.DLN.RLCT.Validate.RouteMSJDecoratedMeas

/-!
# `DLNFibre.DLN.RLCT.Validate.RouteMSJDecoratedRadial` — the radial-attach integral factoring

**Thread `genm-sjassembly`, R1-UPPER.** The integral-level realization of the decorated Case-2 radial
step: attaching a fresh fully-shared exceptional divisor `u₀` (`SJDecoration.radialAttach`, `RouteMSJDecorated`)
FACTORS the decorated box-integral into a 1-D radial factor times the parent integral. This is the
integral-level companion of the pointwise `radialAttach_decLoss` (`decLoss (u₀ ::: u) z = u₀²·decLoss u z`)
and the combinatorial `carrierThreshold_shift` — the exponent shift `c' ↦ c' − ½·(j₀+1)` acting through
the 1-D Jacobian factor, unblocked by the `residualMeas` field (via `RouteMSJDecoratedMeas`).

## What lands here

* **`radialFactor j₀ c' = ∫⁻_{u₀∈[0,1]} |u₀|^{j₀}·(u₀²)^{−c'}`** — the 1-D radial Jacobian factor of one
  Case-2 divisor with accumulated Jacobian exponent `j₀`. Finite iff `j₀ − 2c' > −1`, i.e. `c' < (j₀+1)/2`
  (the per-divisor Morse threshold; not proved here — this module is the EQUALITY).

* **`SJDecoration.radialAttach_integral`** — the factoring, UNCONDITIONAL in `c'`:

      (radialAttach D j₀).integral c'  =  radialFactor j₀ c' · D.integral c'.

  Proof: split coordinate `0` off `unitBox (d+1)` (`lintegral_unitBox_succ_cons`, the `piFinSuccAbove`
  Tonelli step); the radial-attach integrand factors pointwise
  (`radialAttach_decLoss` + `Fin.prod_univ_succ` + `Real.mul_rpow` on `(u₀²·decLoss)^{−c'}`) into
  `ofReal(|u₀|^{j₀}·(u₀²)^{−c'}) · ofReal(parent integrand)`; the 1-D factor pulls out of the `u`-integral
  (`lintegral_const_mul`, `measurable_integrand` per-`z` slice), out of the `u₀`-integral
  (`lintegral_mul_const`), and out of the `z`-integral (`lintegral_const_mul`, `lintegral_prod_right'`).

## What this is, and is NOT (fidelity)

The single-divisor factoring the decorated recursion's Case-2 RADIAL step consumes. The equality is
unconditional (holds even where both sides are `⊤`). It does NOT: (i) supply the finiteness of
`radialFactor` (the `c' < (j₀+1)/2` threshold, a separate 1-D monomial-integrability fact); (ii) perform
the ANISOTROPIC-corank descent (the spherical blow-up `lintegral_eq_polar` exposing the `r^{pq−1}`
Jacobian on the pivot chart — that is the genuine crux, a different coordinate structure); (iii) discharge
the recursion. It is the reusable radial-attach factoring, validating the `residualMeas` measurability
field end-to-end.

S2-FREE: pure measure-preserving Tonelli + `rpow` algebra over the banked measurability primitives.
Axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/

namespace DLNFibre.DLN.RLCT

open MeasureTheory Set
open scoped ENNReal BigOperators

variable {L : ℕ}

/-- **The 1-D radial Jacobian factor** of one Case-2 divisor at accumulated exponent `j₀`, exponent `c'`:
`∫⁻_{u₀∈[0,1]} |u₀|^{j₀}·(u₀²)^{−c'} du₀`. (Finite iff `c' < (j₀+1)/2`; that threshold is not proved here.) -/
noncomputable def radialFactor (j₀ : ℕ) (c' : ℝ) : ℝ≥0∞ :=
  ∫⁻ u₀ in Set.Icc (0 : ℝ) 1, ENNReal.ofReal (|u₀| ^ j₀ * (u₀ ^ 2) ^ (-c'))

/-- **The radial-attach integral factoring (unconditional in `c'`).** Attaching a fresh fully-shared
Case-2 divisor factors the decorated box-integral into the 1-D radial Jacobian factor times the parent:
`(radialAttach D j₀).integral c' = radialFactor j₀ c' · D.integral c'`. The integral-level realization of
the pointwise `radialAttach_decLoss` and the combinatorial `carrierThreshold_shift`. -/
theorem SJDecoration.radialAttach_integral {M : Fin (L + 1) → ℕ} (D : SJDecoration M) (j₀ : ℕ)
    (c' : ℝ) :
    (D.radialAttach j₀).integral c' = radialFactor j₀ c' * D.integral c' := by
  letI := D.mZ
  have hA : Measurable (fun u₀ : ℝ => ENNReal.ofReal (|u₀| ^ j₀ * (u₀ ^ 2) ^ (-c'))) := by fun_prop
  have hBz : ∀ z : D.Z, Measurable (fun u : Fin D.d → ℝ =>
      ENNReal.ofReal ((∏ ℓ, |u ℓ| ^ (D.jac ℓ)) * (D.decLoss u z) ^ (-c'))) := by
    intro z
    apply ENNReal.measurable_ofReal.comp
    refine Measurable.mul ((continuous_jacMonomial D.jac).measurable) ?_
    exact (by fun_prop : Measurable (fun t : ℝ => t ^ (-c'))).comp
      (D.continuous_decLoss_right z).measurable
  have hID : Measurable (fun z : D.Z => ∫⁻ u in unitBox D.d,
      ENNReal.ofReal ((∏ ℓ, |u ℓ| ^ (D.jac ℓ)) * (D.decLoss u z) ^ (-c'))) :=
    (D.measurable_integrand c').lintegral_prod_right'
  -- Per deeper-parameter `z`: the inner exceptional-coordinate integral factors.
  have key : ∀ z : D.Z,
      (∫⁻ v in unitBox (D.d + 1), ENNReal.ofReal
        ((∏ ℓ, |v ℓ| ^ ((Fin.cons j₀ D.jac : Fin (D.d + 1) → ℕ) ℓ))
          * ((D.radialAttach j₀).decLoss v z) ^ (-c')))
      = radialFactor j₀ c'
        * ∫⁻ u in unitBox D.d, ENNReal.ofReal ((∏ ℓ, |u ℓ| ^ (D.jac ℓ)) * (D.decLoss u z) ^ (-c')) := by
    intro z
    have hFz : Measurable (fun v : Fin (D.d + 1) → ℝ => ENNReal.ofReal
        ((∏ ℓ, |v ℓ| ^ ((Fin.cons j₀ D.jac : Fin (D.d + 1) → ℕ) ℓ))
          * ((D.radialAttach j₀).decLoss v z) ^ (-c'))) := by
      apply ENNReal.measurable_ofReal.comp
      refine Measurable.mul (continuous_jacMonomial (Fin.cons j₀ D.jac)).measurable ?_
      exact (by fun_prop : Measurable (fun t : ℝ => t ^ (-c'))).comp
        ((D.radialAttach j₀).continuous_decLoss_right z).measurable
    rw [lintegral_unitBox_succ_cons _ hFz]
    -- The radial-attach integrand factors pointwise.
    have hpt : ∀ (u₀ : ℝ) (u : Fin D.d → ℝ),
        ENNReal.ofReal ((∏ ℓ, |(Fin.cons u₀ u) ℓ| ^ ((Fin.cons j₀ D.jac : Fin (D.d + 1) → ℕ) ℓ))
          * ((D.radialAttach j₀).decLoss (Fin.cons u₀ u) z) ^ (-c'))
        = ENNReal.ofReal (|u₀| ^ j₀ * (u₀ ^ 2) ^ (-c'))
          * ENNReal.ofReal ((∏ ℓ, |u ℓ| ^ (D.jac ℓ)) * (D.decLoss u z) ^ (-c')) := by
      intro u₀ u
      rw [radialAttach_decLoss D j₀ u₀ u z, Fin.prod_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ]
      rw [Real.mul_rpow (sq_nonneg u₀) (D.decLoss_nonneg u z),
        ← ENNReal.ofReal_mul (by positivity)]
      congr 1; ring
    have hinner : ∀ u₀ : ℝ,
        (∫⁻ u in unitBox D.d, ENNReal.ofReal
          ((∏ ℓ, |(Fin.cons u₀ u) ℓ| ^ ((Fin.cons j₀ D.jac : Fin (D.d + 1) → ℕ) ℓ))
            * ((D.radialAttach j₀).decLoss (Fin.cons u₀ u) z) ^ (-c')))
        = ENNReal.ofReal (|u₀| ^ j₀ * (u₀ ^ 2) ^ (-c'))
          * ∫⁻ u in unitBox D.d, ENNReal.ofReal ((∏ ℓ, |u ℓ| ^ (D.jac ℓ)) * (D.decLoss u z) ^ (-c')) := by
      intro u₀
      rw [lintegral_congr (fun u => hpt u₀ u), lintegral_const_mul _ (hBz z)]
    trans (∫⁻ u₀ in Set.Icc (0 : ℝ) 1, ENNReal.ofReal (|u₀| ^ j₀ * (u₀ ^ 2) ^ (-c'))
        * ∫⁻ u in unitBox D.d, ENNReal.ofReal ((∏ ℓ, |u ℓ| ^ (D.jac ℓ)) * (D.decLoss u z) ^ (-c')))
    · exact lintegral_congr hinner
    · rw [lintegral_mul_const _ hA]; rfl
  -- Assemble over the deeper parameter.
  change (∫⁻ z in D.dom, ∫⁻ v in unitBox (D.d + 1), ENNReal.ofReal
      ((∏ ℓ, |v ℓ| ^ ((Fin.cons j₀ D.jac : Fin (D.d + 1) → ℕ) ℓ))
        * ((D.radialAttach j₀).decLoss v z) ^ (-c')))
    = radialFactor j₀ c' * ∫⁻ z in D.dom, ∫⁻ u in unitBox D.d,
        ENNReal.ofReal ((∏ ℓ, |u ℓ| ^ (D.jac ℓ)) * (D.decLoss u z) ^ (-c'))
  trans (∫⁻ z in D.dom, radialFactor j₀ c'
      * ∫⁻ u in unitBox D.d, ENNReal.ofReal ((∏ ℓ, |u ℓ| ^ (D.jac ℓ)) * (D.decLoss u z) ^ (-c')))
  · exact lintegral_congr key
  · rw [lintegral_const_mul _ hID]

end DLNFibre.DLN.RLCT
