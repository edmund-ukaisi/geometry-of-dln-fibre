import DLNFibre.Core.Aoyagi.SandwichCover
import DLNFibre.Core.Aoyagi.DomainSandwich

/-!
# `Core.Aoyagi.SandwichCoverValue` — the STEP 4→5 joint (wire conclusion → ½·divisorMin)

The value-normalised form of the merged V-lower wire. `rlctAt_ge_iInf_threshold_of_sandwich_cover`
concludes `⨅_c monomialThreshold_c ≤ rlctAt`; under the DLN normal-crossing fact that every binding
divisor has unit multiplicity (`hunit_mult`), the STEP 5 conversion
`DomainSandwich.inf'_monomialThreshold_eq_half_divisorMin` turns the boxed `⨅ monomialThreshold` into
`½·divisorMin` (`divisorMin = ⨅_c ⨅_{binding} (jac_d+1)`). So the wire delivers
`½·divisorMin ≤ rlctAt`, and a `divisorMin = 8` (Object D / `minAdm ![3,3,4] = 8`) reads off the
`(3,3,4)` headline `4 ≤ rlctAt`.

This module verifies that the STEP 5 conversion consumes the wire's EXACT conclusion shape (the joint
the controller composes at integration). It carries the wire's conclusion as the hypothesis `hwire`
(rather than restating the wire's 28 per-chart inputs) — the controller supplies `hwire` from the
wire applied to the concrete `(3,3,4)` chart family + the born-α `hsandwich`
(`DomainSandwich.sandwich_on_domain_of_survivor`) + hjac + hbdd + the SHEARED hcover (the separate
cover seat).
-/

open MeasureTheory Set Filter Topology RLCT

namespace DLNFibre.Core.Aoyagi

variable {D Mn : ℕ}

/-- **STEP 4→5 joint: the wire's `⨅ monomialThreshold ≤ rlctAt` normalises to `½·divisorMin ≤ rlctAt`.**
Under unit divisor multiplicity `hunit_mult` (each binding exponent `= 1`), the boxed threshold
`⨅_c monomialThreshold (bexp c (k₀ c)) (jac c)` equals `(⨅_c ⨅_{binding} (jac_d+1))/2 = ½·divisorMin`
(`inf'_monomialThreshold_eq_half_divisorMin`), so the wire's lower bound becomes
`½·divisorMin ≤ rlctAt (∑Fᵢ²) x₀`. A downstream `divisorMin = 8` gives `4 ≤ rlctAt`. -/
theorem rlctAt_ge_half_divisorMin_of_iInf_threshold
    {F : Fin Mn → (Fin D → ℝ) → ℝ} {x₀ : Fin D → ℝ} {numCharts : ℕ}
    (hne : (Finset.univ : Finset (Fin numCharts)).Nonempty)
    (bexp : Fin numCharts → Fin Mn → Fin D → ℕ) (k₀ : Fin numCharts → Fin Mn)
    (jac : Fin numCharts → Fin D → ℕ)
    (hbind : ∀ c, (bindingAxes (bexp c (k₀ c))).Nonempty)
    (hunit_mult : ∀ c, ∀ d ∈ bindingAxes (bexp c (k₀ c)), bexp c (k₀ c) d = 1)
    (hwire : Finset.univ.inf' hne (fun c ↦ monomialThreshold (bexp c (k₀ c)) (jac c) (hbind c))
        ≤ rlctAt (sumSqFam F) x₀) :
    (Finset.univ.inf' hne
        (fun c ↦ (bindingAxes (bexp c (k₀ c))).inf' (hbind c) (fun d ↦ (jac c d + 1 : ℝ)))) / 2
      ≤ rlctAt (sumSqFam F) x₀ := by
  rwa [inf'_monomialThreshold_eq_half_divisorMin Finset.univ hne
    (fun c ↦ bexp c (k₀ c)) jac hbind hunit_mult] at hwire

/-- **The `(3,3,4)` headline value read-off**: once the joint gives `½·divisorMin ≤ rlctAt`, a
`divisorMin = 8` yields `4 ≤ rlctAt`. The `divisorMin = 8` is Object D (`minAdm ![3,3,4] = 8`),
supplied downstream. Pure arithmetic (no new content) — the last step of the payoff read-off. -/
theorem rlctAt_ge_four_of_half_divisorMin
    {F : Fin Mn → (Fin D → ℝ) → ℝ} {x₀ : Fin D → ℝ} {v : ℝ}
    (hdiv : v = 8) (h : v / 2 ≤ rlctAt (sumSqFam F) x₀) :
    (4 : ℝ) ≤ rlctAt (sumSqFam F) x₀ := by
  rw [hdiv] at h; norm_num at h; exact h

-- Forced axiom gate: the STEP 4→5 joint rests only on `[propext, Classical.choice, Quot.sound]`.
#assert_banked_clean_batch [rlctAt_ge_half_divisorMin_of_iInf_threshold,
  rlctAt_ge_four_of_half_divisorMin]

end DLNFibre.Core.Aoyagi
