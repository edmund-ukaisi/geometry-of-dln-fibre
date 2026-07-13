import DLNFibre.DLN.RLCT.Validate.RouteMSJPivotDom

set_option linter.style.longLine false

/-!
# `DLNFibre.DLN.RLCT.Validate.RouteMSJPivotFin` — GLUE-2 (b): the pivot→`decLoss` finiteness

**Thread `genm-sj5` (aoyagi-full Stage 2), the analytic CRUX of the head-split (GLUE-2).**
`pivotDom_finiteness_impl` reproduces the `RouteMSJPivotDom.pivotDom_finiteness` stub signature VERBATIM;
the controller wires the stub to it.

The genuine analytic content: `pivotDomRHS < ⊤ → pivotDomLHS < ⊤`, keeping the freed-loss corank
(load-bearing — the `ab/2` shift regularizes the pivot's zero-locus). Mechanism (cert
`s1-Chle-angular-integrability-cert` §8 #1): S3 (`shell_corankOffSector_le_unif`) integrates out the corank
(`A_cor`, `Γ`) at fixed pivot energy `w`, producing the `−ab/2` exponent shift `c' ↦ c'' = c' − ab/2`; the
residual pivot box-integral `∫ frobSq(P·Q_p + B₁₂·Q_b)^{−c''}` is finite via the codim-`u·ρ` linear-image
argument (D-B `RouteMSJRankRCodim.lintegral_cube_frobSq_neg_of_finrank_range`), in the regime `c'' < u·ρ/2`
extracted from `hRHS` (the comparator diverges above `minAdm(redChain u M)/2 ≤ u·ρ/2` by `hpiv`). Design:
`s1-Chle-angular-integrability-cert`.
-/

namespace DLNFibre.DLN.RLCT

open Matrix MeasureTheory
open scoped ENNReal BigOperators

variable {L : ℕ}

/-- **GLUE-2 finiteness (the isolated crux).** Verbatim statement of `RouteMSJPivotDom.pivotDom_finiteness`;
the controller wires the stub to it. -/
theorem pivotDom_finiteness_impl (M : Fin (L + 1 + 1 + 1) → ℕ) (u : ℕ)
    {ε : ℝ} (hε : 0 < ε) (c' : ℝ) (hnd : ∀ i, 1 ≤ M i)
    (hpiv : minAdm (redChain u M) ≤ u * tailMinWidth M) {m : ℕ}
    (hcvg : (M 0 - u) + (M 1 - u) ≤ m) (hmM : m ≤ dropHead (redChain u M) 0)
    {ε' : ℝ} (hε' : 0 < ε')
    (Zf : Params (redChain u M)
        → Matrix (Fin (dropHead (redChain u M) 0))
            (Fin (dropHead (redChain u M) (Fin.last L))) ℝ)
    (hZfMeas : Measurable Zf)
    (U_sf : Params (redChain u M) → Matrix (Fin (dropHead (redChain u M) 0)) (Fin m) ℝ)
    (hUs : ∀ z, (U_sf z)ᵀ * U_sf z = 1)
    (hrank : ∀ z, m ≤ (Zf z).rank)
    (hfloor : ∀ z, (Zf z * (Zf z)ᵀ - (ε' ^ 2) • (U_sf z * (U_sf z)ᵀ)).PosSemidef)
    (hRHS : pivotDomRHS M u c' Zf < ⊤) :
    pivotDomLHS M u c' Zf < ⊤ := by
  sorry

end DLNFibre.DLN.RLCT
