import DLNFibre.DLN.RLCT.Validate.RouteMSJHeadSplitDom

set_option linter.style.longLine false

/-!
# `DLNFibre.DLN.RLCT.Validate.RouteMSJPivotDom` — GLUE-2: the coupled pivot→`decLoss` domination

**Thread `genm-sj5` (aoyagi-full Stage 2), the analytic CRUX of the head-split (GLUE-2).**
`headSplit_pivotDom_impl` reproduces the `RouteMSJHeadSplitDom.headSplit_pivotDom` stub signature
VERBATIM (referencing the imported `hsQ`); the controller wires the stub to it.

## Architecture (locked with the controller, 2026-07-13): finiteness / ratio

The RHS is EXISTENTIAL in `C_hle`, and `C_hle` may depend on everything held fixed (`M, u, c', Zf, …`) —
just not on the integration variables. So `∃ C_hle < ⊤, LHS ≤ C_hle · RHS` is a **finiteness
comparison**, not a tight domination:
* `RHS = ⊤` → `C_hle := 1` (trivial);
* `RHS < ⊤` (and `RHS ≠ 0`) → `C_hle := LHS / RHS` works iff `LHS < ⊤` (`ENNReal.div_mul_cancel`).

So the genuine content is `pivotDom_finiteness : RHS < ⊤ → LHS < ⊤`, isolated as the ONE crux sorry.

**Soundness note (verified numerically, 2026-07-13).** The finiteness `LHS < ⊤` genuinely needs the
freed-loss's CORANK term kept: dropping it (`freedSchurLoss ≥ pivot`) over-estimates `LHS` to `⊤` in the
regime `c' ∈ (u·ρ/2, (minAdm(M)/2))` — the pure-pivot `∫_W frobSq(W·Q̂)^(-c')` has D-B threshold `u·ρ/2`,
but the true `LHS` (and `RHS`) converge to `minAdm(M)/2 = minAdm(redChain u M)/2 + ab/2`, because the
corank's `ab/2` shift (S3) regularizes the pivot's zero-locus (witness `(3,3,3)`, `u=2`: pure-pivot
threshold `3`, true threshold `3.5`; `hpiv` gives only `u·ρ/2 ≥ minAdm(redChain u M)/2`, short by exactly
the `ab/2`). Hence `pivotDom_finiteness` keeps the corank and follows the cert mechanism: D-A P-radial
blow-up of the pivot → `commonDivisor²·frobSq(Q_p) = decLoss` after the angular/`B₁₂` integration (the
non-pointwise cross-term drop) → S3 (`shell_corankOffSector_le_unif`) on the corank, det-Gram convergence
via `hcvg`. It is commissioned as a dedicated tide (design: `s1-Chle-angular-integrability-cert`).
-/

namespace DLNFibre.DLN.RLCT

open Matrix MeasureTheory
open scoped ENNReal BigOperators

variable {L : ℕ}

/-- **The GLUE-2 LHS integral** — the freed Schur-loss spine integrand at `Q = hsQ` (pivot rows
`prod(redChain u M) z`, corank rows `A_cor·Zf z`), integrated over `(z, A_cor, x=(P,B₁₂,C), Γ)`. This is
the exact left-hand side of `RouteMSJHeadSplitDom.headSplit_pivotDom`. -/
noncomputable def pivotDomLHS (M : Fin (L + 1 + 1 + 1) → ℕ) (u : ℕ) (ε : ℝ) (c' : ℝ)
    (Zf : Params (redChain u M)
        → Matrix (Fin (dropHead (redChain u M) 0))
            (Fin (dropHead (redChain u M) (Fin.last L))) ℝ) : ℝ≥0∞ :=
  ∫⁻ z in paramsBoxM (redChain u M) 1,
    ∫⁻ A_cor in matBox (M 1 - u) (dropHead (redChain u M) 0) 1 ∩ pivotShell M u ε Zf z,
      ∫⁻ x in outerDom u (M 0 - u) (M 1 - u) 1,
        ∫⁻ Γ in {Γ : Fin (M 0 - u) → Fin (M 1 - u) → ℝ |
            Γ + schurShift x ∈ genBox (Fin (M 0 - u)) (Fin (M 1 - u)) 1},
          ENNReal.ofReal ((freedSchurLoss x Γ (hsQ M u Zf z A_cor)) ^ (-c'))

/-- **The GLUE-2 RHS integrand** — `deeperFlagCoreIntegrand` at the clean comparator data `k = ![1]`,
`jc = ![minAdm(redChain u M) − 1]`, `Ccrossf = 0`, `sΓf = genBox`. Abbreviation for readability. -/
noncomputable def pivotDomRHS (M : Fin (L + 1 + 1 + 1) → ℕ) (u : ℕ) (c' : ℝ)
    (Zf : Params (redChain u M)
        → Matrix (Fin (dropHead (redChain u M) 0))
            (Fin (dropHead (redChain u M) (Fin.last L))) ℝ) : ℝ≥0∞ :=
  deeperFlagCoreIntegrand M u (![1] : Fin 1 → ℕ)
    (![minAdm (redChain u M) - 1] : Fin 1 → ℕ) Zf
    (fun _ => 0) (fun _ => genBox (Fin (M 0 - u)) (Fin (M 1 - u)) 1) c'

/-- **The GLUE-2 finiteness (the genuine analytic content — the ISOLATED CRUX).** Whenever the
comparator-core RHS is finite, the freed Schur-loss spine LHS is finite. Mechanism (cert
`s1-Chle-angular-integrability-cert` + `s1-spine-headsplit-cert` §A): keeping the corank (load-bearing —
see the soundness note in the module header), the D-A P-radial blow-up of the pivot block `W = (P|B₁₂)`
factors the pivot energy to `commonDivisor(v)²·frobSq(Q_p) = decLoss` after the angular/`B₁₂` integration
(the non-pointwise cross-term drop), and S3 (`shell_corankOffSector_le_unif`) integrates the corank with
the `ab/2` shift; finiteness is the codim-`u·ρ` singularity (D-B
`lintegral_cube_frobSq_neg_of_finrank_range`) with the det-Gram outer convergence (`hcvg`, `a < m − b + 1`),
threshold-covered by `hpiv`. Commissioned as a dedicated fresh tide. -/
theorem pivotDom_finiteness (M : Fin (L + 1 + 1 + 1) → ℕ) (u : ℕ)
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
    pivotDomLHS M u ε c' Zf < ⊤ := by
  sorry

/-- **The GLUE-2 RHS is nonzero (in the operative `u ≥ 1` cut).** `decLoss =
commonDivisor(v)²·frobSq(prod(redChain u M) z)` is `> 0` a.e. on `paramsBoxM × unitBox` (the deep-tail
product is a nonzero polynomial ⟹ null zero set; `v 0 ≠ 0` a.e.), so the RHS integrand `|v 0|^{minAdm-1}·
∫∫(decLoss + …)^(-c')` is positive on a positive-measure set. Uses the banked
`deeperFlagCore_decLoss_pos_ae` (at `t = u`, `j = 0`). -/
theorem pivotDom_RHS_ne_zero (M : Fin (L + 1 + 1 + 1) → ℕ) (u : ℕ)
    (hu : 1 ≤ u) (c' : ℝ) (hnd : ∀ i, 1 ≤ M i)
    (Zf : Params (redChain u M)
        → Matrix (Fin (dropHead (redChain u M) 0))
            (Fin (dropHead (redChain u M) (Fin.last L))) ℝ)
    (hZfMeas : Measurable Zf) :
    pivotDomRHS M u c' Zf ≠ 0 := by
  sorry

/-- **The degenerate `u = 0` edge.** With a `0`-width pivot the front block vanishes
(`freedSchurLoss = frobSq(Γ·Q_b)`, the `(P,B₁₂,C)`-integral is over a singleton), and `hpiv` forces
`minAdm(redChain 0 M) = 0` so the RHS Jacobian monomial is `|v 0|^0 = 1`; a Tonelli factorisation of the
`v`-integral gives `LHS = RHS`. NOT the analytic crux (no pivot energy). -/
theorem pivotDom_uzero (M : Fin (L + 1 + 1 + 1) → ℕ) (u : ℕ) (hu0 : u = 0) {ε : ℝ} (c' : ℝ)
    (hpiv : minAdm (redChain u M) ≤ u * tailMinWidth M)
    (Zf : Params (redChain u M)
        → Matrix (Fin (dropHead (redChain u M) 0))
            (Fin (dropHead (redChain u M) (Fin.last L))) ℝ) :
    pivotDomLHS M u ε c' Zf ≤ pivotDomRHS M u c' Zf := by
  sorry

/-- **GLUE-2 — the coupled pivot→`decLoss` domination (the analytic crux).** Verbatim statement of the
`RouteMSJHeadSplitDom.headSplit_pivotDom` stub; the controller wires the stub to it. Ratio wiring:
`RHS = ⊤ → C_hle := 1`; else `C_hle := LHS/RHS` (finite by `pivotDom_finiteness`, nonzero denominator by
`pivotDom_RHS_ne_zero`), closing via `ENNReal.div_mul_cancel`; the degenerate `u = 0` cut via
`pivotDom_uzero`. -/
theorem headSplit_pivotDom_impl (M : Fin (L + 1 + 1 + 1) → ℕ) (u : ℕ)
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
    (hfloor : ∀ z, (Zf z * (Zf z)ᵀ - (ε' ^ 2) • (U_sf z * (U_sf z)ᵀ)).PosSemidef) :
    ∃ (C_hle : ℝ≥0∞), C_hle < ⊤
      ∧ (∫⁻ z in paramsBoxM (redChain u M) 1,
            ∫⁻ A_cor in matBox (M 1 - u) (dropHead (redChain u M) 0) 1 ∩ pivotShell M u ε Zf z,
              ∫⁻ x in outerDom u (M 0 - u) (M 1 - u) 1,
                ∫⁻ Γ in {Γ : Fin (M 0 - u) → Fin (M 1 - u) → ℝ |
                    Γ + schurShift x ∈ genBox (Fin (M 0 - u)) (Fin (M 1 - u)) 1},
                  ENNReal.ofReal ((freedSchurLoss x Γ (hsQ M u Zf z A_cor)) ^ (-c')))
          ≤ C_hle * deeperFlagCoreIntegrand M u (![1] : Fin 1 → ℕ)
              (![minAdm (redChain u M) - 1] : Fin 1 → ℕ) Zf
              (fun _ => 0) (fun _ => genBox (Fin (M 0 - u)) (Fin (M 1 - u)) 1) c' := by
  -- fold LHS/RHS to the named abbreviations (defeq)
  change ∃ (C_hle : ℝ≥0∞), C_hle < ⊤ ∧ pivotDomLHS M u ε c' Zf ≤ C_hle * pivotDomRHS M u c' Zf
  rcases Nat.eq_zero_or_pos u with hu0 | hupos
  · -- degenerate `u = 0`: `LHS ≤ RHS`, `C_hle := 1`
    exact ⟨1, ENNReal.one_lt_top,
      by rw [one_mul]; exact pivotDom_uzero M u hu0 c' hpiv Zf⟩
  · -- `u ≥ 1`: ratio trick
    by_cases htop : pivotDomRHS M u c' Zf = ⊤
    · exact ⟨1, ENNReal.one_lt_top, by rw [one_mul, htop]; exact le_top⟩
    · have hRlt : pivotDomRHS M u c' Zf < ⊤ := lt_top_iff_ne_top.mpr htop
      have hne : pivotDomRHS M u c' Zf ≠ 0 := pivotDom_RHS_ne_zero M u hupos c' hnd Zf hZfMeas
      have hfin : pivotDomLHS M u ε c' Zf < ⊤ :=
        pivotDom_finiteness M u hε c' hnd hpiv hcvg hmM hε' Zf hZfMeas U_sf hUs hrank hfloor hRlt
      exact ⟨pivotDomLHS M u ε c' Zf / pivotDomRHS M u c' Zf,
        ENNReal.div_lt_top hfin.ne hne,
        by rw [ENNReal.div_mul_cancel hne htop]⟩

end DLNFibre.DLN.RLCT
