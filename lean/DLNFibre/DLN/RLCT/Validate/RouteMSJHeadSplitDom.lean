import DLNFibre.DLN.RLCT.Validate.RouteMSJDeeperFlagCore
import DLNFibre.DLN.RLCT.Validate.RouteMSJPivotBlowup
import DLNFibre.DLN.RLCT.Validate.RouteMSJRankRCodim
import DLNFibre.DLN.RLCT.Validate.RouteMSJShellContain
import DLNFibre.DLN.RLCT.Validate.RouteMSJBlockReindex
import DLNFibre.DLN.RLCT.Validate.RouteMSJRowSplit
import DLNFibre.DLN.RLCT.Validate.RouteMSJDeepFactor
import DLNFibre.DLN.RLCT.Validate.RouteMSJHeadSplit

/-!
# `DLNFibre.DLN.RLCT.Validate.RouteMSJHeadSplitDom` — Brick D join: the head-split domination

**Isolated Brick D** (`s1-spine-headsplit-cert` Part A + `s1-Chle-angular-integrability-cert`): the
head-split domination with a FINITE reorganization constant. `headSplit_domination_impl` reproduces the
`headSplit_domination` stub signature VERBATIM; the controller wires the stub to it.

The frame data `(Zf, U_sf, hZfMeas, hUsMeas, hUs, hrank, hfloor, hagree)` are HYPOTHESES (Brick F provides
them). This module lands the MECHANICAL reduction (head/row split, the shell⊆good rewrite, the witnesses
`Ccrossf = 0` / `sΓf = genBox`) sorry-free, isolating the GENUINE analytic crux as the single sorry
`headSplit_pivotDom` — the coupled pivot→`decLoss` domination (dropping the `B₁₂·Q_b` cross-coupling),
commissioned as a dedicated 7th brick (design: D-A `pivotBlock_radial_blowup` + D-B
`lintegral_cube_frobSq_neg_of_finrank_range` + `s1-Chle-angular-integrability-cert`).
-/

namespace DLNFibre.DLN.RLCT

open Matrix MeasureTheory
open scoped ENNReal BigOperators

variable {L : ℕ}

/-- Column-width bridge `dropHead (redChain u M) (Fin.last L) = redChain u M (Fin.last (L+1))` (both are
`M (Fin.last (L+1+1))`, the input width). -/
theorem dropHead_last_eq_redChain_last (M : Fin (L + 1 + 1 + 1) → ℕ) (u : ℕ) :
    dropHead (redChain u M) (Fin.last L) = redChain u M (Fin.last (L + 1)) := by
  have h2 : redChain u M (Fin.last (L + 1)) = M (Fin.last (L + 1 + 1)) := by
    rw [← Fin.succ_last, redChain_succ, Fin.succ_last, Fin.succ_last]
  rw [dropHead_redChain_last, h2]

/-- **The reassembled front-factor block product** `Q = [ prod(redChain u M) z ; A_cor·Zf z ]`
(pivot rows `Q_p = prod(redChain u M) z`, corank rows `Q_b = A_cor·Zf z`), with `prod`'s columns cast to
match `Zf`'s column type `Fin (dropHead (redChain u M) (Fin.last L))`. The `Q` fed to `freedSchurLoss` on
the head-split spine. -/
noncomputable def hsQ (M : Fin (L + 1 + 1 + 1) → ℕ) (u : ℕ)
    (Zf : Params (redChain u M)
        → Matrix (Fin (dropHead (redChain u M) 0))
            (Fin (dropHead (redChain u M) (Fin.last L))) ℝ)
    (z : Params (redChain u M))
    (A_cor : Fin (M 1 - u) → Fin (dropHead (redChain u M) 0) → ℝ) :
    Matrix (Fin u ⊕ Fin (M 1 - u)) (Fin (dropHead (redChain u M) (Fin.last L))) ℝ :=
  Matrix.fromRows
    ((prod (redChain u M) z).submatrix (finCongr (redChain_zero u M).symm)
      (finCongr (dropHead_last_eq_redChain_last M u)))
    (Matrix.of A_cor * Zf z)

/-- **GLUE-2 — the coupled pivot→`decLoss` domination (the analytic crux, ISOLATED as the 7th brick).**
On the `(z, A_cor)`-box, the freed Schur-loss spine integrand (pivot rows `prod(redChain u M) z`, corank
rows `A_cor·Zf z`) is dominated by a FINITE constant times the comparator-core integrand at the clean data
`k = ![1]`, `jc = ![minAdm(redChain u M) − 1]`, `Ccrossf = 0`, `sΓf = genBox`.

CONTENT (NOT a mechanical brick compose — the `B₁₂·Q_b` cross-term drop is non-pointwise): the P-radial
blow-up (D-A `pivotBlock_radial_blowup`) of `frobSq(P·Q_p + B₁₂·Q_b)` exposes `commonDivisor(v)²·frobSq
(Q_p) = decLoss` + the Jacobian monomial `r^{u·M₁−1}`; the drop to the comparator's `r^{minAdm−1}` is an
on-`[0,1]` power domination (via `hpiv`: `ρ ≤ M₁ ⟹ u·M₁ ≥ minAdm`); the absorbed P-angular/`B₁₂`-box/`C`
directions integrate to the finite `C_hle`, finite as a CONSTANT via the codim-`u·ρ` integrable singularity
(D-B `lintegral_cube_frobSq_neg_of_finrank_range`, `c'' < u·ρ/2` in-regime; det-Gram convergence via `hcvg`,
`a < m − b + 1`). Outside the operative `ab/2 < c' < carrierThreshold` regime both sides are `⊤`, so the
bound is trivial there. Design: `s1-Chle-angular-integrability-cert`. -/
theorem headSplit_pivotDom (M : Fin (L + 1 + 1 + 1) → ℕ) (u : ℕ)
    {ε : ℝ} (hε : 0 < ε) (c' : ℝ) (hnd : ∀ i, 1 ≤ M i)
    (hpiv : minAdm (redChain u M) ≤ u * tailMinWidth M) {m : ℕ}
    (hcvg : (M 0 - u) + (M 1 - u) ≤ m) (hmM : m ≤ dropHead (redChain u M) 0)
    {ε' : ℝ} (hε' : 0 < ε')
    (Zf : Params (redChain u M)
        → Matrix (Fin (dropHead (redChain u M) 0))
            (Fin (dropHead (redChain u M) (Fin.last L))) ℝ)
    (U_sf : Params (redChain u M) → Matrix (Fin (dropHead (redChain u M) 0)) (Fin m) ℝ)
    (hUs : ∀ z, (U_sf z)ᵀ * U_sf z = 1)
    (hrank : ∀ z, m ≤ (Zf z).rank)
    (hfloor : ∀ z, (Zf z * (Zf z)ᵀ - (ε' ^ 2) • (U_sf z * (U_sf z)ᵀ)).PosSemidef) :
    ∃ (C_hle : ℝ≥0∞), C_hle < ⊤
      ∧ (∫⁻ z in paramsBoxM (redChain u M) 1,
            ∫⁻ A_cor in matBox (M 1 - u) (dropHead (redChain u M) 0) 1,
              ∫⁻ x in outerDom u (M 0 - u) (M 1 - u) 1,
                ∫⁻ Γ in {Γ : Fin (M 0 - u) → Fin (M 1 - u) → ℝ |
                    Γ + schurShift x ∈ genBox (Fin (M 0 - u)) (Fin (M 1 - u)) 1},
                  ENNReal.ofReal ((freedSchurLoss x Γ (hsQ M u Zf z A_cor)) ^ (-c')))
          ≤ C_hle * deeperFlagCoreIntegrand M u (![1] : Fin 1 → ℕ)
              (![minAdm (redChain u M) - 1] : Fin 1 → ℕ) Zf
              (fun _ => 0) (fun _ => genBox (Fin (M 0 - u)) (Fin (M 1 - u)) 1) c' := by
  sorry

/-- **The mechanical head/row-split domination** (steps 1,2,5,6 — banked plumbing): the literal
shell-restricted spine integrand is dominated by the `(z, A_cor)`-box freed-loss integrand at `Q = hsQ`
(pivot rows `prod(redChain u M) z`, corank rows `A_cor·Zf z`). Route: head split (`paramsHeadSplit` +
`prod_headSplit`, MP), the shell⊆good-set rewrite `Zf z = Z_deep` on the shell (D-C `shell_subset_goodSet`
+ `hagree`), drop the shell indicator (`≥ 0`), Tonelli, row split (`rowSplit_lintegral_eq`), recombine
`(z0, A'tail) ↝ z`. NO analytic content — pure measure reorganization onto `GLUE-2`'s LHS shape. -/
theorem shellSpine_le_hsQ_box {L : ℕ} (M : Fin (L + 1 + 1 + 1) → ℕ) (t j : ℕ)
    (κ : Fin (t + j) ↪ Fin (M 1)) {ε : ℝ} (hε : 0 < ε) (c' : ℝ)
    (ht : t ≤ min (M 0) (M 1)) (hj : j ≤ min (M 0 - t) (M 1 - t))
    (ht1 : 1 ≤ t) (hnd : ∀ i, 1 ≤ M i)
    (hrange : min (M 1) (M (Fin.last (L + 1 + 1))) - j ≤ M 2)
    {ε' : ℝ} (hε' : 0 < ε')
    (Zf : Params (redChain (t + j) M)
        → Matrix (Fin (dropHead (redChain (t + j) M) 0))
            (Fin (dropHead (redChain (t + j) M) (Fin.last L))) ℝ)
    (hagree : ∀ z, weakEigCount ε' (deeperFlagZdeep M (t + j) z)
        ≤ dropHead (redChain (t + j) M) 0 - (min (M 1) (M (Fin.last (L + 1 + 1))) - j)
        → Zf z = deeperFlagZdeep M (t + j) z) :
    shellSpineIntegrand M (t + j) κ ε (min (M 0 - t) (M 1 - t)) ⟨j, Nat.lt_succ_of_le hj⟩ c'
      ≤ ∫⁻ z in paramsBoxM (redChain (t + j) M) 1,
          ∫⁻ A_cor in matBox (M 1 - (t + j)) (dropHead (redChain (t + j) M) 0) 1,
            ∫⁻ x in outerDom (t + j) (M 0 - (t + j)) (M 1 - (t + j)) 1,
              ∫⁻ Γ in {Γ : Fin (M 0 - (t + j)) → Fin (M 1 - (t + j)) → ℝ |
                  Γ + schurShift x ∈ genBox (Fin (M 0 - (t + j))) (Fin (M 1 - (t + j))) 1},
                ENNReal.ofReal ((freedSchurLoss x Γ (hsQ M (t + j) Zf z A_cor)) ^ (-c')) := by
  sorry

/-- **Brick D (isolated): the head-split domination with a FINITE reorganization constant.** Verbatim
signature of the `headSplit_domination` stub; the controller wires the stub to it. -/
theorem headSplit_domination_impl {L : ℕ} (M : Fin (L + 1 + 1 + 1) → ℕ) (t j : ℕ)
    (κ : Fin (t + j) ↪ Fin (M 1)) {ε : ℝ} (hε : 0 < ε) (c' : ℝ)
    (ht : t ≤ min (M 0) (M 1)) (hj : j ≤ min (M 0 - t) (M 1 - t))
    (ht1 : 1 ≤ t) (hnd : ∀ i, 1 ≤ M i)
    (hpiv : minAdm (redChain (t + j) M) ≤ (t + j) * tailMinWidth M)
    (hcvg : (M 0 - (t + j)) + (M 1 - (t + j))
        ≤ min (M 1) (M (Fin.last (L + 1 + 1))) - j)
    (hrange : min (M 1) (M (Fin.last (L + 1 + 1))) - j ≤ M 2)
    {ε' : ℝ} (hε' : 0 < ε')
    (Zf : Params (redChain (t + j) M)
        → Matrix (Fin (dropHead (redChain (t + j) M) 0))
            (Fin (dropHead (redChain (t + j) M) (Fin.last L))) ℝ)
    (U_sf : Params (redChain (t + j) M)
        → Matrix (Fin (dropHead (redChain (t + j) M) 0))
            (Fin (min (M 1) (M (Fin.last (L + 1 + 1))) - j)) ℝ)
    (hZfMeas : Measurable Zf) (hUsMeas : Measurable U_sf)
    (hUs : ∀ z, (U_sf z)ᵀ * U_sf z = 1)
    (hrank : ∀ z, (min (M 1) (M (Fin.last (L + 1 + 1))) - j) ≤ (Zf z).rank)
    (hfloor : ∀ z, (Zf z * (Zf z)ᵀ - (ε' ^ 2) • (U_sf z * (U_sf z)ᵀ)).PosSemidef)
    (hagree : ∀ z, weakEigCount ε' (deeperFlagZdeep M (t + j) z)
        ≤ dropHead (redChain (t + j) M) 0 - (min (M 1) (M (Fin.last (L + 1 + 1))) - j)
        → Zf z = deeperFlagZdeep M (t + j) z) :
    ∃ (Ccrossf : Params (redChain (t + j) M)
          → Matrix (Fin (M 0 - (t + j))) (Fin (dropHead (redChain (t + j) M) (Fin.last L))) ℝ)
        (sΓf : Params (redChain (t + j) M)
          → Set (Fin (M 0 - (t + j)) → Fin (M 1 - (t + j)) → ℝ))
        (C_hle : ℝ≥0∞),
      C_hle < ⊤
      ∧ shellSpineIntegrand M (t + j) κ ε (min (M 0 - t) (M 1 - t)) ⟨j, Nat.lt_succ_of_le hj⟩ c'
          ≤ C_hle * deeperFlagCoreIntegrand M (t + j) (![1] : Fin 1 → ℕ)
              (![minAdm (redChain (t + j) M) - 1] : Fin 1 → ℕ) Zf Ccrossf sΓf c' := by
  -- witnesses: `Ccrossf = 0`, `sΓf = genBox`
  refine ⟨fun _ => 0, fun _ => genBox (Fin (M 0 - (t + j))) (Fin (M 1 - (t + j))) 1, ?_⟩
  -- `m ≤ M₂ = dropHead (redChain u M) 0` from `hrange`
  have hmM : min (M 1) (M (Fin.last (L + 1 + 1))) - j ≤ dropHead (redChain (t + j) M) 0 := by
    rw [dropHead_redChain_zero]; exact hrange
  -- GLUE-2: the coupled pivot→decLoss domination (the isolated 7th brick)
  obtain ⟨C_hle, hfin, hle⟩ :=
    headSplit_pivotDom M (t + j) hε c' hnd hpiv (m := min (M 1) (M (Fin.last (L + 1 + 1))) - j)
      hcvg hmM hε' Zf U_sf hUs hrank hfloor
  refine ⟨C_hle, hfin, ?_⟩
  -- mechanical head/row split, then GLUE-2
  exact le_trans (shellSpine_le_hsQ_box M t j κ hε c' ht hj ht1 hnd hrange hε' Zf hagree) hle

end DLNFibre.DLN.RLCT
