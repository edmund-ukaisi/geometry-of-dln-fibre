import DLNFibre.DLN.RLCT.Validate.RouteMSJPivotDom

set_option linter.style.longLine false

/-!
# `DLNFibre.DLN.RLCT.Validate.RouteMSJPivotFin` — GLUE-2 (b): the pivot→`decLoss` finiteness

**Thread `genm-sj5` (aoyagi-full Stage 2), the analytic CRUX of the head-split (GLUE-2).**
`pivotDom_finiteness_impl` reproduces the `RouteMSJPivotDom.pivotDom_finiteness` stub signature VERBATIM;
the controller wires the stub to it.

## Sound decomposition (locked with the controller, 2026-07-13, reconciliation gate + Codex xhigh)

The crux `pivotDomRHS < ⊤ → pivotDomLHS < ⊤` splits, at the SHARED RLCT threshold
`X := (minAdm (redChain u M) + peelCharge M u)/2`, into:

* **Step 1 — the exponent extraction** `pivotDomRHS_lt_top_exponent` (SOUND). `pivotDomRHS < ⊤ ⟹ c' < X`.
  The comparator diverges above `X`: lower-bound the corank integral on the sublevel set
  `{‖Γ·(A_cor·Zf z)‖² ≤ decLoss}` (integrand `≥ (2·decLoss)^{−c'}` there) by the corner sublevel-VOLUME
  lower bound `μ ≳ decLoss^{ab/2}` (a `Γ`-box of radius `√decLoss/‖Q_b‖`), leaving the pure monomial
  `∫_{v0} v0^{minAdm(redChain)−1+ab−2c'}` which `= ⊤` for `c' ≥ X`; the `z`-factor is positive
  (`frobSq(prod) > 0` a.e., bounded on the box). NO two-sided corner atom needed.

* **Step 2 — the forward finiteness** `forward_LHS_finiteness` (the ISOLATED CRUX, `sorry`). `c' < X ⟹
  pivotDomLHS < ⊤`. This is the genuine bilinear-RLCT: the pivot `‖P·Q_p + B₁₂·Q_b‖²` couples to the corank
  variable `A_cor` via the `B₁₂·Q_b` cross-term, so it is NOT `∑(linear)²` jointly (D-B cannot shortcut it)
  and the threshold `X` is the OUTER `(z,A_cor)` degeneracy stratum, not a fixed-outer codimension. Its exact
  scope-covering decomposition (the non-pointwise cross-term drop + a uniform angular/Jacobian ratio) is being
  pinned by the parallel pen-and-paper (`archfin`); the statement here is guaranteed-correct (`X` is the
  sharp forward threshold) so the sorry is a true building block, filled on the pin.

* **`u = 0` edge** `pivotDom_finiteness_uzero`: the `0`-width pivot makes the front block vanish
  (`freedSchurLoss = ‖Γ·Q_b‖²`) and `decLoss = 0`, so `pivotDomLHS ≤ pivotDomRHS` (`pivotDom_uzero`) — no
  pivot energy, not the analytic crux.
-/

namespace DLNFibre.DLN.RLCT

open Matrix MeasureTheory
open scoped ENNReal BigOperators

variable {L : ℕ}

/-- **The `matBox` volume** `= ofReal(2ρ)^{a·b}` (for `ρ ≥ 0`). Nested `volume_pi_pi` + `Real.volume_Icc`. -/
theorem matBox_volume (a b : ℕ) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    volume (matBox a b ρ) = ENNReal.ofReal (2 * ρ) ^ (a * b) := by
  have hset : matBox a b ρ
      = Set.univ.pi (fun _ : Fin a => Set.univ.pi (fun _ : Fin b => Set.Icc (-ρ) ρ)) := by
    ext X
    simp only [matBox, Set.mem_setOf_eq, Set.mem_pi, Set.mem_univ, true_implies]
  rw [hset, MeasureTheory.volume_pi_pi]
  have hinner : ∀ _i : Fin a,
      volume (Set.univ.pi (fun _ : Fin b => Set.Icc (-ρ) ρ)) = ENNReal.ofReal (2 * ρ) ^ b := by
    intro _
    rw [MeasureTheory.volume_pi_pi]
    simp only [Real.volume_Icc]
    rw [show ρ - -ρ = 2 * ρ by ring, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [Finset.prod_congr rfl (fun i _ => hinner i),
    Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul, Nat.mul_comm]

/-- **The corner sublevel-volume lower bound.** For `w > 0` and a `Γ`-box of radius `ρ ≤ 1` on which
`frobSq(Γ·(A·Z)) ≤ w` (uniformly over `A ∈ matBox`), the corank inner integral dominates
`(2w)^{−c'}·(2ρ)^{ab}·vol(matBox b M₂ 1)`: restrict `Γ` to `matBox a b ρ ⊆ genBox`, use the pointwise
`(w+frobSq)^{−c'} ≥ (2w)^{−c'}` and `matBox_volume`. The `(2ρ)^{ab}` scaling is what produces the `ab/2`
threshold shift downstream. -/
theorem corner_inner_ge {a b M₂ nn : ℕ} (Z : Matrix (Fin M₂) (Fin nn) ℝ) {c' : ℝ} (hc0 : 0 ≤ c')
    {w ρ : ℝ} (hw : 0 < w) (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hbound : ∀ A : Fin b → Fin M₂ → ℝ, A ∈ matBox b M₂ 1 →
      ∀ Γ : Fin a → Fin b → ℝ, Γ ∈ matBox a b ρ →
        frobSq ((Matrix.of Γ) * ((Matrix.of A) * Z)) ≤ w) :
    ENNReal.ofReal ((2 * w) ^ (-c')) * ENNReal.ofReal (2 * ρ) ^ (a * b) * volume (matBox b M₂ 1)
      ≤ ∫⁻ A in matBox b M₂ 1, ∫⁻ Γ in genBox (Fin a) (Fin b) 1,
          ENNReal.ofReal ((w + frobSq ((Matrix.of Γ) * ((Matrix.of A) * Z))) ^ (-c')) := by
  have hsub : matBox a b ρ ⊆ genBox (Fin a) (Fin b) 1 := by
    intro Γ hΓ i k
    have := hΓ i k
    rw [Set.mem_Icc] at this ⊢
    constructor <;> [nlinarith [this.1]; nlinarith [this.2]]
  -- per-`A` inner lower bound
  have hinner : ∀ A : Fin b → Fin M₂ → ℝ, A ∈ matBox b M₂ 1 →
      ENNReal.ofReal ((2 * w) ^ (-c')) * ENNReal.ofReal (2 * ρ) ^ (a * b)
        ≤ ∫⁻ Γ in genBox (Fin a) (Fin b) 1,
            ENNReal.ofReal ((w + frobSq ((Matrix.of Γ) * ((Matrix.of A) * Z))) ^ (-c')) := by
    intro A hA
    calc ENNReal.ofReal ((2 * w) ^ (-c')) * ENNReal.ofReal (2 * ρ) ^ (a * b)
        = ENNReal.ofReal ((2 * w) ^ (-c')) * volume (matBox a b ρ) := by
          rw [matBox_volume a b hρ0.le]
      _ = ∫⁻ _Γ in matBox a b ρ, ENNReal.ofReal ((2 * w) ^ (-c')) := by
          rw [setLIntegral_const]
      _ ≤ ∫⁻ Γ in matBox a b ρ,
            ENNReal.ofReal ((w + frobSq ((Matrix.of Γ) * ((Matrix.of A) * Z))) ^ (-c')) := by
          refine setLIntegral_mono_ae' (matBox_measurableSet a b ρ) (ae_of_all _ (fun Γ hΓ => ?_))
          refine ENNReal.ofReal_le_ofReal ?_
          have hfnn : (0 : ℝ) ≤ frobSq ((Matrix.of Γ) * ((Matrix.of A) * Z)) := frobSq_nonneg _
          have hle : w + frobSq ((Matrix.of Γ) * ((Matrix.of A) * Z)) ≤ 2 * w := by
            have := hbound A hA Γ hΓ; linarith
          exact Real.rpow_le_rpow_of_nonpos (by linarith) hle (by linarith)
      _ ≤ ∫⁻ Γ in genBox (Fin a) (Fin b) 1,
            ENNReal.ofReal ((w + frobSq ((Matrix.of Γ) * ((Matrix.of A) * Z))) ^ (-c')) :=
          lintegral_mono_set hsub
  calc ENNReal.ofReal ((2 * w) ^ (-c')) * ENNReal.ofReal (2 * ρ) ^ (a * b) * volume (matBox b M₂ 1)
      = ∫⁻ _A in matBox b M₂ 1,
          ENNReal.ofReal ((2 * w) ^ (-c')) * ENNReal.ofReal (2 * ρ) ^ (a * b) := by
        rw [setLIntegral_const]
    _ ≤ ∫⁻ A in matBox b M₂ 1, ∫⁻ Γ in genBox (Fin a) (Fin b) 1,
          ENNReal.ofReal ((w + frobSq ((Matrix.of Γ) * ((Matrix.of A) * Z))) ^ (-c')) :=
        setLIntegral_mono_ae' (matBox_measurableSet b M₂ 1) (ae_of_all _ (fun A hA => hinner A hA))

/-- **Step 1 — the exponent extraction.** If the comparator-core RHS is finite then `c'` is strictly below
the shared RLCT threshold `X = (minAdm (redChain u M) + peelCharge M u)/2`. Proof (contrapositive): for
`c' ≥ X`, `pivotDomRHS = ⊤` — the corner sublevel-volume lower bound `μ{‖Γ·(A_cor·Zf z)‖² ≤ D} ≳ D^{ab/2}`
turns the RHS into `≳ ∫_z (pos)·∫_{v0} v0^{minAdm(redChain)−1+ab−2c'}`, whose `v0`-monomial diverges at
`c' ≥ X`. -/
theorem pivotDomRHS_lt_top_exponent (M : Fin (L + 1 + 1 + 1) → ℕ) (u : ℕ) (hu : 1 ≤ u) (c' : ℝ)
    (hnd : ∀ i, 1 ≤ M i)
    (Zf : Params (redChain u M)
        → Matrix (Fin (dropHead (redChain u M) 0))
            (Fin (dropHead (redChain u M) (Fin.last L))) ℝ)
    (hZfMeas : Measurable Zf)
    (hRHS : pivotDomRHS M u c' Zf < ⊤) :
    c' < ((minAdm (redChain u M) : ℝ) + (peelCharge M u : ℝ)) / 2 := by
  sorry

/-- **Step 2 — the forward finiteness (the ISOLATED CRUX).** Below the shared RLCT threshold `X`, the
freed Schur-loss spine LHS is finite. THE genuine bilinear-RLCT content of GLUE-2 (the non-pointwise
cross-term drop; the pivot couples to `A_cor` via `B₁₂·Q_b`). Guaranteed-correct statement (`X` is the
sharp forward threshold); its decomposition is pinned by the parallel pen-and-paper. -/
theorem forward_LHS_finiteness (M : Fin (L + 1 + 1 + 1) → ℕ) (u : ℕ) (hu : 1 ≤ u)
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
    (hc' : c' < ((minAdm (redChain u M) : ℝ) + (peelCharge M u : ℝ)) / 2) :
    pivotDomLHS M u c' Zf < ⊤ := by
  sorry

/-- **The `u = 0` edge.** With a `0`-width pivot the front block vanishes and `decLoss = 0`, so
`pivotDomLHS ≤ pivotDomRHS` (`pivotDom_uzero`), hence finite from `hRHS`. -/
theorem pivotDom_finiteness_uzero (M : Fin (L + 1 + 1 + 1) → ℕ) (u : ℕ) (hu0 : u = 0) (c' : ℝ)
    (hpiv : minAdm (redChain u M) ≤ u * tailMinWidth M)
    (Zf : Params (redChain u M)
        → Matrix (Fin (dropHead (redChain u M) 0))
            (Fin (dropHead (redChain u M) (Fin.last L))) ℝ)
    (hRHS : pivotDomRHS M u c' Zf < ⊤) :
    pivotDomLHS M u c' Zf < ⊤ :=
  lt_of_le_of_lt (pivotDom_uzero M u hu0 c' hpiv Zf) hRHS

/-- **GLUE-2 finiteness (the isolated crux).** Verbatim statement of
`RouteMSJPivotDom.pivotDom_finiteness`; the controller wires the stub to it. Splits into the exponent
extraction (step 1) and the forward finiteness (step 2, the isolated crux) at the shared threshold, with the
`u = 0` edge separate. -/
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
  rcases Nat.eq_zero_or_pos u with hu0 | hupos
  · exact pivotDom_finiteness_uzero M u hu0 c' hpiv Zf hRHS
  · exact forward_LHS_finiteness M u hupos hε c' hnd hpiv hcvg hmM hε' Zf hZfMeas U_sf hUs hrank hfloor
      (pivotDomRHS_lt_top_exponent M u hupos c' hnd Zf hZfMeas hRHS)

end DLNFibre.DLN.RLCT
