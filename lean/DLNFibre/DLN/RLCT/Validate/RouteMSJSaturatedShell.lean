import DLNFibre.DLN.RLCT.Validate.RouteMSJArity4Assembly
import DLNFibre.DLN.RLCT.Validate.RouteMSJDeeperFlagCore

set_option linter.style.longLine false

/-!
# `RouteMSJSaturatedShell` — the `j = r` saturated boundary brick (a = 0 brick + b = 0 collapse)

**Thread `genm-satbuild` (aoyagi-full Stage 2), the saturated boundary hole of the arity-≥4 `(□)`
closure.** Fills the `hbdryShell` slot at the saturated shell `j = r` of the coupled-incidence assembly
(`RouteMSJArity4Assembly`): for a `≥ 4`-width chain `M` at a binding cut `t` with `M₀ ≤ M₁`, the saturated
shell `j = r = min(M₀−t, M₁−t)` sits at the cut `u = t + r = min(M₀,M₁) = M₀`, so `a = M₀ − u = 0`.

## The mechanism (satred's design cert, `genm-satred/satred-cert.md`)
At `a = 0`:
* the SECOND `frobSq` of `freedSchurLoss` vanishes (its rows are indexed by `Fin (M₀−u) = Fin 0`);
* the corank block `Γ : Fin (M₀−u) → Fin (M₁−u) → ℝ` lives in the singleton (empty-domain) space, so the
  `∫⁻ Γ`-integral collapses to a bounded factor.

The surviving loss is the pivot energy `frobSq(P·(Q_inl + P⁻¹·B₁₂·Q_inr))` where `Q_inl = z₀·Zdeep`,
`Q_inr = A_cor·Zdeep`; on the invertible-pivot chart this equals `frobSq((P·z₀ + B₁₂·A_cor)·Zdeep) =
frobSq(z̃₀·Zdeep)`, `z̃₀ = [P|B₁₂]·A₀` the reduced-chain leading layer. The det-P→0 degeneracy is benign
(the corank cross-block `B₁₂` keeps `X = [P|B₁₂]` full row rank). Pushing forward `(x, A₀) ↦ z̃₀` gives the
reduced-chain box integrand at the shifted exponent `q = c' + Δ + ε`, `Δ = ½(minAdm(redChain u M) − minAdm M)
≥ 0`, dominated by the reduced chain's headroom — finite by the arity-IH `RouteMBoxThresholdFinite`.

## What is PROVED here vs ASSUMED
* **Proved (sorry-free):** the `a = 0` structural collapse — `freedSchurLoss` reduces to its first term
  (`freedSchurLoss_of_isEmpty_a`), and the shell integrand is dominated by the Γ-free front integrand
  (`shellSpine_le_satFront`). The reduction skeleton (`saturatedShell_lt_top`) consuming the IH. Also the
  `b = 0` mirror STRUCTURAL COLLAPSE (`freedSchurLoss_of_isEmpty_b`, `shellSpine_le_satFront_b`; see the
  `b = 0` section) — its reduction skeleton is deferred (design-gated, distinct mechanism).
* **Named hypothesis (`hdensity`, the genuinely-new analytic content):** the matrix-product
  pushforward-density domination `satFrontIntegrand ≤ K · routeMLayerBoxIntegral(redChain u M) q 1`, with
  `K < ⊤` and `q < ½·minAdm(redChain u M)`. This is the fused `(P,B₁₂,A₀,z_deep) ↦ (z̃₀, z_deep)`
  change-of-variables; it is NOT banked (nothing does this reverse two-full-layer reconstruction with the
  density) and is left as the tide's one analytic hole (`hdensity` is a HYPOTHESIS, not a `sorry` — this
  module is sorry-free, `[propext, Classical.choice, Quot.sound]`).

## Discharging `hdensity` (satred, cert §4 correction, commit `571214cbc`)
`hdensity` is always TRUE for `c' < ½·minAdm M` (finiteness `λ_H = ½·minAdm M` holds unconditionally,
`(I) = RMBTF(M)|_{P invertible}`, Aoyagi), so the reduction skeleton is sound. Its PROOF splits by regime,
`A := max_{1≤j≤min(u,M₂)} j(M₂−b−j)` (the pushforward-density order) vs `2Δ = minAdm(redChain u M) − minAdm M`:
* **`A ≤ 2Δ` (sufficient: `b ≥ M₂−1`, bounded/log density):** the clean bounded/log measure-domination,
  folds at `q = c' + ε`. The tractable sub-case (target it first).
* **`A > 2Δ` (small `b`, INCLUDING the `b = 0` corner `M₀ = M₁` that this a=0 brick covers via
  `hab : M₀ ≤ M₁`):** the naive pointwise `‖z̃₀‖^{−A}`-fold UNDERSHOOTS; discharge needs the joint
  determinantal rank-sector resolution (the genuinely-hard analytic piece, where the det-P `B₁₂`
  compensation is weak/absent). Left open.

The `b = 0` MIRROR (`M₁ < M₀`, `a > 0`) is a genuinely SEPARATE reduction — NOT a mechanical transpose of
`a = 0`. At `b = 0` the front factor `[P;C]` is `M₀×M₁` TALL / full COLUMN rank, so `A₀ ↦ [P;C]·A₀` is
INJECTIVE (singular pushforward on a proper subvariety), the OPPOSITE of `a = 0`'s WIDE / full-ROW-rank
surjective front. So there is no abs-continuous density and no `z̃₀`-box reduction; the `C` output rows are a
separate high-codim OUTPUT charge, and the `b = 0` reduced-chain target is `redChain (M 0) M` (leading `M₀`),
not `redChain u M`. The `b = 0` STRUCTURAL COLLAPSE is proved sorry-free below
(`freedSchurLoss_of_isEmpty_b`, `shellSpine_le_satFront_b`); the `b = 0` reduction SKELETON is DEFERRED
pending the corner-frontier mechanism verdict (`RouteMBoxThresholdFinite` is proved for arbitrary unsorted
`M`, so the mirror genuinely arises and cannot be normalized away).
-/

namespace DLNFibre.DLN.RLCT

open Matrix MeasureTheory
open scoped ENNReal BigOperators NNReal

variable {L : ℕ}

/-! ## Step 1 — the `a = 0` collapse of `freedSchurLoss` -/

/-- **`freedSchurLoss` at `a = 0` (empty corank rows).** When the corank row index `Fin a` is empty, the
second (corank-energy) `frobSq` vanishes and the freed loss is its first (pivot-energy) term only —
independent of the freed block `Γ`. -/
theorem freedSchurLoss_of_isEmpty_a {t a b q : ℕ} (haE : IsEmpty (Fin a))
    (x : SJOuter t a b) (Γ : Fin a → Fin b → ℝ) (Q : Matrix (Fin t ⊕ Fin b) (Fin q) ℝ) :
    freedSchurLoss x Γ Q
      = frobSq (Matrix.of x.1.1 * (Q.submatrix Sum.inl id
          + (Matrix.of x.1.1)⁻¹ * Matrix.of x.1.2 * Q.submatrix Sum.inr id)) := by
  haveI := haE
  have h2 : frobSq (Matrix.of x.2 * (Q.submatrix Sum.inl id
        + (Matrix.of x.1.1)⁻¹ * Matrix.of x.1.2 * Q.submatrix Sum.inr id)
      + Matrix.of Γ * Q.submatrix Sum.inr id) = 0 := by
    simp [frobSq, Finset.univ_eq_empty]
  rw [freedSchurLoss, h2, add_zero]

/-! ## Step 2 — the Γ-free front integrand and the collapse domination -/

/-- **The `a = 0`-collapsed front integrand.** The shell integrand with the (empty) corank block `Γ`
integrated out and the empty-row `frobSq` dropped: the pivot energy
`frobSq(P·(Q_inl + P⁻¹·B₁₂·Q_inr))^{−c'}` integrated over the shell-restricted `A'` and the front block
`x ∈ outerDom u 0 (M₁−u) 1`. -/
noncomputable def satFrontIntegrand (M : Fin (L + 1 + 1 + 1) → ℕ) (u : ℕ)
    (κ : Fin u ↪ Fin (M 1)) (ε : ℝ) (r : ℕ) (jf : Fin (r + 1)) (c' : ℝ) : ℝ≥0∞ :=
  ∫⁻ A' in paramsBoxM (tailChain M) 1
      ∩ {A' | prod (tailChain M) A' ∈ singularShell ε r jf},
    ∫⁻ x in outerDom u (M 0 - u) (M 1 - u) 1,
      ENNReal.ofReal
        ((frobSq (Matrix.of x.1.1
          * (((prod (tailChain M) A').submatrix (blockSplitEquiv κ) id).submatrix Sum.inl id
            + (Matrix.of x.1.1)⁻¹ * Matrix.of x.1.2
                * ((prod (tailChain M) A').submatrix (blockSplitEquiv κ) id).submatrix Sum.inr id)))
          ^ (-c'))

/-- **The `a = 0` collapse domination.** When `M₀ − u = 0`, the shell integrand is bounded by the Γ-free
front integrand: the `∫⁻ Γ`-integral is over the singleton empty-domain space (mass `≤ 1`) and the
integrand is Γ-independent after the empty-row `frobSq` drops. -/
theorem shellSpine_le_satFront (M : Fin (L + 1 + 1 + 1) → ℕ) (u : ℕ)
    (κ : Fin u ↪ Fin (M 1)) (ε : ℝ) (r : ℕ) (jf : Fin (r + 1)) (c' : ℝ)
    (ha0 : M 0 - u = 0) :
    shellSpineIntegrand M u κ ε r jf c' ≤ satFrontIntegrand M u κ ε r jf c' := by
  haveI hIE : IsEmpty (Fin (M 0 - u)) := by rw [ha0]; infer_instance
  haveI hProb : IsProbabilityMeasure
      (volume : Measure (Fin (M 0 - u) → Fin (M 1 - u) → ℝ)) := by
    rw [Measure.volume_pi_eq_dirac]; infer_instance
  rw [shellSpineIntegrand, satFrontIntegrand]
  refine lintegral_mono (fun A' => ?_)
  refine lintegral_mono (fun x => ?_)
  set Q := (prod (tailChain M) A').submatrix (blockSplitEquiv κ) id with hQ
  have hfl : ∀ Γ : Fin (M 0 - u) → Fin (M 1 - u) → ℝ, freedSchurLoss x Γ Q
      = frobSq (Matrix.of x.1.1 * (Q.submatrix Sum.inl id
          + (Matrix.of x.1.1)⁻¹ * Matrix.of x.1.2 * Q.submatrix Sum.inr id)) :=
    fun Γ => freedSchurLoss_of_isEmpty_a hIE x Γ Q
  calc ∫⁻ Γ in {Γ : Fin (M 0 - u) → Fin (M 1 - u) → ℝ |
          Γ + schurShift x ∈ genBox (Fin (M 0 - u)) (Fin (M 1 - u)) 1},
          ENNReal.ofReal (freedSchurLoss x Γ Q ^ (-c'))
      = ∫⁻ _Γ in {Γ : Fin (M 0 - u) → Fin (M 1 - u) → ℝ |
          Γ + schurShift x ∈ genBox (Fin (M 0 - u)) (Fin (M 1 - u)) 1},
          ENNReal.ofReal ((frobSq (Matrix.of x.1.1 * (Q.submatrix Sum.inl id
            + (Matrix.of x.1.1)⁻¹ * Matrix.of x.1.2 * Q.submatrix Sum.inr id))) ^ (-c')) :=
        lintegral_congr (fun Γ => by rw [hfl Γ])
    _ = ENNReal.ofReal ((frobSq (Matrix.of x.1.1 * (Q.submatrix Sum.inl id
            + (Matrix.of x.1.1)⁻¹ * Matrix.of x.1.2 * Q.submatrix Sum.inr id))) ^ (-c'))
          * volume {Γ : Fin (M 0 - u) → Fin (M 1 - u) → ℝ |
              Γ + schurShift x ∈ genBox (Fin (M 0 - u)) (Fin (M 1 - u)) 1} :=
        setLIntegral_const _ _
    _ ≤ ENNReal.ofReal ((frobSq (Matrix.of x.1.1 * (Q.submatrix Sum.inl id
            + (Matrix.of x.1.1)⁻¹ * Matrix.of x.1.2 * Q.submatrix Sum.inr id))) ^ (-c')) * 1 := by
        gcongr
        exact le_trans (measure_mono (Set.subset_univ _)) (le_of_eq measure_univ)
    _ = ENNReal.ofReal ((frobSq (Matrix.of x.1.1 * (Q.submatrix Sum.inl id
            + (Matrix.of x.1.1)⁻¹ * Matrix.of x.1.2 * Q.submatrix Sum.inr id))) ^ (-c')) :=
        mul_one _

/-! ## Step 3 — the brick: box-finiteness at the saturated shell -/

/-- **The `j = r` saturated boundary brick (a = 0 case).** At the saturated shell `j = r = min(M₀−t, M₁−t)`
with `M₀ ≤ M₁` (cut `u = t + ↑j`, so `a = M₀ − u = 0`), the spine integrand is finite, GIVEN:
* the arity-IH `hIH : RouteMBoxThresholdFinite (redChain (t + ↑j) M)` (threaded by the capstone);
* the matrix-product pushforward-density domination `hdensity` (∃ a valid exponent `q < ½·minAdm(redChain)`
  and finite constant `K` dominating the a=0-collapsed front integrand by the reduced box) — the
  genuinely-new analytic content (see the module docstring for its regime-split discharge).

Weakest hypotheses: the reduction needs only `hjeq` (j = r) and `hab` (M₀ ≤ M₁) to force `a = 0`, plus
`hIH` and `hdensity`; nondegeneracy (`1 ≤ t`, `t+1 ≤ min(M₀,M₁)`, `∀i, 1 ≤ Mᵢ`) and `ε > 0` are NOT needed
for the reduction (they gate `hdensity`'s discharge upstream, not this step). Conclusion matches
`RouteMSJArity4Assembly`'s `hbdryShell` slot at `j = r` verbatim. -/
theorem saturatedShell_lt_top (M : Fin (L + 1 + 1 + 1) → ℕ) (t : ℕ)
    (j : Fin (min (M 0 - t) (M 1 - t) + 1)) (hjeq : (j : ℕ) = min (M 0 - t) (M 1 - t))
    (κ : Fin (t + (j : ℕ)) ↪ Fin (M 1)) (ε c' : ℝ)
    (hab : M 0 ≤ M 1)
    (hIH : RouteMBoxThresholdFinite (redChain (t + (j : ℕ)) M))
    (hdensity : ∃ (q : ℝ≥0) (K : ℝ≥0∞), K < ⊤
        ∧ (q : ℝ) < (minAdm (redChain (t + (j : ℕ)) M) : ℝ) / 2
        ∧ satFrontIntegrand M (t + (j : ℕ)) κ ε (min (M 0 - t) (M 1 - t)) j c'
            ≤ K * routeMLayerBoxIntegral (redChain (t + (j : ℕ)) M) (q : ℝ) 1) :
    shellSpineIntegrand M (t + (j : ℕ)) κ ε (min (M 0 - t) (M 1 - t)) j c' < ⊤ := by
  obtain ⟨q, K, hK, hq_hi, hdens⟩ := hdensity
  have ha0 : M 0 - (t + (j : ℕ)) = 0 := by omega
  have hbox : routeMLayerBoxIntegral (redChain (t + (j : ℕ)) M) (q : ℝ) 1 < ⊤ := hIH q hq_hi
  calc shellSpineIntegrand M (t + (j : ℕ)) κ ε (min (M 0 - t) (M 1 - t)) j c'
      ≤ satFrontIntegrand M (t + (j : ℕ)) κ ε (min (M 0 - t) (M 1 - t)) j c' :=
        shellSpine_le_satFront M (t + (j : ℕ)) κ ε (min (M 0 - t) (M 1 - t)) j c' ha0
    _ ≤ K * routeMLayerBoxIntegral (redChain (t + (j : ℕ)) M) (q : ℝ) 1 := hdens
    _ < ⊤ := ENNReal.mul_lt_top hK hbox

/-! ## The `b = 0` mirror collapse (output-corank; skeleton deferred)

The transpose-dual corner `M₁ < M₀` (cut `u = min(M₀,M₁) = M₁`, so `b = M₁ − u = 0`, `a = M₀ − u > 0`).
Here `Q_inr = Q.submatrix Sum.inr id` has EMPTY ROWS (`Fin b = Fin 0`), so the empty-MIDDLE products
`B₁₂·Q_inr` and `Γ·Q_inr` vanish, leaving BOTH `frobSq` terms — `frobSq(P·Q_inl) + frobSq(C·Q_inl)`
(the vertical stack `frobSq([P;C]·Q_inl)`). This is STRUCTURALLY different from `a = 0` (where the second
`frobSq` VANISHES). The front factor `[P;C]` is `M₀×M₁` TALL, full COLUMN rank — an INJECTIVE map
`A₀ ↦ [P;C]·A₀`, so its pushforward is SINGULAR on a proper subvariety (NO abs-continuous density) and the
`C` output rows are a genuine separate high-codim OUTPUT charge — NOT the surjective/density reduction of
`a = 0`. Consequently the `b = 0` reduced-chain target is `redChain (M 0) M` (leading `M₀ = max`), not
`redChain u M`. The reduction skeleton (`saturatedShell_lt_top_b`) is DEFERRED pending the corner-frontier
mechanism verdict; the collapse below is proved sorry-free and reusable regardless. -/

/-- **`freedSchurLoss` at `b = 0` (empty corank columns).** When the corank column index `Fin b` is empty,
the empty-middle products `B₁₂·Q_inr` and `Γ·Q_inr` vanish, so the freed loss is
`frobSq(P·Q_inl) + frobSq(C·Q_inl)` — both terms, `Γ`-free. -/
theorem freedSchurLoss_of_isEmpty_b {t a b q : ℕ} (hbE : IsEmpty (Fin b))
    (x : SJOuter t a b) (Γ : Fin a → Fin b → ℝ) (Q : Matrix (Fin t ⊕ Fin b) (Fin q) ℝ) :
    freedSchurLoss x Γ Q
      = frobSq (Matrix.of x.1.1 * Q.submatrix Sum.inl id)
        + frobSq (Matrix.of x.2 * Q.submatrix Sum.inl id) := by
  haveI := hbE
  have hB : (Matrix.of x.1.1)⁻¹ * Matrix.of x.1.2 * Q.submatrix Sum.inr id = 0 := by
    ext i k; simp [Matrix.mul_apply, Finset.univ_eq_empty]
  have hG : Matrix.of Γ * Q.submatrix Sum.inr id = 0 := by
    ext i k; simp [Matrix.mul_apply, Finset.univ_eq_empty]
  rw [freedSchurLoss, hB, hG]
  simp only [add_zero]

/-- **The `b = 0`-collapsed front integrand.** The shell integrand with the (empty-column) corank block `Γ`
integrated out; the surviving loss is the vertical-stack pivot+corank energy
`(frobSq(P·Q_inl) + frobSq(C·Q_inl))^{−c'}` over the shell-restricted `A'` and the front block `x`. -/
noncomputable def satFrontIntegrand_b (M : Fin (L + 1 + 1 + 1) → ℕ) (u : ℕ)
    (κ : Fin u ↪ Fin (M 1)) (ε : ℝ) (r : ℕ) (jf : Fin (r + 1)) (c' : ℝ) : ℝ≥0∞ :=
  ∫⁻ A' in paramsBoxM (tailChain M) 1
      ∩ {A' | prod (tailChain M) A' ∈ singularShell ε r jf},
    ∫⁻ x in outerDom u (M 0 - u) (M 1 - u) 1,
      ENNReal.ofReal
        ((frobSq (Matrix.of x.1.1
            * ((prod (tailChain M) A').submatrix (blockSplitEquiv κ) id).submatrix Sum.inl id)
          + frobSq (Matrix.of x.2
            * ((prod (tailChain M) A').submatrix (blockSplitEquiv κ) id).submatrix Sum.inl id))
          ^ (-c'))

/-- **The `b = 0` collapse domination.** When `M₁ − u = 0`, the shell integrand is bounded by the
`b = 0`-collapsed front integrand: the `∫⁻ Γ`-integral runs over the singleton space
`Fin (M₀−u) → Fin 0 → ℝ` (a probability measure — the inner empty-column factor is `dirac`), and the
integrand is `Γ`-independent after the empty-middle products drop. -/
theorem shellSpine_le_satFront_b (M : Fin (L + 1 + 1 + 1) → ℕ) (u : ℕ)
    (κ : Fin u ↪ Fin (M 1)) (ε : ℝ) (r : ℕ) (jf : Fin (r + 1)) (c' : ℝ)
    (hb0 : M 1 - u = 0) :
    shellSpineIntegrand M u κ ε r jf c' ≤ satFrontIntegrand_b M u κ ε r jf c' := by
  haveI hbE : IsEmpty (Fin (M 1 - u)) := by rw [hb0]; infer_instance
  haveI hInnerProb : IsProbabilityMeasure (volume : Measure (Fin (M 1 - u) → ℝ)) := by
    rw [Measure.volume_pi_eq_dirac]; infer_instance
  haveI hProb : IsProbabilityMeasure
      (volume : Measure (Fin (M 0 - u) → Fin (M 1 - u) → ℝ)) := inferInstance
  rw [shellSpineIntegrand, satFrontIntegrand_b]
  refine lintegral_mono (fun A' => ?_)
  refine lintegral_mono (fun x => ?_)
  set Q := (prod (tailChain M) A').submatrix (blockSplitEquiv κ) id with hQ
  have hfl : ∀ Γ : Fin (M 0 - u) → Fin (M 1 - u) → ℝ, freedSchurLoss x Γ Q
      = frobSq (Matrix.of x.1.1 * Q.submatrix Sum.inl id)
        + frobSq (Matrix.of x.2 * Q.submatrix Sum.inl id) :=
    fun Γ => freedSchurLoss_of_isEmpty_b hbE x Γ Q
  calc ∫⁻ Γ in {Γ : Fin (M 0 - u) → Fin (M 1 - u) → ℝ |
          Γ + schurShift x ∈ genBox (Fin (M 0 - u)) (Fin (M 1 - u)) 1},
          ENNReal.ofReal (freedSchurLoss x Γ Q ^ (-c'))
      = ∫⁻ _Γ in {Γ : Fin (M 0 - u) → Fin (M 1 - u) → ℝ |
          Γ + schurShift x ∈ genBox (Fin (M 0 - u)) (Fin (M 1 - u)) 1},
          ENNReal.ofReal ((frobSq (Matrix.of x.1.1 * Q.submatrix Sum.inl id)
            + frobSq (Matrix.of x.2 * Q.submatrix Sum.inl id)) ^ (-c')) :=
        lintegral_congr (fun Γ => by rw [hfl Γ])
    _ = ENNReal.ofReal ((frobSq (Matrix.of x.1.1 * Q.submatrix Sum.inl id)
            + frobSq (Matrix.of x.2 * Q.submatrix Sum.inl id)) ^ (-c'))
          * volume {Γ : Fin (M 0 - u) → Fin (M 1 - u) → ℝ |
              Γ + schurShift x ∈ genBox (Fin (M 0 - u)) (Fin (M 1 - u)) 1} :=
        setLIntegral_const _ _
    _ ≤ ENNReal.ofReal ((frobSq (Matrix.of x.1.1 * Q.submatrix Sum.inl id)
            + frobSq (Matrix.of x.2 * Q.submatrix Sum.inl id)) ^ (-c')) * 1 := by
        gcongr
        exact le_trans (measure_mono (Set.subset_univ _)) (le_of_eq measure_univ)
    _ = ENNReal.ofReal ((frobSq (Matrix.of x.1.1 * Q.submatrix Sum.inl id)
            + frobSq (Matrix.of x.2 * Q.submatrix Sum.inl id)) ^ (-c')) :=
        mul_one _

end DLNFibre.DLN.RLCT
