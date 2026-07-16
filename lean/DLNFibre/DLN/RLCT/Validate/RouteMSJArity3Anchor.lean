import DLNFibre.DLN.RLCT.Validate.RouteMSJStratumRadial
import DLNFibre.DLN.RLCT.Validate.RouteMSJCornerComparator

set_option linter.style.longLine false

/-!
# `RouteMSJArity3Anchor` — the arity-3 (L=0) anchor of the `deeperFlag_shell_le` recursion

**Thread `genm-arch1asm` (aoyagi-full Stage 2).** The base case of the (□)-discharge recursion. At `L = 0`
the deep factor is trivial (`deeperFlagZdeep M u = I_{M₂}`, `det⁺(I) = 1`), so the front-charge form equals
the undecorated object and the coupled incidence-chart resolution reassembles the front-parameter-box
integral of `frontChargeIntegrand` onto the reduced-chain `cornerComparator (u, M₂) ![1] ![u·M₂−1]`.

**Exact spec:** `genm-reassembly/reassembly-cert.md §3.1` (commit `a25091d35`). The comparator RHS monomial
exponent is `|v₀|^{minAdm(M')−1−2q}` (SINGLE, not doubled) — the Jacobian exponent `jc₀ = minAdm(M')−1`
lives in `.jac`, the `|v₀|²` in `decLoss`.

## What lands here (this file)

* **`cornerComparator_integral_eq`** — the exact computation of the reduced comparator's `SJDecoration.integral`
  (piece (6)'s RHS shape): for the single-radial choice `k ≡ ![1]`, `jac = ![jc]`,

      cornerComparator M' ![1] ![jc] .integral q
        = ∫_{z ∈ paramsBoxM M' 1} ∫_{u ∈ unitBox 1}
            ofReal( |u₀|^{jc} · (|u₀|² · frobSq (prod M' z))^{−q} ).

  Unfolds `SJDecoration.integral` + `cornerComparator_decLoss` (the clean reduced-product loss
  `commonDivisor² · frobSq (prod M')`) + the uniform-support `commonDivisor (≡![1]) u = |u₀|`.

## What is HELD (the coupled incidence-chart resolution — pieces (2)/(3')/(5)/(6))

The top-level anchor obligation (the base case of the `deeperFlag_shell_le` recursion) is the finiteness

    ∫_p frontChargeIntegrand M u c' p < ⊤     (`p ∈ paramsBoxM (redChain u M) 1 ×ˢ matBox (M₁−u) M₂ 1`),

for `M : Fin (0+1+1+1)` (L=0), `u ≤ min(M₀,M₁)`, the scope `(M₀−u)+(M₁−u) ≤ M₂`, and `c' < carrierThreshold M`.
It is TRUE for `L = 0` (reassembly-cert `§Verdict A`, 332/332 in-scope cuts verified): `deeperFlagZdeep M u
= I_{M₂}`, so `Q_b = A_cor` free and `Q_p = A'₀`, and the coupled front-charge box integral reassembles onto
`cornerComparator (u, M₂) ![1] ![u·M₂−1]`. Its proof is the coupled `(A'₀, A_cor, x)`-integral CoV mountain
(the [pending] steps 3/4/5 of `RouteMSJIncidenceAssembly`):

* **(2)** the `A_cor` `b`-minor determinantal atlas + per-chart CoV chain (charge factor `det_chartGram`
  → `Q_p`-shear `W = Q_p·N` → front `B`-shear → `H̃`-completion; net `|det D|^{M₂−b−a−u}`, integrable ⟺
  `a+b ≤ M₂`). The charge-Wishart finiteness core is BANKED (`detGram_lintegral_box_lt_top`,
  `strongBlock_lintegral_lt_top`, `det_chartGram`, `lintegral_comp_mulLeftₚ`, `chart5_bigcell_cov`); the
  CONNECTIVE CoV chain resolving the coupled front loss is the open work (the largest piece).
* **(3')** the ℓ=0 two-block corner (`twoBlock_radial_le` BANKED; the SVD spectral bound
  `‖YW‖² ≥ (‖W‖²/min(u,d))·‖Y e₁‖²` is the open, HIGH-FRICTION spectral piece — needs a spectral specialist).
* **(5)** the finite-cover gluing over the `(ℓ, s, b-minor)` index (`lintegral_lt_top_of_finite_cover`
  BANKED; the atlas-specific coverage is the open work).
* **(6)** the top-level reassembly onto the comparator, whose RHS shape is computed by
  `cornerComparator_integral_eq{,_single}` below (the descent gate `minAdm_le_ab_add_uM2` BANKED). The
  per-stratum radial finiteness is BANKED (`single_block_stratum_lt_top` / `stratum_corner_lt_top`).

This file lands the comparator-side RHS computation (piece (6)); the coupled resolution is tracked on tide
branch `genm-arch1asm` and reported to the controller.

Axiom target `[propext, Classical.choice, Quot.sound]`.
-/

namespace DLNFibre.DLN.RLCT

open Matrix MeasureTheory Set
open scoped ENNReal BigOperators

variable {L : ℕ}

/-- **The exact computation of the reduced comparator's integral (piece (6) RHS shape).** For the
single-radial comparator `cornerComparator M' ![1] ![jc]`, the decorated box integral is the double
integral over the reduced params `z` (the box `paramsBoxM M' 1`) and the radial coordinate `u₀ ∈ [0,1]`
(the `unitBox 1`) of `|u₀|^{jc} · (|u₀|² · frobSq (prod M' z))^{−q}`. Unfolds `SJDecoration.integral`,
substitutes `cornerComparator_decLoss` (loss `= commonDivisor² · frobSq (prod M')`) and the
`k ≡ ![1]` common divisor `commonDivisor (≡![1]) u = |u 0|`, and collapses the `Fin 1` Jacobian
product `∏ ℓ, |u ℓ|^{![jc] ℓ} = |u 0|^{jc}`. -/
theorem cornerComparator_integral_eq (M' : Fin (L + 1 + 1) → ℕ) (jc : ℕ) (q : ℝ)
    (i₀ : Fin (M' 0) × Fin (M' (Fin.last (L + 1)))) :
    (cornerComparator M' (![1] : Fin 1 → ℕ) (![jc] : Fin 1 → ℕ)).integral q
      = ∫⁻ z in paramsBoxM M' 1, ∫⁻ u in unitBox 1,
          ENNReal.ofReal (|u 0| ^ jc * (|u 0| ^ 2 * frobSq (prod M' z)) ^ (-q)) := by
  letI := (cornerComparator M' (![1] : Fin 1 → ℕ) (![jc] : Fin 1 → ℕ)).fι
  letI := (cornerComparator M' (![1] : Fin 1 → ℕ) (![jc] : Fin 1 → ℕ)).fν
  haveI : Nonempty (cornerComparator M' (![1] : Fin 1 → ℕ) (![jc] : Fin 1 → ℕ)).ι := ⟨i₀⟩
  -- The common divisor at `k ≡ ![1]`: `commonDivisor supp u = |u 0|`.
  have hcd : ∀ u : Fin 1 → ℝ,
      commonDivisor (cornerComparator M' (![1] : Fin 1 → ℕ) (![jc] : Fin 1 → ℕ)).carrier.supp u
        = |u 0| := by
    intro u
    have hs := cornerComparator_sharedDivisorExp M' (![1] : Fin 1 → ℕ) (![jc] : Fin 1 → ℕ) i₀
    unfold commonDivisor
    rw [hs]
    change (∏ x : Fin 1, |u x| ^ (![1] : Fin 1 → ℕ) x) = |u 0|
    rw [Fin.prod_univ_one]
    simp
  -- `SJDecoration.integral` unfolds to the concrete double integral (`.d = 1`, `.jac = ![jc]`,
  -- `.dom = paramsBoxM M' 1`, `.mZ` the standard measure — all `rfl`).
  change (∫⁻ z in paramsBoxM M' 1, ∫⁻ u in unitBox 1,
      ENNReal.ofReal ((∏ ℓ : Fin 1, |u ℓ| ^ ((![jc] : Fin 1 → ℕ) ℓ))
        * ((cornerComparator M' (![1] : Fin 1 → ℕ) (![jc] : Fin 1 → ℕ)).decLoss u z) ^ (-q)))
    = ∫⁻ z in paramsBoxM M' 1, ∫⁻ u in unitBox 1,
        ENNReal.ofReal (|u 0| ^ jc * (|u 0| ^ 2 * frobSq (prod M' z)) ^ (-q))
  refine lintegral_congr (fun z => lintegral_congr (fun u => ?_))
  congr 1
  rw [Fin.prod_univ_one, Matrix.cons_val_zero,
    cornerComparator_decLoss M' (![1] : Fin 1 → ℕ) (![jc] : Fin 1 → ℕ) i₀ u z, hcd u]

/-- **The reduced comparator's integral in the SINGLE-exponent form (cert §1's `|v₀|^{jc−2q}` shape).**
Combining the Jacobian monomial `|v₀|^{jc}` with the `|v₀|²` inside the loss (a.e. off the null slice
`v₀ = 0`) gives the single radial monomial `|v₀|^{jc − 2q}` times the honest reduced-product loss
`frobSq (prod M')^{−q}`:

    cornerComparator M' ![jc'] .integral q
      = ∫_{z} ∫_{v₀ ∈ [0,1]}  ofReal( |v₀|^{jc − 2q} · frobSq (prod M' z)^{−q} ).

This is the shape whose `v₀`-radial converges iff `jc − 2q > −1`, i.e. `q < (jc+1)/2` — the clean IH
threshold `carrierThreshold M' = minAdm(M')/2` at `jc = minAdm(M') − 1` (cert §1). The combination
`|v₀|^{jc} · (|v₀|² · F)^{−q} = |v₀|^{jc − 2q} · F^{−q}` is `Real.rpow_add` on `|v₀| > 0`; the origin
`v₀ = 0` is a `volume`-null singleton of `unitBox 1`, dropped by `lintegral_congr_ae`. -/
theorem cornerComparator_integral_eq_single (M' : Fin (L + 1 + 1) → ℕ) (jc : ℕ) (q : ℝ)
    (i₀ : Fin (M' 0) × Fin (M' (Fin.last (L + 1)))) :
    (cornerComparator M' (![1] : Fin 1 → ℕ) (![jc] : Fin 1 → ℕ)).integral q
      = ∫⁻ z in paramsBoxM M' 1, ∫⁻ u in unitBox 1,
          ENNReal.ofReal (|u 0| ^ ((jc : ℝ) - 2 * q) * frobSq (prod M' z) ^ (-q)) := by
  rw [cornerComparator_integral_eq M' jc q i₀]
  refine lintegral_congr (fun z => lintegral_congr_ae ?_)
  -- a.e. off the null slice `u 0 = 0`, combine the two `|u 0|` powers into a single rpow.
  have hane : ∀ᵐ u ∂(volume.restrict (unitBox 1)), (u 0 : ℝ) ≠ 0 := by
    refine ae_restrict_of_ae ?_
    have hset : {u : Fin 1 → ℝ | ¬ (u 0 ≠ 0)} = {(0 : Fin 1 → ℝ)} := by
      ext u
      simp only [Set.mem_setOf_eq, not_not, Set.mem_singleton_iff]
      constructor
      · intro h; funext i; fin_cases i; exact h
      · intro h; rw [h]; rfl
    rw [ae_iff, hset]; exact measure_singleton _
  filter_upwards [hane] with u hu
  set t := |u 0| with ht
  have htpos : 0 < t := abs_pos.mpr hu
  have hFnn : (0 : ℝ) ≤ frobSq (prod M' z) := frobSq_nonneg _
  congr 1
  rw [Real.mul_rpow (by positivity) hFnn, ← Real.rpow_natCast t jc,
    ← Real.rpow_natCast t 2, ← Real.rpow_mul htpos.le, ← mul_assoc, ← Real.rpow_add htpos,
    show (jc : ℝ) + ((2 : ℕ) : ℝ) * -q = (jc : ℝ) - 2 * q from by push_cast; ring]

end DLNFibre.DLN.RLCT
