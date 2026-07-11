import DLNFibre.DLN.RLCT.Validate.RouteMSJLeafRayleigh
import DLNFibre.DLN.RLCT.Validate.RouteMSJCorankResidual
import DLNFibre.DLN.RLCT.Validate.RouteMSJGoodLoss
import DLNFibre.DLN.RLCT.Foundations.S1RadialMorse

/-!
# `DLNFibre.DLN.RLCT.Validate.RouteMSJLeafFinite` — the route-A leaf finiteness (`DecoratedBaseHyp` loss part)

**Thread `genm-sj5-descent`, route-A `DecoratedBaseHyp` completion.** Composes the banked route-A core
(`RouteMSJLeafRayleigh`: the Rayleigh matrix bound `c·frobSq Γ ≤ frobSq (Γ·Z)`) with the free-`Γ` Morse
to close the corank leaf integral:

    ∫_{Γ ∈ matBox a n T} (frobSq (Γ·Z))^{−c'} dΓ  < ⊤   for  c' < (a·n)/2 = ½·minAdm(base),

given the units-on-chart interface `Z·Zᵀ ≽ c·I` (`c > 0`, `#144`-supplied). Route (A) (cover Q4 PASS):
local Rayleigh, no `sjLoss_terminal`, no `(P)/(T)` gap.

* **`frobSq_mul_rpow_le_everywhere`** — the Rayleigh value majorant, valid EVERYWHERE (the `Γ = 0` point
  handled directly: both sides collapse to `0^{−c'}`), so the leaf integral dominates pointwise (no a.e.).
* **`frobSq_matBox_rpow_lt_top`** — the FREE-`Γ` Morse `∫_{matBox a n T}(frobSq Γ)^{−c'} < ⊤` for
  `c' < (a·n)/2`, via the banked measure-preserving flatten `eMatFlat` + `morseBox_sumSq_lt_top`.
* **`corankLeaf_rpow_lt_top`** — the leaf integral `< ⊤`: `lintegral_mono` by the everywhere majorant,
  `c^{−c'}` pulled out, closed by the free-`Γ` Morse.

Untracked (A2 co-audited with cover). Axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/

namespace DLNFibre.DLN.RLCT

open Matrix MeasureTheory
open scoped BigOperators ENNReal

/-- **The Rayleigh value majorant, valid everywhere.** `(frobSq (Γ·Z))^{−c'} ≤ c^{−c'}·(frobSq Γ)^{−c'}`
for all `Γ` (`0 ≤ c'`, `c > 0`, `Z·Zᵀ ≽ c·I`). On `Γ ≠ 0` it is the banked `frobSq_mul_rpow_le`
(`0 < frobSq Γ`); on `Γ = 0` both sides collapse to `0^{−c'}` (`= 0` for `c' > 0`, `= 1` at `c' = 0`). -/
theorem frobSq_mul_rpow_le_everywhere {a n D : ℕ} (Γ : Matrix (Fin a) (Fin n) ℝ)
    (Z : Matrix (Fin n) (Fin D) ℝ) (c : ℝ) (hc : 0 < c)
    (hZ : (Z * Zᵀ - c • (1 : Matrix (Fin n) (Fin n) ℝ)).PosSemidef) (c' : ℝ) (hc0 : 0 ≤ c') :
    (frobSq (Γ * Z)) ^ (-c') ≤ c ^ (-c') * (frobSq Γ) ^ (-c') := by
  by_cases hΓ : Γ = 0
  · subst hΓ
    rw [Matrix.zero_mul]
    have h0 : ∀ {p q : ℕ}, frobSq (0 : Matrix (Fin p) (Fin q) ℝ) = 0 := by
      intro p q; simp [frobSq]
    rw [h0, h0]
    rcases eq_or_lt_of_le hc0 with hc'0 | hc'pos
    · rw [← hc'0]; norm_num
    · rw [Real.zero_rpow (by linarith : -c' ≠ 0), mul_zero]
  · exact frobSq_mul_rpow_le Γ Z c hc hZ c' hc0 (frobSq_pos_of_ne_zero Γ hΓ)

/-- **The free-`Γ` Morse box integral is finite below `(a·n)/2`.** `∫_{matBox a n T}(frobSq Γ)^{−c'} < ⊤`
for `0 < a·n` and `c' < (a·n)/2`. The banked measure-preserving flatten `eMatFlat` sends `frobSq Γ` to the
flat sum of squares and `matBox a n T` to `morseBox (a·n) T`; `morseBox_sumSq_lt_top` closes it. -/
theorem frobSq_matBox_rpow_lt_top {a n : ℕ} (h : 0 < a * n) (c' : ℝ)
    (hc' : c' < (a * n : ℝ) / 2) (T : ℝ) (hT : 0 < T) :
    ∫⁻ Γ in matBox a n T, ENNReal.ofReal ((frobSq Γ) ^ (-c')) < ⊤ := by
  have hmp := measurePreserving_eMatFlat a n
  have hpremeas : MeasurableSet (eMatFlat a n ⁻¹' morseBox (a * n) T) :=
    (morseBox_measurableSet (a * n) T).preimage (eMatFlat a n).measurable
  have hrwfrob : ∀ Γ : Fin a → Fin n → ℝ, ENNReal.ofReal ((frobSq Γ) ^ (-c'))
      = (fun x : Fin (a * n) → ℝ => ENNReal.ofReal ((∑ i, (x i) ^ 2) ^ (-c'))) (eMatFlat a n Γ) :=
    fun Γ => by rw [frobSq_eq_flatSum a n Γ]
  rw [matBox_eq_eMatFlat_preimage a n T, setLIntegral_congr_fun hpremeas (fun Γ _ => hrwfrob Γ),
    hmp.setLIntegral_comp_preimage_emb (eMatFlat a n).measurableEmbedding
      (fun x => ENNReal.ofReal ((∑ i, (x i) ^ 2) ^ (-c'))) (morseBox (a * n) T)]
  obtain ⟨m, hm⟩ : ∃ m, a * n = m + 1 := ⟨a * n - 1, by omega⟩
  rw [hm]
  refine sumSqND_box_lt_top m T hT c' ?_
  have hcast : (↑m + 1 : ℝ) = (↑a * ↑n : ℝ) := by rw [← Nat.cast_mul, hm]; push_cast; ring
  rw [hcast]; exact hc'

/-- **The route-A corank leaf integral is finite (the `DecoratedBaseHyp` loss part).** Given the
units-on-chart interface `Z·Zᵀ ≽ c·I` (`c > 0`, `#144`-supplied), `∫_{matBox a n T}(frobSq (Γ·Z))^{−c'} < ⊤`
for `c' < (a·n)/2 = ½·minAdm(base)`. The everywhere Rayleigh majorant dominates pointwise by
`c^{−c'}·(frobSq Γ)^{−c'}`; `c^{−c'}` pulls out; the free-`Γ` Morse `frobSq_matBox_rpow_lt_top` closes it. -/
theorem corankLeaf_rpow_lt_top {a n D : ℕ} (h : 0 < a * n) (Z : Matrix (Fin n) (Fin D) ℝ) (c : ℝ)
    (hc : 0 < c) (hZ : (Z * Zᵀ - c • (1 : Matrix (Fin n) (Fin n) ℝ)).PosSemidef)
    (c' : ℝ) (hc0 : 0 ≤ c') (hc' : c' < (a * n : ℝ) / 2) (T : ℝ) (hT : 0 < T) :
    ∫⁻ Γ in matBox a n T, ENNReal.ofReal ((frobSq (rmatMul Γ Z)) ^ (-c')) < ⊤ := by
  have hmaj : ∀ Γ : Fin a → Fin n → ℝ,
      ENNReal.ofReal ((frobSq (rmatMul Γ Z)) ^ (-c'))
        ≤ ENNReal.ofReal (c ^ (-c')) * ENNReal.ofReal ((frobSq Γ) ^ (-c')) := by
    intro Γ
    rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hc.le _)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hbridge : rmatMul Γ Z = Matrix.of Γ * Z := by
      funext i j; simp [rmatMul, Matrix.mul_apply]
    rw [hbridge]
    exact frobSq_mul_rpow_le_everywhere (Matrix.of Γ) Z c hc hZ c' hc0
  calc ∫⁻ Γ in matBox a n T, ENNReal.ofReal ((frobSq (rmatMul Γ Z)) ^ (-c'))
      ≤ ∫⁻ Γ in matBox a n T,
          ENNReal.ofReal (c ^ (-c')) * ENNReal.ofReal ((frobSq Γ) ^ (-c')) :=
        lintegral_mono hmaj
    _ = ENNReal.ofReal (c ^ (-c'))
          * ∫⁻ Γ in matBox a n T, ENNReal.ofReal ((frobSq Γ) ^ (-c')) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top (frobSq_matBox_rpow_lt_top h c' hc' T hT)

end DLNFibre.DLN.RLCT
