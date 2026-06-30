import DLNFibre.DLN.RLCT.Validate.RouteMSchurRectPos
import DLNFibre.DLN.RLCT.Validate.RouteMSchurFiring

/-!
# `DLNFibre.DLN.RLCT.Validate.RouteMSchurRectPeel` — the RECTANGULAR Morse peel + residual translate (3b-peel)

The asymmetric (`Δ : Fin a → Fin b` RECTANGULAR) generalisation of the square `Fin p`-width Morse peel +
residual translate (`RouteMSchurCapAP.coreSchurGenValP` / `schurResidGP_translate_le` +
`RouteMSchurCapACarveP.resolvedShiftRGP_le`, where the core matrix is square `Fin (r−1) → Fin (r−1)`).
The single change is the inner matrix shape `Fin (r−1) → Fin (r−1)` becoming `Fin a → Fin b` (the
rectangular Schur complement `Sc : (m−1)×(n−1)` after the N2b `t=1` peel — `a = m−1`, `b = n−1`), the
shift `Sh : Fin a → Fin b`, and the translate-enlarge box `matBox a b`.

* `coreSchurValRect a b p c'' Kr` — the lower-corank free RECTANGULAR core value (= `RectSchurCore a b p`).
* `matBoxRect_translate_le` — the rectangular matrix-box translate-enlarge (rectangular `matBoxSq_translate_le`).
* `schurResidRect_translate_le` — the shift-uniform translate-domination into `coreSchurValRect`.
* `resolvedShiftRRect_le` — the JOINT brick: the a.e. `Fin p` Morse peel at threshold `p/2`
  (`core_T_peel_le_aeG` on the shifted core, `> 0` a.e. by `frobSqShiftRect_ne_zero_ae`) + the translate
  into the `(m−1, n−1)` lower-IH box.

INDEPENDENT of the in-flight carve coordinate side: builds only on the LANDED substrate
(`core_T_peel_le_aeG` / `Cresid` from `RouteMSchurFiring` / `RadialResidualPower`, `matBox` /
`frobSq` / `rmatMul` from `MatMulFibre`) + the sibling 3b-pos `frobSqShiftRect_ne_zero_ae`. Needs NEITHER
`innerSRect_eq_norm` NOR `innerSGenCarveRect_le`.
-/

open MeasureTheory Set
open scoped ENNReal BigOperators
namespace DLNFibre.DLN.RLCT

/-! ## The rectangular lower-corank free core value -/

/-- **The rectangular lower-corank free core value.** `coreSchurValRect a b p c'' Kr := ∫_{Δ∈matBox a b Kr}
∫_{S∈matBox b p Kr} frobSq(Δ·S)^{−c''}` — the `Sh`-independent constant the shifted residual is bounded by
(the rectangular Schur complement is `a×b`, the bottom `S` block is `b×p`). The rectangular analog of
`coreSchurGenValP`; it is literally `RectSchurCore a b p c'' Kr`. -/
noncomputable def coreSchurValRect (a b p : ℕ) (c'' Kr : ℝ) : ℝ≥0∞ :=
  ∫⁻ Δ in matBox a b Kr, ∫⁻ S in matBox b p Kr,
    ENNReal.ofReal ((frobSq (rmatMul Δ S)) ^ (-c''))

/-! ## The rectangular matrix-box translate-enlarge -/

/-- **Matrix-box translate-enlarge (rectangular `a×b`).** `∫_{Δ∈matBox a b K} f(Δ + Sh) ≤
∫_{Δ'∈matBox a b Kg} f Δ'` when `(·+Sh)''(matBox a b K) ⊆ matBox a b Kg`. Measure-preserving matrix-space
translation (`measurePreserving_add_right`) + `lintegral_mono_set`. Rectangular `matBoxSq_translate_le`. -/
theorem matBoxRect_translate_le {a b : ℕ} (Sh : Fin a → Fin b → ℝ) (K Kg : ℝ)
    (f : (Fin a → Fin b → ℝ) → ℝ≥0∞)
    (hsub : (fun Δ => Δ + Sh) '' (matBox a b K) ⊆ matBox a b Kg) :
    (∫⁻ Δ in matBox a b K, f (Δ + Sh)) ≤ ∫⁻ Δ' in matBox a b Kg, f Δ' := by
  set τ : (Fin a → Fin b → ℝ) → (Fin a → Fin b → ℝ) := fun Δ => Δ + Sh with hτ
  have hmp : MeasurePreserving τ volume volume := measurePreserving_add_right volume Sh
  have hemb : MeasurableEmbedding τ := (Homeomorph.addRight Sh).measurableEmbedding
  have h1 : (∫⁻ Δ in matBox a b K, f (τ Δ)) = ∫⁻ Δ' in τ '' (matBox a b K), f Δ' := by
    rw [← hmp.setLIntegral_comp_preimage_emb hemb f (τ '' (matBox a b K)),
      Set.preimage_image_eq (matBox a b K) hemb.injective]
  calc (∫⁻ Δ in matBox a b K, f (Δ + Sh)) = ∫⁻ Δ' in τ '' (matBox a b K), f Δ' := h1
    _ ≤ ∫⁻ Δ' in matBox a b Kg, f Δ' := lintegral_mono_set hsub

/-! ## The shift-uniform residual translate-domination -/

/-- **The rectangular shift-uniform residual `_le` bound.** For a fixed rectangular shift
`Sh : Fin a → Fin b → ℝ` with `|Sh| ≤ B`, the shifted RECTANGULAR core integral is
`≤ coreSchurValRect a b p c'' (K+B)`, a bound INDEPENDENT of `Sh` (only the radius `K+B` records the
shift's size). Same chain as `schurResidGP_translate_le`: `S`-monotone enlarge `K → K+B`, then translate
`Δ ↦ Δ − Sh` into radius `K+B` (`matBoxRect_translate_le`). The rectangular analog. -/
theorem schurResidRect_translate_le (a b p : ℕ) (ha : 0 < a) (hb : 0 < b)
    (Sh : Fin a → Fin b → ℝ) (B : ℝ) (hB : ∀ i j, |Sh i j| ≤ B)
    (c'' : ℝ) (K : ℝ) :
    (∫⁻ Δ in matBox a b K, ∫⁻ S in matBox b p K,
        ENNReal.ofReal ((frobSq (rmatMul (fun i j => Δ i j - Sh i j) S)) ^ (-c'')))
      ≤ coreSchurValRect a b p c'' (K + B) := by
  -- a, b ≥ 1: `B ≥ |Sh 0 0| ≥ 0`
  have hB0 : 0 ≤ B := le_trans (abs_nonneg _) (hB ⟨0, ha⟩ ⟨0, hb⟩)
  set g : (Fin a → Fin b → ℝ) → ℝ≥0∞ := fun Δ =>
    ∫⁻ S in matBox b p (K + B),
      ENNReal.ofReal ((frobSq (rmatMul Δ S)) ^ (-c'')) with hg
  have hSsub : matBox b p K ⊆ matBox b p (K + B) := by
    intro X hX i k; have := Set.mem_Icc.1 (hX i k); rw [Set.mem_Icc]
    constructor <;> [linarith [this.1]; linarith [this.2]]
  have hle1 : ∀ Δ : Fin a → Fin b → ℝ,
      (∫⁻ S in matBox b p K,
          ENNReal.ofReal ((frobSq (rmatMul (fun i j => Δ i j - Sh i j) S)) ^ (-c'')))
        ≤ g (Δ + (fun i j => -Sh i j)) := by
    intro Δ
    have hmono := lintegral_mono_set (μ := volume) hSsub
      (f := fun S => ENNReal.ofReal ((frobSq (rmatMul (fun i j => Δ i j - Sh i j) S)) ^ (-c'')))
    refine le_trans hmono (le_of_eq ?_)
    have heqfun : (fun i j => Δ i j - Sh i j) = (Δ + (fun i j => -Sh i j)) := by
      funext i j; simp [Pi.add_apply, sub_eq_add_neg]
    rw [hg]; refine lintegral_congr (fun S => ?_); rw [heqfun]
  refine le_trans (lintegral_mono hle1) ?_
  have hsub : (fun Δ => Δ + (fun i j => -Sh i j)) '' (matBox a b K)
      ⊆ matBox a b (K + B) := by
    rintro Δ' ⟨Δ, hΔ, rfl⟩
    intro i j
    show -(K + B) ≤ Δ i j + (-Sh i j) ∧ Δ i j + (-Sh i j) ≤ K + B
    have hΔij := Set.mem_Icc.1 (hΔ i j)
    have hShij := abs_le.1 (hB i j)
    constructor <;> [linarith [hΔij.1, hShij.2]; linarith [hΔij.2, hShij.1]]
  refine le_trans (matBoxRect_translate_le (fun i j => -Sh i j) K (K + B) g hsub) (le_of_eq ?_)
  rw [coreSchurValRect]

/-! ## The SHIFTED resolved-form UNIFORM `_le` bound (the JOINT brick, rectangular) -/

/-- **The SHIFTED resolved-form UNIFORM `_le` bound (rectangular `a×b`).** For a fixed rectangular shift
`Sh : Fin a → Fin b → ℝ` with `|Sh i j| ≤ B`, `p/2 < c'`, every `K > 0`,
`∫_{Δ∈matBox a b K}∫_{S∈matBox b p K}∫_{T∈morseBox p K}(∑T² + frobSq((Δ−Sh)·S))^{−c'}` is bounded by
`ofReal(Cresid p c') · coreSchurValRect a b p (c'−p/2) (K+B)` — INDEPENDENT of `Sh`. The `Fin p` Morse
`T`-peel (`core_T_peel_le_aeG`, `p = pm+1`, threshold `p/2`) on the shifted core (`> 0` a.e. by
`frobSqShiftRect_ne_zero_ae`) leaves the residual at `c'−p/2`, closed by `schurResidRect_translate_le`.
The rectangular analog of `resolvedShiftRGP_le` (`Δ` rows `a`, contraction `b`, residual `a×b`). -/
theorem resolvedShiftRRect_le (a b p : ℕ) (ha : 0 < a) (hb : 0 < b) (hp : 0 < p)
    (Sh : Fin a → Fin b → ℝ) (B : ℝ) (hB : ∀ i j, |Sh i j| ≤ B)
    (K : ℝ) (hK : 0 < K) (c' : ℝ) (hcp : (p : ℝ) / 2 < c') :
    (∫⁻ Δ in matBox a b K, ∫⁻ S in matBox b p K, ∫⁻ T in morseBox p K,
        ENNReal.ofReal ((∑ i, (T i) ^ 2
          + frobSq (rmatMul (fun x y => Δ x y - Sh x y) S)) ^ (-c')))
      ≤ ENNReal.ofReal (Cresid p c') * coreSchurValRect a b p (c' - (p : ℝ) / 2) (K + B) := by
  -- write `p = pm + 1` so the peel's `morseBox (pm+1)` / `(pm+1)/2` match `morseBox p` / `p/2` literally
  obtain ⟨pm, rfl⟩ : ∃ pm, p = pm + 1 := ⟨p - 1, by omega⟩
  set w : (Fin a → Fin b → ℝ) × (Fin b → Fin (pm + 1) → ℝ) → ℝ :=
    fun q => frobSq (rmatMul (fun x y => q.1 x y - Sh x y) q.2) with hwdef
  have hmeasT : Measurable (fun q : ((Fin a → Fin b → ℝ) × (Fin b → Fin (pm + 1) → ℝ))
      × (Fin (pm + 1) → ℝ) => ENNReal.ofReal ((∑ i, (q.2 i) ^ 2 + w q.1) ^ (-c'))) := by
    apply ENNReal.measurable_ofReal.comp
    apply Measurable.comp (g := fun t : ℝ => t ^ (-c')) (by fun_prop)
    show Measurable (fun q : ((Fin a → Fin b → ℝ) × (Fin b → Fin (pm + 1) → ℝ))
        × (Fin (pm + 1) → ℝ) =>
        (∑ i, (q.2 i) ^ 2 + frobSq (rmatMul (fun x y => q.1.1 x y - Sh x y) q.1.2)))
    unfold frobSq rmatMul; fun_prop
  -- Step 1: Tonelli ∫_Δ∫_S∫_T = ∫_{(Δ,S)}∫_T over the product box
  have hstep1 : ∫⁻ Δ in matBox a b K, ∫⁻ S in matBox b (pm + 1) K,
        ∫⁻ T in morseBox (pm + 1) K,
        ENNReal.ofReal ((∑ i, (T i) ^ 2 + frobSq (rmatMul (fun x y => Δ x y - Sh x y) S)) ^ (-c'))
      = ∫⁻ q in (matBox a b K ×ˢ matBox b (pm + 1) K),
          (∫⁻ T in morseBox (pm + 1) K,
          ENNReal.ofReal ((∑ i, (T i) ^ 2 + w q) ^ (-c'))) ∂volume := by
    rw [Measure.volume_eq_prod (Fin a → Fin b → ℝ) (Fin b → Fin (pm + 1) → ℝ),
      setLIntegral_prod _ (Measurable.lintegral_prod_right hmeasT).aemeasurable]
  rw [hstep1]
  -- Step 2: the a.e. T-peel (m = pm): bound by Cresid · ∫_{(Δ,S)} w^{−(c'−(pm+1)/2)}
  have hwpos : ∀ᵐ z ∂(volume.restrict
        (matBox a b K ×ˢ matBox b (pm + 1) K)), 0 < w z :=
    ae_restrict_of_ae (frobSqShiftRect_ne_zero_ae a b (pm + 1) ha hb hp Sh)
  have hpeel := core_T_peel_le_aeG (m := pm) (volume) c' (by exact_mod_cast hcp) K hK w
    (matBox a b K ×ˢ matBox b (pm + 1) K) hwpos
  refine le_trans hpeel ?_
  -- Step 3: the residual ∫_{(Δ,S)} w^{−(c'−(pm+1)/2)} = ∫_Δ∫_S frobSq((Δ−Sh)·S)^{−(c'−(pm+1)/2)}
  refine mul_le_mul_left' ?_ _
  have hmeasResid : Measurable
      (fun q : (Fin a → Fin b → ℝ) × (Fin b → Fin (pm + 1) → ℝ) =>
        ENNReal.ofReal ((w q) ^ (-(c' - (pm + 1 : ℝ) / 2)))) := by
    apply ENNReal.measurable_ofReal.comp
    apply Measurable.comp (g := fun t : ℝ => t ^ (-(c' - (pm + 1 : ℝ) / 2))) (by fun_prop)
    show Measurable (fun q : (Fin a → Fin b → ℝ) × (Fin b → Fin (pm + 1) → ℝ) =>
        frobSq (rmatMul (fun x y => q.1 x y - Sh x y) q.2))
    unfold frobSq rmatMul; fun_prop
  have hresid : (∫⁻ q in (matBox a b K ×ˢ matBox b (pm + 1) K),
        ENNReal.ofReal ((w q) ^ (-(c' - (pm + 1 : ℝ) / 2))))
      = ∫⁻ Δ in matBox a b K, ∫⁻ S in matBox b (pm + 1) K,
          ENNReal.ofReal ((frobSq (rmatMul (fun x y => Δ x y - Sh x y) S))
            ^ (-(c' - ((pm : ℝ) + 1) / 2))) := by
    rw [Measure.volume_eq_prod (Fin a → Fin b → ℝ) (Fin b → Fin (pm + 1) → ℝ),
      setLIntegral_prod _ hmeasResid.aemeasurable]
  rw [hresid]
  -- the residual exponent `c' − (pm+1)/2 = c' − p/2`; close by schurResidRect_translate_le
  have hcast : (c' - ((pm : ℝ) + 1) / 2) = (c' - ((pm + 1 : ℕ) : ℝ) / 2) := by push_cast; ring
  rw [hcast]
  exact schurResidRect_translate_le a b (pm + 1) ha hb Sh B hB (c' - ((pm + 1 : ℕ) : ℝ) / 2) K

end DLNFibre.DLN.RLCT
