import DLNFibre.DLN.RLCT.Validate.RouteMSchurDirectMorseP
import DLNFibre.DLN.RLCT.Validate.RouteMSchurThresholdP

/-!
# `DLNFibre.DLN.RLCT.Validate.RouteMSchurCapAP` — the `Fin p` cap-A carve leaf bricks

The recursion-facing leaf bricks for the cap-A (interior-stratum) carve of `schurCoreP_capA`, generalised
`4 → p` from `RouteMSchurFiring`'s `coreSchurGenVal` / `coreSchurGenVal_lt_top` /
`schurResidG_translate_le`. These are self-contained (no N2b split, no `zEG`): the lower-corank free core
value, its finiteness from the abstract IH at width `p`, and the shift-uniform translate-domination of the
shifted residual into the IH box. The full cap-A carve (`innerSGenCarveP_le` + `schurRatioResidGenP_mid` +
the dispatch) stands on these.

These carry the threshold at width `p`: the lower IH is `SchurLowerIH p (schurLambdaP p) r`, and the
shifted residual closes below `schurLambdaP p (r - 1)`.
-/

open MeasureTheory Set
open scoped ENNReal BigOperators
namespace DLNFibre.DLN.RLCT

/-- **The `Fin p` lower-corank free core value** (`4 → p` of `coreSchurGenVal`): the corank-`m` free
two-matrix box integral at exponent `c''`, radius `Kr`. The value the cap-A carve's shifted residual is
dominated into. -/
noncomputable def coreSchurGenValP (m p : ℕ) (c'' Kr : ℝ) : ℝ≥0∞ :=
  ∫⁻ Δ in matBox m m Kr, ∫⁻ S in matBox m p Kr,
    ENNReal.ofReal ((frobSq (rmatMul Δ S)) ^ (-c''))

/-- `coreSchurGenValP (r−1) p c'' Kr < ⊤` for `0 < c'' < schurLambdaP p (r−1)`, `0 < Kr`, `r ≥ 3` —
exactly `SchurCore p (r−1) c'' Kr` from the abstract width-`p` IH (at `j = 1`). The `4 → p` of
`coreSchurGenVal_lt_top`. -/
theorem coreSchurGenValP_lt_top (r p : ℕ) (hr : 3 ≤ r)
    (hIH : SchurLowerIH p (schurLambdaP p) r)
    (c'' : ℝ) (hc0 : 0 < c'') (hclam : c'' < schurLambdaP p (r - 1)) (Kr : ℝ) (hKr : 0 < Kr) :
    coreSchurGenValP (r - 1) p c'' Kr < ⊤ := by
  have hcore : SchurCore p (r - 1) c'' Kr :=
    hIH 1 (le_refl 1) (by omega) c'' hc0 (by simpa using hclam) Kr hKr
  rwa [SchurCore] at hcore

/-- **The `Fin p` shift-uniform residual `_le` bound** (`4 → p` of `schurResidG_translate_le`). For a
fixed shift `Sh : Fin (r−1) → Fin (r−1) → ℝ` with `|Sh| ≤ B`, the shifted corank-`(r−1)` core integral
is `≤ coreSchurGenValP (r−1) p c'' (K+B)`, a bound INDEPENDENT of `Sh` (only the radius `K+B` records the
shift's size). Same chain: `S`-monotone enlarge `K → K+B`, then translate `Δ ↦ Δ − Sh` into radius
`K+B` (`matBoxSq_translate_le`). -/
theorem schurResidGP_translate_le (r p : ℕ) (hr : 3 ≤ r)
    (Sh : Fin (r - 1) → Fin (r - 1) → ℝ) (B : ℝ) (hB : ∀ i j, |Sh i j| ≤ B)
    (c'' : ℝ) (K : ℝ) :
    (∫⁻ Δ in matBox (r - 1) (r - 1) K, ∫⁻ S in matBox (r - 1) p K,
        ENNReal.ofReal ((frobSq (rmatMul (fun i j => Δ i j - Sh i j) S)) ^ (-c'')))
      ≤ coreSchurGenValP (r - 1) p c'' (K + B) := by
  have hB0 : 0 ≤ B := le_trans (abs_nonneg _) (hB ⟨0, by omega⟩ ⟨0, by omega⟩)
  set g : (Fin (r - 1) → Fin (r - 1) → ℝ) → ℝ≥0∞ := fun Δ =>
    ∫⁻ S in matBox (r - 1) p (K + B),
      ENNReal.ofReal ((frobSq (rmatMul Δ S)) ^ (-c'')) with hg
  have hSsub : matBox (r - 1) p K ⊆ matBox (r - 1) p (K + B) := by
    intro X hX i k; have := Set.mem_Icc.1 (hX i k); rw [Set.mem_Icc]
    constructor <;> [linarith [this.1]; linarith [this.2]]
  have hle1 : ∀ Δ : Fin (r - 1) → Fin (r - 1) → ℝ,
      (∫⁻ S in matBox (r - 1) p K,
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
  have hsub : (fun Δ => Δ + (fun i j => -Sh i j)) '' (matBox (r - 1) (r - 1) K)
      ⊆ matBox (r - 1) (r - 1) (K + B) := by
    rintro Δ' ⟨Δ, hΔ, rfl⟩
    intro i j
    show -(K + B) ≤ Δ i j + (-Sh i j) ∧ Δ i j + (-Sh i j) ≤ K + B
    have hΔij := Set.mem_Icc.1 (hΔ i j)
    have hShij := abs_le.1 (hB i j)
    constructor <;> [linarith [hΔij.1, hShij.2]; linarith [hΔij.2, hShij.1]]
  refine le_trans (matBoxSq_translate_le (fun i j => -Sh i j) K (K + B) g hsub) (le_of_eq ?_)
  rw [coreSchurGenValP]

end DLNFibre.DLN.RLCT
