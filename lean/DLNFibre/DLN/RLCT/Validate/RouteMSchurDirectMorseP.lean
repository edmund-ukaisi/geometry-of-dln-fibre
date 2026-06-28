import DLNFibre.DLN.RLCT.Validate.RouteMSchurFiring

/-!
# `DLNFibre.DLN.RLCT.Validate.RouteMSchurDirectMorseP` — the shared `Fin p` chart plumbing + cap-B branch

The output-width-`p` generalisation of the per-chart angular machinery (`RouteMSchurFiring`'s `Fin 4`
top-row identity / shear), used by BOTH the cap-B `directMorse` branch and the cap-A carve-peel branch of
`schurRecStep_p` (task #146). This file builds the SHARED `Fin p` plumbing first, then the cap-B branch.

The `Fin 4 → Fin p` swap in these lemmas is mechanical (the `4` is the S-column width, summed opaquely),
but it is genuinely load-bearing (Codex flagged the directMorse angular bound — a naive `frobSq(R·S) ≥
c₀·frobSq(S)` is FALSE, since `R` can annihilate `S`; the correct bound is the carve's own N2b one-pivot
Schur/Morse lower bound, with the residual term DROPPED in the cap-B regime).

## Shared plumbing
* `frobSqTopRowP_eq_shearP` — the top-row identity `frobSq(top row of R·S) = ∑_q (sheared top row)²`, the
  `Fin p` analog of `frobSqTopRow_eq_shear`. The pivot `R₀₀ = 1` makes the `j = 1` block read off `S₀ q`;
  the rest is the shear `S₀q + ∑_a R₀,₁₊ₐ · S₁₊ₐ,q`.
-/

open MeasureTheory Set
open scoped ENNReal BigOperators
namespace DLNFibre.DLN.RLCT

/-! ## Shared `Fin p` chart plumbing -/

/-- **The `Fin p` top-row identity** (`Fin p` analog of `frobSqTopRow_eq_shear`). For an angular matrix `R`
with pivot `R ⟨0⟩ ⟨0⟩ = 1`, the squared norm of the TOP ROW of `R·S` equals the sum over the `Fin p`
columns of the squared SHEARED entry `S₀q + ∑_a R₀,₁₊ₐ · S₁₊ₐ,q`. The `4 → p` swap is verbatim: the `p`
appears only as the opaque `∑ q : Fin p` column sum. -/
theorem frobSqTopRowP_eq_shearP (r p : ℕ) (hr : 3 ≤ r) (R : Fin r → Fin r → ℝ)
    (hpiv : R ⟨0, by omega⟩ ⟨0, by omega⟩ = 1) (S : Fin r → Fin p → ℝ) :
    frobSq (fun a : Fin 1 => rmatMul R S ⟨(a : ℕ), by omega⟩)
      = ∑ q, (S ⟨0, by omega⟩ q
          + ∑ a : Fin (r - 1), R ⟨0, by omega⟩ ⟨1 + (a : ℕ), by omega⟩ * S ⟨1 + (a : ℕ), by omega⟩ q) ^ 2 := by
  unfold frobSq
  rw [Fin.sum_univ_one]
  refine Finset.sum_congr rfl (fun q _ => ?_)
  congr 1
  show rmatMul R S ⟨0, by omega⟩ q = _
  unfold rmatMul
  rw [fin_sum_block_split 1 (show (1 : ℕ) ≤ r by omega) (fun k : Fin r => R ⟨0, by omega⟩ k * S k q)]
  congr 1
  · rw [Fin.sum_univ_one]
    have h0 : (⟨(0 : Fin 1), lt_of_lt_of_le (0 : Fin 1).2 (show (1:ℕ) ≤ r by omega)⟩ : Fin r)
        = ⟨0, by omega⟩ := rfl
    rw [h0, hpiv, one_mul]

/-- **The `Fin p` foundational shear** (`Fin p` analog of `stepShearG`). The top-row shear change of
variables on the `S`-box: translating the top row `S 0 ↦ T' = S 0 + b·S_bot` (per fixed lower block
`S_bot`) bounds the sheared integral by the product of the lower-block box and the enlarged `morseBox p`
(radius `(m+1)·T`, the shift `|∑_a b_a S_bot_a| ≤ m·T`). The `4 → p` swap is verbatim: `p` is the opaque
`S`-column width throughout (`Fin p`, `matBox _ p`, `morseBox p`, `lintegral_translate_leG p`, all
`p`-general). -/
theorem stepShearGP (m p : ℕ) (b : Fin m → ℝ) (hb : ∀ a, |b a| ≤ 1)
    (Sc : Matrix (Fin m) (Fin m) ℝ) (T : ℝ) (hT : 0 < T) (c' : ℝ) :
    (∫⁻ S in matBox (m + 1) p T,
        ENNReal.ofReal (((∑ q, (S 0 q + ∑ a, b a * S a.succ q) ^ 2)
          + frobSq (rmatMul Sc (fun a q => S a.succ q))) ^ (-c')))
      ≤ ∫⁻ S_bot in matBox m p T, ∫⁻ T' in morseBox p ((m + 1 : ℕ) * T),
          ENNReal.ofReal (((∑ q, (T' q) ^ 2) + frobSq (rmatMul Sc S_bot)) ^ (-c')) := by
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => Fin p → ℝ) 0 with he
  have hmp : MeasurePreserving e volume volume :=
    volume_preserving_piFinSuccAbove (fun _ : Fin (m + 1) => Fin p → ℝ) 0
  set H : (Fin p → ℝ) × (Fin m → Fin p → ℝ) → ℝ≥0∞ := fun q =>
    ENNReal.ofReal (((∑ qq, (q.1 qq + ∑ a, b a * q.2 a qq) ^ 2)
      + frobSq (rmatMul Sc q.2)) ^ (-c')) with hHdef
  have hHmeas : Measurable H := by
    rw [hHdef]
    apply ENNReal.measurable_ofReal.comp
    apply Measurable.comp (g := fun t : ℝ => t ^ (-c')) (by fun_prop)
    refine Measurable.add ?_ ?_
    · refine Finset.measurable_sum _ (fun qq _ => ?_)
      refine Measurable.pow_const ?_ 2
      have h0 : Measurable (fun q : (Fin p → ℝ) × (Fin m → Fin p → ℝ) => q.1 qq) :=
        (measurable_pi_apply qq).comp measurable_fst
      refine h0.add (Finset.measurable_sum _ (fun a _ => ?_))
      exact measurable_const.mul ((measurable_pi_apply qq).comp
        ((measurable_pi_apply a).comp measurable_snd))
    · unfold frobSq rmatMul
      refine Finset.measurable_sum _ (fun i _ => ?_)
      refine Finset.measurable_sum _ (fun j _ => ?_)
      refine Measurable.pow_const ?_ 2
      refine Finset.measurable_sum _ (fun k _ => ?_)
      exact measurable_const.mul ((measurable_pi_apply j).comp
        ((measurable_pi_apply k).comp measurable_snd))
  have hsplit : matBox (m + 1) p T
      = e ⁻¹' ((Set.univ.pi (fun _ : Fin p => Set.Icc (-T) T)) ×ˢ matBox m p T) := by
    ext S
    simp only [he, Set.mem_preimage, Set.mem_prod, matBox, Set.mem_setOf_eq, Set.mem_pi,
      Set.mem_univ, true_implies]
    constructor
    · intro h
      refine ⟨fun q => h 0 q, fun a q => h a.succ q⟩
    · rintro ⟨h1, h2⟩ i k
      rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i', rfl⟩
      · exact h1 k
      · exact h2 i' k
  have hLHS : (∫⁻ S in matBox (m + 1) p T,
      ENNReal.ofReal (((∑ q, (S 0 q + ∑ a, b a * S a.succ q) ^ 2)
        + frobSq (rmatMul Sc (fun a q => S a.succ q))) ^ (-c')))
      = ∫⁻ pq in ((Set.univ.pi (fun _ : Fin p => Set.Icc (-T) T)) ×ˢ matBox m p T), H pq := by
    rw [hsplit, ← hmp.setLIntegral_comp_preimage_emb e.measurableEmbedding H
        ((Set.univ.pi (fun _ : Fin p => Set.Icc (-T) T)) ×ˢ matBox m p T)]
    refine setLIntegral_congr_fun ?_ (fun S _ => rfl)
    exact e.measurable (MeasurableSet.prod
      (MeasurableSet.univ_pi (fun _ => measurableSet_Icc)) (matBox_measurableSet m p T))
  rw [hLHS, Measure.volume_eq_prod, setLIntegral_prod _ hHmeas.aemeasurable,
    lintegral_lintegral_swap hHmeas.aemeasurable]
  refine setLIntegral_mono_ae' (matBox_measurableSet m p T) (ae_of_all _ (fun S_bot hSbot => ?_))
  set shift : Fin p → ℝ := fun q => ∑ a, b a * S_bot a q with hshift
  set f : (Fin p → ℝ) → ℝ≥0∞ := fun T' =>
    ENNReal.ofReal (((∑ q, (T' q) ^ 2) + frobSq (rmatMul Sc S_bot)) ^ (-c')) with hf
  have hrw : ∀ S_top : Fin p → ℝ, H (S_top, S_bot) = f (S_top + shift) := by
    intro S_top; rw [hHdef, hf]; rfl
  rw [lintegral_congr hrw]
  refine lintegral_translate_leG p shift (Set.univ.pi (fun _ : Fin p => Set.Icc (-T) T))
    (morseBox p ((m + 1 : ℕ) * T)) f ?_
  rintro T' ⟨v, hv, rfl⟩
  simp only [morseBox, Set.mem_pi, Set.mem_univ, true_implies] at hv ⊢
  intro q
  have hvq := Set.mem_Icc.1 (hv q)
  have htermbd : ∀ a : Fin m, |b a * S_bot a q| ≤ T := by
    intro a
    rw [abs_mul]
    have hSa := Set.mem_Icc.1 (hSbot a q)
    calc |b a| * |S_bot a q| ≤ 1 * T :=
          mul_le_mul (hb a) (abs_le.2 hSa) (abs_nonneg _) (by norm_num)
      _ = T := by ring
  have hshiftbd : |shift q| ≤ (m : ℝ) * T := by
    rw [hshift]
    calc |∑ a, b a * S_bot a q| ≤ ∑ a, |b a * S_bot a q| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _a : Fin m, T := Finset.sum_le_sum (fun a _ => htermbd a)
      _ = (m : ℝ) * T := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [Set.mem_Icc, Pi.add_apply, hshift]
  have habs := abs_le.1 hshiftbd
  push_cast
  constructor <;> [nlinarith [hvq.1, habs.1, hT]; nlinarith [hvq.2, habs.2, hT]]

/-- **The `Fin p` row-indexed shear** (`Fin p` analog of `stepShearG_r`). Same as `stepShearGP` but with
the `Fin r` row indices `⟨0⟩` / `⟨1+a⟩` (the carve's native index form) instead of `0` / `a.succ`, via the
`(r−1)+1 = r` row-reindex MP. -/
theorem stepShearP_r (r p : ℕ) (hr : 3 ≤ r) (b : Fin (r - 1) → ℝ) (hb : ∀ a, |b a| ≤ 1)
    (Sc : Matrix (Fin (r - 1)) (Fin (r - 1)) ℝ) (T : ℝ) (hT : 0 < T) (c' : ℝ) :
    (∫⁻ S in matBox r p T,
        ENNReal.ofReal (((∑ q, (S ⟨0, by omega⟩ q + ∑ a, b a * S ⟨1 + (a : ℕ), by omega⟩ q) ^ 2)
          + frobSq (rmatMul Sc (fun a q => S ⟨1 + (a : ℕ), by omega⟩ q))) ^ (-c')))
      ≤ ∫⁻ S_bot in matBox (r - 1) p T, ∫⁻ T' in morseBox p ((r : ℕ) * T),
          ENNReal.ofReal (((∑ q, (T' q) ^ 2) + frobSq (rmatMul Sc S_bot)) ^ (-c')) := by
  have hrm : (r - 1) + 1 = r := Nat.sub_add_cancel (by omega)
  set er : Fin ((r - 1) + 1) ≃ Fin r := finCongr hrm with her
  set E := MeasurableEquiv.piCongrLeft (fun _ : Fin r => Fin p → ℝ) er with hE
  have hmp : MeasurePreserving E.symm volume volume :=
    (volume_measurePreserving_piCongrLeft (fun _ : Fin r => Fin p → ℝ) er).symm E
  have hpre : matBox r p T = E.symm ⁻¹' (matBox ((r - 1) + 1) p T) := by
    ext S
    simp only [Set.mem_preimage, matBox, Set.mem_setOf_eq]
    constructor
    · intro h i k; exact h (er i) k
    · intro h i k
      have := h (er.symm i) k
      rw [show E.symm S (er.symm i) k = S i k from by
        show S (er (er.symm i)) k = S i k; rw [Equiv.apply_symm_apply]] at this
      exact this
  set f : (Fin ((r - 1) + 1) → Fin p → ℝ) → ℝ≥0∞ := fun S =>
    ENNReal.ofReal (((∑ q, (S 0 q + ∑ a, b a * S a.succ q) ^ 2)
      + frobSq (rmatMul Sc (fun a q => S a.succ q))) ^ (-c')) with hf
  have hkey := hmp.setLIntegral_comp_preimage_emb E.symm.measurableEmbedding f
    (matBox ((r - 1) + 1) p T)
  rw [← hpre] at hkey
  have hLHSeq : (∫⁻ S in matBox r p T,
      ENNReal.ofReal (((∑ q, (S ⟨0, by omega⟩ q + ∑ a, b a * S ⟨1 + (a : ℕ), by omega⟩ q) ^ 2)
        + frobSq (rmatMul Sc (fun a q => S ⟨1 + (a : ℕ), by omega⟩ q))) ^ (-c')))
      = ∫⁻ S in matBox r p T, f (E.symm S) := by
    refine lintegral_congr (fun S => ?_)
    rw [hf]
    have hrow0 : E.symm S (0 : Fin ((r - 1) + 1)) = S ⟨0, by omega⟩ := by
      show S (er 0) = S ⟨0, by omega⟩; rfl
    have hrowsucc : ∀ a : Fin (r - 1), E.symm S a.succ = S ⟨1 + (a : ℕ), by omega⟩ := by
      intro a
      show S (er a.succ) = S ⟨1 + (a : ℕ), by omega⟩
      congr 1; apply Fin.ext; simp [her, Fin.succ]; omega
    simp only [hrow0, hrowsucc]
  rw [hLHSeq, hkey]
  have hshear := stepShearGP (r - 1) p b hb Sc T hT c'
  have hcast : (((r - 1) + 1 : ℕ) : ℝ) * T = ((r : ℕ) : ℝ) * T := by rw [hrm]
  rw [hcast] at hshear
  exact hshear

/-! ## The `Fin p` inner-S integrand (shared plumbing 3/3) -/

/-- **The `Fin p` inner-S integrand** (`Fin p` analog of `innerSGen`): the inner-`S` integral
`∫_{S∈matBox r p T} frobSq(RmatG·S)^{−c'}` over the output-width-`p` box. The angular matrix
`RmatG r pivot y` is `p`-FREE (it reshapes the `r×r` ratio chart); only the `S`-box width is `p`. -/
noncomputable def innerSGenP (r p : ℕ) (c' : ℝ) (T : ℝ) (pivot : Fin (r * r)) (y : Fin (r * r) → ℝ) :
    ℝ≥0∞ :=
  ∫⁻ S in matBox r p T, ENNReal.ofReal ((frobSq (rmatMul (RmatG r pivot y) S)) ^ (-c'))

/-- `innerSGenP r p c' T pivot` is measurable in `y` (the `Fin p` analog of `measurable_innerSGen`;
verbatim — `RmatG` is `p`-free, only the `S`-box width changes). -/
theorem measurable_innerSGenP (r p : ℕ) (c' : ℝ) (T : ℝ) (pivot : Fin (r * r)) :
    Measurable (innerSGenP r p c' T pivot) := by
  unfold innerSGenP
  apply Measurable.lintegral_prod_right (f := fun y S =>
    ENNReal.ofReal ((frobSq (rmatMul (RmatG r pivot y) S)) ^ (-c')))
  apply ENNReal.measurable_ofReal.comp
  apply Measurable.comp (g := fun t : ℝ => t ^ (-c')) (by fun_prop)
  unfold frobSq rmatMul
  apply Finset.measurable_sum; intro i _
  apply Finset.measurable_sum; intro j _
  apply Measurable.pow_const
  apply Finset.measurable_sum; intro k _
  apply Measurable.mul
  · have hy : Measurable (fun y : Fin (r * r) → ℝ => RmatG r pivot y i k) := by
      simp only [RmatG_entry]
      by_cases h : eG r (i, k) = pivot
      · simp only [if_pos h]; exact measurable_const
      · simp only [if_neg h]; exact measurable_pi_apply _
    exact hy.comp measurable_fst
  · exact (measurable_pi_apply j).comp ((measurable_pi_apply k).comp measurable_snd)

end DLNFibre.DLN.RLCT
