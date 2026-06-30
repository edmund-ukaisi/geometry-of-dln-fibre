import DLNFibre.DLN.RLCT.Validate.RouteMSchurDirectMorseP

/-!
# `DLNFibre.DLN.RLCT.Validate.RouteMSchurRectShear` — the RECTANGULAR top-row shear plumbing (3b-carve dep)

The asymmetric generalisation of the square `Fin p` top-row identity + foundational shear
(`RouteMSchurDirectMorseP.frobSqTopRowP_eq_shearP` / `stepShearGP` / `stepShearP_r`, where the angular
matrix is square `Fin r → Fin r` and the residual Schur complement is square `Fin (r−1) → Fin (r−1)`).

Two re-indexings vs. the square chain:
* the angular matrix is RECTANGULAR `R : Fin m → Fin n`, so the top-row shear runs over the `Fin (n−1)`
  non-pivot COLUMNS (= the contraction dim), not `Fin (m−1)`;
* the residual Schur complement is RECTANGULAR `Sc : Fin sr → Fin nr` (`sr = m−1` rows, `nr = n−1`
  contraction), so the abstract shear `stepShearGRect` frees `Sc`'s row type from its column/contraction
  type. The square `Sc : Fin m → Fin m` is the `sr = nr` case.

* `frobSqTopRowRect_eq_shear` — the rectangular top-row identity (`frobSqTopRowP_eq_shearP1`, `R : m×n`).
* `stepShearGRect` — the abstract rectangular shear (`stepShearGP`, `Sc : sr×nr`).
* `stepShearRect_r` — the row-indexed rectangular shear (`stepShearP_r`, `S : n×p` rows `⟨0⟩/⟨1+a⟩`).

INDEPENDENT of the carve coordinate side: builds only on the LANDED substrate
(`fin_sum_block_split` / `frobSq` / `rmatMul` / `matBox` / `morseBox` / `lintegral_translate_leG`).
-/

open MeasureTheory Set
open scoped ENNReal BigOperators
namespace DLNFibre.DLN.RLCT

/-! ## The rectangular top-row identity -/

/-- **The rectangular `Fin p` top-row identity** (rectangular analog of `frobSqTopRowP_eq_shearP1`). For an
angular matrix `R : Fin m → Fin n` with pivot `R ⟨0⟩ ⟨0⟩ = 1`, the squared norm of the TOP ROW of `R·S`
(`S : Fin n → Fin p`) equals the sum over the `Fin p` columns of the squared SHEARED entry
`S₀q + ∑_{a:Fin(n−1)} R₀,₁₊ₐ · S₁₊ₐ,q`. The shear runs over the `Fin (n−1)` non-pivot COLUMNS of `R`
(the contraction dim). Needs `1 ≤ m` (for the row `⟨0⟩ : Fin m`) and `1 ≤ n` (for the block split). -/
theorem frobSqTopRowRect_eq_shear (m n p : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n) (R : Fin m → Fin n → ℝ)
    (hpiv : R ⟨0, by omega⟩ ⟨0, by omega⟩ = 1) (S : Fin n → Fin p → ℝ) :
    frobSq (fun a : Fin 1 => rmatMul R S ⟨(a : ℕ), by omega⟩)
      = ∑ q, (S ⟨0, by omega⟩ q
          + ∑ a : Fin (n - 1), R ⟨0, by omega⟩ ⟨1 + (a : ℕ), by omega⟩
              * S ⟨1 + (a : ℕ), by omega⟩ q) ^ 2 := by
  unfold frobSq
  rw [Fin.sum_univ_one]
  refine Finset.sum_congr rfl (fun q _ => ?_)
  congr 1
  show rmatMul R S ⟨0, by omega⟩ q = _
  unfold rmatMul
  rw [fin_sum_block_split 1 (show (1 : ℕ) ≤ n by omega) (fun k : Fin n => R ⟨0, by omega⟩ k * S k q)]
  congr 1
  · rw [Fin.sum_univ_one]
    have h0 : (⟨(0 : Fin 1), lt_of_lt_of_le (0 : Fin 1).2 (show (1:ℕ) ≤ n by omega)⟩ : Fin n)
        = ⟨0, by omega⟩ := rfl
    rw [h0, hpiv, one_mul]

/-! ## The abstract rectangular shear (residual `Sc : sr × nr` freed) -/

/-- **The rectangular abstract shear** (rectangular analog of `stepShearGP`, `Sc`'s row type `sr` freed
from its column/contraction type `nr`). The top-row shear change of variables on the `S`-box
(`S : Fin (nr+1) → Fin p`): translating the top row `S 0 ↦ T' = S 0 + b·S_bot` bounds the sheared integral
by the product of the lower-block box and the enlarged `morseBox p` (radius `(nr+1)·T`, the shift
`|∑_a b_a S_bot_a| ≤ nr·T`). `Sc : Matrix (Fin sr) (Fin nr)` is an opaque spectator in `rmatMul Sc S_bot`
(its row count `sr` is never tied to the shear). -/
theorem stepShearGRect (sr nr p : ℕ) (b : Fin nr → ℝ) (hb : ∀ a, |b a| ≤ 1)
    (Sc : Matrix (Fin sr) (Fin nr) ℝ) (T : ℝ) (hT : 0 < T) (c' : ℝ) :
    (∫⁻ S in matBox (nr + 1) p T,
        ENNReal.ofReal (((∑ q, (S 0 q + ∑ a, b a * S a.succ q) ^ 2)
          + frobSq (rmatMul Sc (fun a q => S a.succ q))) ^ (-c')))
      ≤ ∫⁻ S_bot in matBox nr p T, ∫⁻ T' in morseBox p ((nr + 1 : ℕ) * T),
          ENNReal.ofReal (((∑ q, (T' q) ^ 2) + frobSq (rmatMul Sc S_bot)) ^ (-c')) := by
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (nr + 1) => Fin p → ℝ) 0 with he
  have hmp : MeasurePreserving e volume volume :=
    volume_preserving_piFinSuccAbove (fun _ : Fin (nr + 1) => Fin p → ℝ) 0
  set H : (Fin p → ℝ) × (Fin nr → Fin p → ℝ) → ℝ≥0∞ := fun q =>
    ENNReal.ofReal (((∑ qq, (q.1 qq + ∑ a, b a * q.2 a qq) ^ 2)
      + frobSq (rmatMul Sc q.2)) ^ (-c')) with hHdef
  have hHmeas : Measurable H := by
    rw [hHdef]
    apply ENNReal.measurable_ofReal.comp
    apply Measurable.comp (g := fun t : ℝ => t ^ (-c')) (by fun_prop)
    refine Measurable.add ?_ ?_
    · refine Finset.measurable_sum _ (fun qq _ => ?_)
      refine Measurable.pow_const ?_ 2
      have h0 : Measurable (fun q : (Fin p → ℝ) × (Fin nr → Fin p → ℝ) => q.1 qq) :=
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
  have hsplit : matBox (nr + 1) p T
      = e ⁻¹' ((Set.univ.pi (fun _ : Fin p => Set.Icc (-T) T)) ×ˢ matBox nr p T) := by
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
  have hLHS : (∫⁻ S in matBox (nr + 1) p T,
      ENNReal.ofReal (((∑ q, (S 0 q + ∑ a, b a * S a.succ q) ^ 2)
        + frobSq (rmatMul Sc (fun a q => S a.succ q))) ^ (-c')))
      = ∫⁻ pq in ((Set.univ.pi (fun _ : Fin p => Set.Icc (-T) T)) ×ˢ matBox nr p T), H pq := by
    rw [hsplit, ← hmp.setLIntegral_comp_preimage_emb e.measurableEmbedding H
        ((Set.univ.pi (fun _ : Fin p => Set.Icc (-T) T)) ×ˢ matBox nr p T)]
    refine setLIntegral_congr_fun ?_ (fun S _ => rfl)
    exact e.measurable (MeasurableSet.prod
      (MeasurableSet.univ_pi (fun _ => measurableSet_Icc)) (matBox_measurableSet nr p T))
  rw [hLHS, Measure.volume_eq_prod, setLIntegral_prod _ hHmeas.aemeasurable,
    lintegral_lintegral_swap hHmeas.aemeasurable]
  refine setLIntegral_mono_ae' (matBox_measurableSet nr p T) (ae_of_all _ (fun S_bot hSbot => ?_))
  set shift : Fin p → ℝ := fun q => ∑ a, b a * S_bot a q with hshift
  set f : (Fin p → ℝ) → ℝ≥0∞ := fun T' =>
    ENNReal.ofReal (((∑ q, (T' q) ^ 2) + frobSq (rmatMul Sc S_bot)) ^ (-c')) with hf
  have hrw : ∀ S_top : Fin p → ℝ, H (S_top, S_bot) = f (S_top + shift) := by
    intro S_top; rw [hHdef, hf]; rfl
  rw [lintegral_congr hrw]
  refine lintegral_translate_leG p shift (Set.univ.pi (fun _ : Fin p => Set.Icc (-T) T))
    (morseBox p ((nr + 1 : ℕ) * T)) f ?_
  rintro T' ⟨v, hv, rfl⟩
  simp only [morseBox, Set.mem_pi, Set.mem_univ, true_implies] at hv ⊢
  intro q
  have hvq := Set.mem_Icc.1 (hv q)
  have htermbd : ∀ a : Fin nr, |b a * S_bot a q| ≤ T := by
    intro a
    rw [abs_mul]
    have hSa := Set.mem_Icc.1 (hSbot a q)
    calc |b a| * |S_bot a q| ≤ 1 * T :=
          mul_le_mul (hb a) (abs_le.2 hSa) (abs_nonneg _) (by norm_num)
      _ = T := by ring
  have hshiftbd : |shift q| ≤ (nr : ℝ) * T := by
    rw [hshift]
    calc |∑ a, b a * S_bot a q| ≤ ∑ a, |b a * S_bot a q| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _a : Fin nr, T := Finset.sum_le_sum (fun a _ => htermbd a)
      _ = (nr : ℝ) * T := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [Set.mem_Icc, Pi.add_apply, hshift]
  have habs := abs_le.1 hshiftbd
  push_cast
  constructor <;> [nlinarith [hvq.1, habs.1, hT]; nlinarith [hvq.2, habs.2, hT]]

/-- **The rectangular row-indexed shear** (rectangular analog of `stepShearP_r`). Same as `stepShearGRect`
but with the `Fin n` row indices `⟨0⟩` / `⟨1+a⟩` (the carve's native index form) instead of `0` / `a.succ`,
via the `(n−1)+1 = n` row-reindex MP. The contraction dim is `n`, the residual `Sc : Fin sr → Fin (n−1)`.
Needs `1 ≤ n`. -/
theorem stepShearRect_r (sr n p : ℕ) (hn : 1 ≤ n) (b : Fin (n - 1) → ℝ) (hb : ∀ a, |b a| ≤ 1)
    (Sc : Matrix (Fin sr) (Fin (n - 1)) ℝ) (T : ℝ) (hT : 0 < T) (c' : ℝ) :
    (∫⁻ S in matBox n p T,
        ENNReal.ofReal (((∑ q, (S ⟨0, by omega⟩ q + ∑ a, b a * S ⟨1 + (a : ℕ), by omega⟩ q) ^ 2)
          + frobSq (rmatMul Sc (fun a q => S ⟨1 + (a : ℕ), by omega⟩ q))) ^ (-c')))
      ≤ ∫⁻ S_bot in matBox (n - 1) p T, ∫⁻ T' in morseBox p ((n : ℕ) * T),
          ENNReal.ofReal (((∑ q, (T' q) ^ 2) + frobSq (rmatMul Sc S_bot)) ^ (-c')) := by
  have hrm : (n - 1) + 1 = n := Nat.sub_add_cancel hn
  set er : Fin ((n - 1) + 1) ≃ Fin n := finCongr hrm with her
  set E := MeasurableEquiv.piCongrLeft (fun _ : Fin n => Fin p → ℝ) er with hE
  have hmp : MeasurePreserving E.symm volume volume :=
    (volume_measurePreserving_piCongrLeft (fun _ : Fin n => Fin p → ℝ) er).symm E
  have hpre : matBox n p T = E.symm ⁻¹' (matBox ((n - 1) + 1) p T) := by
    ext S
    simp only [Set.mem_preimage, matBox, Set.mem_setOf_eq]
    constructor
    · intro h i k; exact h (er i) k
    · intro h i k
      have := h (er.symm i) k
      rw [show E.symm S (er.symm i) k = S i k from by
        show S (er (er.symm i)) k = S i k; rw [Equiv.apply_symm_apply]] at this
      exact this
  set f : (Fin ((n - 1) + 1) → Fin p → ℝ) → ℝ≥0∞ := fun S =>
    ENNReal.ofReal (((∑ q, (S 0 q + ∑ a, b a * S a.succ q) ^ 2)
      + frobSq (rmatMul Sc (fun a q => S a.succ q))) ^ (-c')) with hf
  have hkey := hmp.setLIntegral_comp_preimage_emb E.symm.measurableEmbedding f
    (matBox ((n - 1) + 1) p T)
  rw [← hpre] at hkey
  have hLHSeq : (∫⁻ S in matBox n p T,
      ENNReal.ofReal (((∑ q, (S ⟨0, by omega⟩ q + ∑ a, b a * S ⟨1 + (a : ℕ), by omega⟩ q) ^ 2)
        + frobSq (rmatMul Sc (fun a q => S ⟨1 + (a : ℕ), by omega⟩ q))) ^ (-c')))
      = ∫⁻ S in matBox n p T, f (E.symm S) := by
    refine lintegral_congr (fun S => ?_)
    rw [hf]
    have hrow0 : E.symm S (0 : Fin ((n - 1) + 1)) = S ⟨0, by omega⟩ := by
      show S (er 0) = S ⟨0, by omega⟩; rfl
    have hrowsucc : ∀ a : Fin (n - 1), E.symm S a.succ = S ⟨1 + (a : ℕ), by omega⟩ := by
      intro a
      show S (er a.succ) = S ⟨1 + (a : ℕ), by omega⟩
      congr 1; apply Fin.ext; simp [her, Fin.succ]; omega
    simp only [hrow0, hrowsucc]
  rw [hLHSeq, hkey]
  have hshear := stepShearGRect sr (n - 1) p b hb Sc T hT c'
  have hcast : (((n - 1) + 1 : ℕ) : ℝ) * T = ((n : ℕ) : ℝ) * T := by rw [hrm]
  rw [hcast] at hshear
  exact hshear

end DLNFibre.DLN.RLCT
