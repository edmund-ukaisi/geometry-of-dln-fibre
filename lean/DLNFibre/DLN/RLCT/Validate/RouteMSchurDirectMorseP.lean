import DLNFibre.DLN.RLCT.Validate.RouteMSchurFiring
import DLNFibre.DLN.RLCT.Validate.RouteMSchurGenCover

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

/-- **The `Fin p` row/col permutation of `frobSq(R·S)`** (`Fin p` analog of `frobSq_rmatMul_permG`):
permuting `R`'s rows by `σr` and both `R`'s cols / `S`'s rows by `σc` leaves `frobSq(R·S)` invariant. The
`4 → p` swap is verbatim (`p` is the opaque `∑ j : Fin p` column sum). -/
theorem frobSq_rmatMul_permGP {r p : ℕ} (R : Fin r → Fin r → ℝ) (S : Fin r → Fin p → ℝ)
    (σr σc : Fin r ≃ Fin r) :
    frobSq (rmatMul R S)
      = frobSq (rmatMul (fun a c => R (σr a) (σc c)) (fun k j => S (σc k) j)) := by
  unfold frobSq rmatMul
  rw [← Equiv.sum_comp σr (fun a => ∑ j, (∑ k, R a k * S k j) ^ 2)]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  refine Finset.sum_congr rfl (fun j _ => ?_)
  congr 1
  rw [← Equiv.sum_comp σc (fun k => R (σr a) k * S k j)]

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

/-- `innerSGenP` is `y pivot`-invariant (`RmatG r pivot y` reads `y i` only for `i ≠ pivot`); the
`Fin p` analog of `innerSGen_offpivot`. -/
theorem innerSGenP_offpivot (r p : ℕ) (c' : ℝ) (T : ℝ) (pivot : Fin (r * r))
    (y y' : Fin (r * r) → ℝ) (h : ∀ i, i ≠ pivot → y i = y' i) :
    innerSGenP r p c' T pivot y = innerSGenP r p c' T pivot y' := by
  have hR : RmatG r pivot y = RmatG r pivot y' := by
    funext i j; rw [RmatG_entry, RmatG_entry]
    by_cases hij : eG r (i, j) = pivot
    · rw [if_pos hij, if_pos hij]
    · rw [if_neg hij, if_neg hij]; exact h _ hij
  rw [innerSGenP, innerSGenP, hR]

/-! ## The cap-B per-`R` inner bound (the genuinely-new directMorse content) -/

/-- **The cap-B inner-`S` finiteness, per angular matrix `R`.** For an `r×r` matrix `R` (`r ≥ 3`) with pivot
`R ⟨0⟩ ⟨0⟩ = 1` and bounded entries `|R a b| ≤ 1`, and `c' < p/2`, the inner-`S` integral
`∫_{S∈matBox r p T} frobSq(R·S)^{−c'} < ⊤` — WITHOUT recursion. The N2b (`j = 1`) two-sided bound bounds
`frobSq(R·S)^{−c'} ≤ c₀^{−c'}·(frobSq(top row) + frobSq(Sc·S_bot))^{−c'}` (`ofReal_rpow_le_const_mul`, the
zero-guard from the upper bound); the split value `X = topRow + frobSq(Sc·S_bot)` rewrites the top row via
`frobSqTopRowP_eq_shearP`; `stepShearP_r` peels the `Fin p` Morse block to `morseBox p (r·T)`; and the
abstract-`Z` Morse dominator `radial_morse_dominates_absZ_lt_top` (`m+1 = p`, `Z = matBox (r-1) p (r·T)`,
`W = frobSq(Sc·S_bot)`) closes it for `c' < p/2`. The constant `c₀` is uniform (chosen before `R`). Cap-B
keeps the residual (the binding stratum `t = 0`); no recursion, unlike the cap-A carve. -/
theorem frobSq_capB_inner_lt_top (r p : ℕ) (hr : 3 ≤ r) (R : Fin r → Fin r → ℝ)
    (hpiv : R ⟨0, by omega⟩ ⟨0, by omega⟩ = 1) (hbd : ∀ a b, |R a b| ≤ 1)
    (c' : ℝ) (hc0 : 0 < c') (hc' : c' < (p : ℝ) / 2) (T : ℝ) (hT : 0 < T) :
    (∫⁻ S in matBox r p T, ENNReal.ofReal ((frobSq (rmatMul R S)) ^ (-c'))) < ⊤ := by
  classical
  have hrm1 : (1 : ℕ) ≤ r := by omega
  -- view R as a Matrix for the Matrix-API spots (.submatrix/.det); rmatMul RM = rmatMul R (defeq)
  set RM : Matrix (Fin r) (Fin r) ℝ := Matrix.of R with hRM
  set c₀ := (schur_minorPivot_split (r := r) (p := p) 1 (by omega)).choose with hc₀def
  obtain ⟨c₁, hc₀, hc₁, hN2b⟩ := (schur_minorPivot_split (r := r) (p := p) 1 hrm1).choose_spec
  -- the 1×1 pivot minor M11 = [1]: det = 1, dominance from |entries| ≤ 1, det ≠ 0
  set M11 : Matrix (Fin 1) (Fin 1) ℝ :=
    Matrix.of (fun a b : Fin 1 => RM ⟨a, lt_of_lt_of_le a.2 hrm1⟩ ⟨b, lt_of_lt_of_le b.2 hrm1⟩) with hM11
  have hM11_one : M11 = 1 := by
    ext a b; fin_cases a; fin_cases b
    simp only [hM11, hRM, Matrix.of_apply, Matrix.one_apply_eq]; exact hpiv
  have hpivdet : M11.det = 1 := by rw [hM11_one]; simp
  have hpivot : ∀ I J : Fin 1 → Fin r, |(RM.submatrix I J).det| ≤ |M11.det| := by
    intro I J
    rw [Matrix.det_fin_one, hpivdet, abs_one, Matrix.submatrix_apply]
    exact hbd (I 0) (J 0)
  have hne : M11.det ≠ 0 := by rw [hpivdet]; norm_num
  -- fix Sc via a dummy extraction; the split value X and the per-S two-sided bound
  obtain ⟨Sc, hSceq, _hdet, _, _⟩ := hN2b RM (fun _ _ => 0) hbd hpivot hne
  set X : (Fin r → Fin p → ℝ) → ℝ := fun S =>
    frobSq (fun a : Fin 1 => rmatMul (fun x y => RM x y) S ⟨a, lt_of_lt_of_le a.2 hrm1⟩)
      + frobSq (rmatMul (fun a b => Sc a b) (fun a : Fin (r - 1) => S ⟨1 + a, by omega⟩)) with hXdef
  have hXnn : ∀ S, 0 ≤ X S := fun S => add_nonneg (frobSq_nonneg _) (frobSq_nonneg _)
  have hlow : ∀ S, c₀ * X S ≤ frobSq (rmatMul RM S) := by
    intro S
    obtain ⟨Sc', hSceq', _, hlo, _⟩ := hN2b RM S hbd hpivot hne
    have : Sc' = Sc := by rw [hSceq', ← hSceq]
    subst this; simpa only [hXdef] using hlo
  have hupp : ∀ S, frobSq (rmatMul RM S) ≤ c₁ * X S := by
    intro S
    obtain ⟨Sc', hSceq', _, _, hup⟩ := hN2b RM S hbd hpivot hne
    have : Sc' = Sc := by rw [hSceq', ← hSceq]
    subst this; simpa only [hXdef] using hup
  -- rpow domination
  have hpt : ∀ S, ENNReal.ofReal ((frobSq (rmatMul R S)) ^ (-c'))
      ≤ ENNReal.ofReal (c₀ ^ (-c')) * ENNReal.ofReal ((X S) ^ (-c')) := by
    intro S
    refine ofReal_rpow_le_const_mul (X S) (frobSq (rmatMul R S)) c₀ c'
      hc0 hc₀ (hXnn S) (frobSq_nonneg _) (hlow S) ?_
    intro hX0
    have := hupp S; rw [hX0, mul_zero] at this
    exact le_antisymm this (frobSq_nonneg _)
  -- the coupling row b a = RM ⟨0⟩ ⟨1+a⟩, |b| ≤ 1; pivot for frobSqTopRowP
  set bcoup : Fin (r - 1) → ℝ := fun a => RM ⟨0, by omega⟩ ⟨1 + (a : ℕ), by omega⟩ with hbcoup
  have hbcoup_le : ∀ a, |bcoup a| ≤ 1 := fun a => hbd _ _
  have hpiv' : (fun x y => RM x y) ⟨0, by omega⟩ ⟨0, by omega⟩ = 1 := hpiv
  -- X S = (shear sum) + frobSq(Sc·S_bot)  (frobSqTopRowP_eq_shearP)
  have hXrw : ∀ S, X S
      = (∑ q, (S ⟨0, by omega⟩ q + ∑ a, bcoup a * S ⟨1 + (a : ℕ), by omega⟩ q) ^ 2)
        + frobSq (rmatMul (fun a b => Sc a b) (fun a q => S ⟨1 + (a : ℕ), by omega⟩ q)) := by
    intro S
    simp only [hXdef]
    rw [frobSqTopRowP_eq_shearP r p hr (fun x y => RM x y) hpiv' S]
  -- assemble: rpow domination → pull constant → frobSqTopRowP bridge → stepShearP_r → Morse dominator
  obtain ⟨pm, hpm⟩ : ∃ pm, p = pm + 1 := by
    refine ⟨p - 1, ?_⟩
    have : 0 < p := by
      by_contra h
      push_neg at h; interval_cases p; simp at hc'; linarith
    omega
  calc (∫⁻ S in matBox r p T, ENNReal.ofReal ((frobSq (rmatMul R S)) ^ (-c')))
      ≤ ∫⁻ S in matBox r p T, ENNReal.ofReal (c₀ ^ (-c')) * ENNReal.ofReal ((X S) ^ (-c')) :=
        lintegral_mono hpt
    _ = ENNReal.ofReal (c₀ ^ (-c')) * ∫⁻ S in matBox r p T, ENNReal.ofReal ((X S) ^ (-c')) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ = ENNReal.ofReal (c₀ ^ (-c'))
          * ∫⁻ S in matBox r p T,
              ENNReal.ofReal (((∑ q, (S ⟨0, by omega⟩ q
                  + ∑ a, bcoup a * S ⟨1 + (a : ℕ), by omega⟩ q) ^ 2)
                + frobSq (rmatMul (fun a b => Sc a b)
                    (fun a q => S ⟨1 + (a : ℕ), by omega⟩ q))) ^ (-c')) := by
        congr 1; exact lintegral_congr (fun S => by rw [hXrw S])
    _ ≤ ENNReal.ofReal (c₀ ^ (-c'))
          * (∫⁻ S_bot in matBox (r - 1) p T, ∫⁻ T' in morseBox p ((r : ℕ) * T),
              ENNReal.ofReal (((∑ q, (T' q) ^ 2)
                + frobSq (rmatMul (fun a b => Sc a b) S_bot)) ^ (-c'))) :=
        mul_le_mul_left' (stepShearP_r r p hr bcoup hbcoup_le (Matrix.of (fun a b => Sc a b)) T hT c') _
    _ < ⊤ := by
        refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_
        -- the residual-kept double integral is finite via the abstract-Z Morse dominator (c' < p/2)
        have hcap : c' < ((pm + 1 : ℝ)) / 2 := by rw [hpm] at hc'; push_cast at hc'; exact hc'
        have hrT : 0 < (r : ℕ) * T := by positivity
        have hZfin : volume (matBox (r - 1) p ((r : ℕ) * T)) < ⊤ :=
          matBox_volume_lt_top (r - 1) p ((r : ℕ) * T)
        have hmain := radial_morse_dominates_absZ_lt_top (m := pm) (Ω := Fin (r - 1) → Fin p → ℝ)
          (volume) c' hcap hc0.le ((r : ℕ) * T) hrT
          (fun S_bot => frobSq (rmatMul (fun a b => Sc a b) S_bot))
          (fun _ => frobSq_nonneg _) (matBox (r - 1) p ((r : ℕ) * T)) hZfin
        -- hmain: ∫_{Z} ∫_{morseBox (pm+1) (r·T)} (∑P² + W)^{−c'} < ⊤; rewrite pm+1 = p, Z radius T ⊆ r·T
        have hpconv : pm + 1 = p := hpm.symm
        subst hpconv
        -- the LHS box (S_bot at radius T) ⊆ (S_bot at radius r·T) — enlarge, then hmain
        have hsub : matBox (r - 1) (pm + 1) T ⊆ matBox (r - 1) (pm + 1) ((r : ℕ) * T) := by
          intro Y hY i k; have := Set.mem_Icc.1 (hY i k); rw [Set.mem_Icc]
          have hTrT : T ≤ (r : ℕ) * T := le_mul_of_one_le_left hT.le
            (by exact_mod_cast (show (1:ℕ) ≤ r by omega))
          constructor <;> [linarith [this.1]; linarith [this.2]]
        exact lt_of_le_of_lt (lintegral_mono_set hsub) hmain

/-- **The cap-B inner-`S` bound by a `z`-UNIFORM constant.** Same hypotheses/proof as
`frobSq_capB_inner_lt_top`, but ending at the explicit bound `ofReal(c₀^{−c'}) · Kbound p c' (r·T) ·
vol(matBox (r-1) p (r·T))` rather than `< ⊤`. The bound is INDEPENDENT of `R` (hence of the chart `z`):
`c₀ = (schur_minorPivot_split r p 1 _).choose` is chosen before `R`, `Kbound`/`vol` are `R`-free, and the
abstract-`Z` Morse dominator's `Kbound` is `W`-INDEPENDENT (`radial_morse_dominates_absZ_le`). This is the
composable form the per-chart `z`-integration consumes (the per-`z` bound factors out as a constant). -/
theorem frobSq_capB_inner_le (r p : ℕ) (hr : 3 ≤ r) (R : Fin r → Fin r → ℝ)
    (hpiv : R ⟨0, by omega⟩ ⟨0, by omega⟩ = 1) (hbd : ∀ a b, |R a b| ≤ 1)
    (c' : ℝ) (hc0 : 0 < c') (hc' : c' < (p : ℝ) / 2) (T : ℝ) (hT : 0 < T) :
    (∫⁻ S in matBox r p T, ENNReal.ofReal ((frobSq (rmatMul R S)) ^ (-c')))
      ≤ ENNReal.ofReal ((schur_minorPivot_split (r := r) (p := p) 1 (by omega)).choose ^ (-c'))
        * (Kbound p c' ((r : ℕ) * T) * volume (matBox (r - 1) p ((r : ℕ) * T))) := by
  classical
  have hrm1 : (1 : ℕ) ≤ r := by omega
  set RM : Matrix (Fin r) (Fin r) ℝ := Matrix.of R with hRM
  set c₀ := (schur_minorPivot_split (r := r) (p := p) 1 (by omega)).choose with hc₀def
  obtain ⟨c₁, hc₀, hc₁, hN2b⟩ := (schur_minorPivot_split (r := r) (p := p) 1 hrm1).choose_spec
  set M11 : Matrix (Fin 1) (Fin 1) ℝ :=
    Matrix.of (fun a b : Fin 1 => RM ⟨a, lt_of_lt_of_le a.2 hrm1⟩ ⟨b, lt_of_lt_of_le b.2 hrm1⟩) with hM11
  have hM11_one : M11 = 1 := by
    ext a b; fin_cases a; fin_cases b
    simp only [hM11, hRM, Matrix.of_apply, Matrix.one_apply_eq]; exact hpiv
  have hpivdet : M11.det = 1 := by rw [hM11_one]; simp
  have hpivot : ∀ I J : Fin 1 → Fin r, |(RM.submatrix I J).det| ≤ |M11.det| := by
    intro I J
    rw [Matrix.det_fin_one, hpivdet, abs_one, Matrix.submatrix_apply]
    exact hbd (I 0) (J 0)
  have hne : M11.det ≠ 0 := by rw [hpivdet]; norm_num
  obtain ⟨Sc, hSceq, _hdet, _, _⟩ := hN2b RM (fun _ _ => 0) hbd hpivot hne
  set X : (Fin r → Fin p → ℝ) → ℝ := fun S =>
    frobSq (fun a : Fin 1 => rmatMul (fun x y => RM x y) S ⟨a, lt_of_lt_of_le a.2 hrm1⟩)
      + frobSq (rmatMul (fun a b => Sc a b) (fun a : Fin (r - 1) => S ⟨1 + a, by omega⟩)) with hXdef
  have hXnn : ∀ S, 0 ≤ X S := fun S => add_nonneg (frobSq_nonneg _) (frobSq_nonneg _)
  have hlow : ∀ S, c₀ * X S ≤ frobSq (rmatMul RM S) := by
    intro S
    obtain ⟨Sc', hSceq', _, hlo, _⟩ := hN2b RM S hbd hpivot hne
    have : Sc' = Sc := by rw [hSceq', ← hSceq]
    subst this; simpa only [hXdef] using hlo
  have hupp : ∀ S, frobSq (rmatMul RM S) ≤ c₁ * X S := by
    intro S
    obtain ⟨Sc', hSceq', _, _, hup⟩ := hN2b RM S hbd hpivot hne
    have : Sc' = Sc := by rw [hSceq', ← hSceq]
    subst this; simpa only [hXdef] using hup
  have hpt : ∀ S, ENNReal.ofReal ((frobSq (rmatMul R S)) ^ (-c'))
      ≤ ENNReal.ofReal (c₀ ^ (-c')) * ENNReal.ofReal ((X S) ^ (-c')) := by
    intro S
    refine ofReal_rpow_le_const_mul (X S) (frobSq (rmatMul R S)) c₀ c'
      hc0 hc₀ (hXnn S) (frobSq_nonneg _) (hlow S) ?_
    intro hX0
    have := hupp S; rw [hX0, mul_zero] at this
    exact le_antisymm this (frobSq_nonneg _)
  set bcoup : Fin (r - 1) → ℝ := fun a => RM ⟨0, by omega⟩ ⟨1 + (a : ℕ), by omega⟩ with hbcoup
  have hbcoup_le : ∀ a, |bcoup a| ≤ 1 := fun a => hbd _ _
  have hpiv' : (fun x y => RM x y) ⟨0, by omega⟩ ⟨0, by omega⟩ = 1 := hpiv
  have hXrw : ∀ S, X S
      = (∑ q, (S ⟨0, by omega⟩ q + ∑ a, bcoup a * S ⟨1 + (a : ℕ), by omega⟩ q) ^ 2)
        + frobSq (rmatMul (fun a b => Sc a b) (fun a q => S ⟨1 + (a : ℕ), by omega⟩ q)) := by
    intro S
    simp only [hXdef]
    rw [frobSqTopRowP_eq_shearP r p hr (fun x y => RM x y) hpiv' S]
  obtain ⟨pm, hpm⟩ : ∃ pm, p = pm + 1 := by
    refine ⟨p - 1, ?_⟩
    have : 0 < p := by
      by_contra h
      push_neg at h; interval_cases p; simp at hc'; linarith
    omega
  calc (∫⁻ S in matBox r p T, ENNReal.ofReal ((frobSq (rmatMul R S)) ^ (-c')))
      ≤ ∫⁻ S in matBox r p T, ENNReal.ofReal (c₀ ^ (-c')) * ENNReal.ofReal ((X S) ^ (-c')) :=
        lintegral_mono hpt
    _ = ENNReal.ofReal (c₀ ^ (-c')) * ∫⁻ S in matBox r p T, ENNReal.ofReal ((X S) ^ (-c')) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ = ENNReal.ofReal (c₀ ^ (-c'))
          * ∫⁻ S in matBox r p T,
              ENNReal.ofReal (((∑ q, (S ⟨0, by omega⟩ q
                  + ∑ a, bcoup a * S ⟨1 + (a : ℕ), by omega⟩ q) ^ 2)
                + frobSq (rmatMul (fun a b => Sc a b)
                    (fun a q => S ⟨1 + (a : ℕ), by omega⟩ q))) ^ (-c')) := by
        congr 1; exact lintegral_congr (fun S => by rw [hXrw S])
    _ ≤ ENNReal.ofReal (c₀ ^ (-c'))
          * (∫⁻ S_bot in matBox (r - 1) p T, ∫⁻ T' in morseBox p ((r : ℕ) * T),
              ENNReal.ofReal (((∑ q, (T' q) ^ 2)
                + frobSq (rmatMul (fun a b => Sc a b) S_bot)) ^ (-c'))) :=
        mul_le_mul_left' (stepShearP_r r p hr bcoup hbcoup_le (Matrix.of (fun a b => Sc a b)) T hT c') _
    _ ≤ ENNReal.ofReal (c₀ ^ (-c'))
          * (Kbound p c' ((r : ℕ) * T) * volume (matBox (r - 1) p ((r : ℕ) * T))) := by
        refine mul_le_mul_left' ?_ _
        -- enlarge the S_bot box (radius T ⊆ r·T), then the abstract-Z Morse dominator's _le bound
        have hcap : c' < ((pm + 1 : ℝ)) / 2 := by rw [hpm] at hc'; push_cast at hc'; exact hc'
        have hsub : matBox (r - 1) p T ⊆ matBox (r - 1) p ((r : ℕ) * T) := by
          intro Y hY i k; have := Set.mem_Icc.1 (hY i k); rw [Set.mem_Icc]
          have hTrT : T ≤ (r : ℕ) * T := le_mul_of_one_le_left hT.le
            (by exact_mod_cast (show (1:ℕ) ≤ r by omega))
          constructor <;> [linarith [this.1]; linarith [this.2]]
        refine le_trans (lintegral_mono_set hsub) ?_
        have hle := radial_morse_dominates_absZ_le (m := pm) (Ω := Fin (r - 1) → Fin p → ℝ)
          (volume) c' hcap hc0.le ((r : ℕ) * T) (by positivity)
          (fun S_bot => frobSq (rmatMul (fun a b => Sc a b) S_bot))
          (fun _ => frobSq_nonneg _) (matBox (r - 1) p ((r : ℕ) * T))
        -- hle: ∫_Z ∫_{morseBox (pm+1) (r·T)} (∑P²+W)^{−c'} ≤ Kbound (pm+1) c' (r·T) · vol Z
        have hpconv : pm + 1 = p := hpm.symm
        subst hpconv
        exact hle

/-! ## The `(r,p)` gen blow-up factor machinery (`4 → p` of the firing's `gFlatG_*` chain) -/

/-- **The `(r,p)` radial pull-out** (`Fin p` analog of `gFlatG_blowup_radial`). The N1 degree-2
homogeneity: `gFlatGen r p c' T (blowup) = ∫_S ((y p)²·frobSq(RmatG·S))^{−c'}`. The angular matrix
`RmatG r p y` is `p`-free (it reshapes the `r×r` ratio chart via `matToFlatGen.symm = matToFlatG.symm`);
only the inner `S`-box width is `p`. Verbatim from `gFlatG_blowup_radial` (`4 → p`, `matToFlatG → matToFlatGen`). -/
theorem gFlatGen_blowup_radial (r p : ℕ) (c' : ℝ) (T : ℝ) (pivot : Fin (r * r)) (y : Fin (r * r) → ℝ) :
    gFlatGen r p c' T (pivotBlowupOn (Finset.univ : Finset (Fin (r * r))) pivot y)
      = ∫⁻ S in matBox r p T,
          ENNReal.ofReal (((y pivot) ^ 2 * frobSq (rmatMul (RmatG r pivot y) S)) ^ (-c')) := by
  unfold gFlatGen
  refine lintegral_congr (fun S => ?_)
  congr 1
  show (frobSq (rmatMul ((matToFlatGen r).symm
      (pivotBlowupOn (Finset.univ : Finset (Fin (r * r))) pivot y)) S)) ^ (-c') = _
  have hbl : (matToFlatGen r).symm (pivotBlowupOn (Finset.univ : Finset (Fin (r * r))) pivot y)
      = fun a b => (y pivot) * (RmatG r pivot y) a b := by
    funext a b
    show (matToFlatGen r).symm (pivotBlowupOn (Finset.univ : Finset (Fin (r * r))) pivot y) a b = _
    rw [show pivotBlowupOn (Finset.univ : Finset (Fin (r * r))) pivot y
        = (fun i => (y pivot) * (if i = pivot then 1 else y i)) from by
      funext i; unfold pivotBlowupOn
      by_cases hi : i = pivot
      · subst hi; simp
      · simp [hi]]
    rfl
  rw [hbl, radialDelta_loss_factor (y pivot) (RmatG r pivot y) S]

/-- **The `(r,p)` blow-up membership** (`Fin p` analog of `flatBoxG_blowup_mem_iff`). Since
`flatBoxGen r T = flatBoxG r T` definitionally, this is the firing lemma re-stated on the gen box. -/
theorem flatBoxGen_blowup_mem_iff (r : ℕ) (T : ℝ) (pivot : Fin (r * r)) (y : Fin (r * r) → ℝ)
    (hy : y ∈ chartDomOn (Finset.univ : Finset (Fin (r * r))) pivot) :
    pivotBlowupOn (Finset.univ : Finset (Fin (r * r))) pivot y ∈ flatBoxGen r T ↔ |y pivot| ≤ T :=
  flatBoxG_blowup_mem_iff r T pivot y hy

/-- **The `(r,p)` per-chart factor** (`Fin p` analog of `chart_integrand_factorG`). On the chart, the
flattened radial-Jacobian × `gFlatGen`-indicator factors as the radial `a`-axis indicator
`|y p|^{(r²−1)−2c'}` × the `Fin p` angular residual `innerSGenP`. Verbatim from `chart_integrand_factorG`
(`4 → p`, `gFlatG → gFlatGen`, `flatBoxG → flatBoxGen`, `innerSGen → innerSGenP`). -/
theorem chart_integrand_factorGen (r p : ℕ) (c' : ℝ) (hc0 : 0 < c') (T : ℝ) (hT : 0 < T)
    (pivot : Fin (r * r)) (y : Fin (r * r) → ℝ) (hyp0 : y pivot ≠ 0)
    (hy : y ∈ chartDomOn (Finset.univ : Finset (Fin (r * r))) pivot) :
    ENNReal.ofReal (|y pivot| ^ (r * r - 1))
        * (flatBoxGen r T).indicator (gFlatGen r p c' T) (pivotBlowupOn
            (Finset.univ : Finset (Fin (r * r))) pivot y)
      = (Set.Icc (-T) T).indicator
          (fun a => ENNReal.ofReal (|a| ^ (((r * r - 1 : ℕ) : ℝ) - 2 * c'))) (y pivot)
        * innerSGenP r p c' T pivot y := by
  by_cases hmem : pivotBlowupOn (Finset.univ : Finset (Fin (r * r))) pivot y ∈ flatBoxGen r T
  · have hyp : |y pivot| ≤ T := (flatBoxGen_blowup_mem_iff r T pivot y hy).1 hmem
    rw [Set.indicator_of_mem hmem,
      Set.indicator_of_mem (s := Set.Icc (-T) T) (by rw [Set.mem_Icc, ← abs_le]; exact hyp)]
    rw [gFlatGen_blowup_radial r p c' T pivot y, innerSGenP]
    have hpull : ∀ S : Fin r → Fin p → ℝ,
        ENNReal.ofReal (((y pivot) ^ 2 * frobSq (rmatMul (RmatG r pivot y) S)) ^ (-c'))
          = ENNReal.ofReal ((((y pivot) ^ 2) ^ (-c')))
            * ENNReal.ofReal ((frobSq (rmatMul (RmatG r pivot y) S)) ^ (-c')) := by
      intro S
      rw [← ENNReal.ofReal_mul (Real.rpow_nonneg (by positivity) _),
        ← Real.mul_rpow (by positivity) (frobSq_nonneg _)]
    rw [lintegral_congr hpull, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← mul_assoc]
    congr 1
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    have hb : ((y pivot) ^ 2 : ℝ) = |y pivot| ^ (2 : ℝ) := by
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, sq_abs]
    have hpos : (0 : ℝ) < |y pivot| := abs_pos.2 hyp0
    rw [hb, ← Real.rpow_natCast (|y pivot|) (r * r - 1), ← Real.rpow_mul (le_of_lt hpos),
      ← Real.rpow_add hpos]
    congr 1; push_cast; ring
  · have hyp : ¬ |y pivot| ≤ T := fun h => hmem ((flatBoxGen_blowup_mem_iff r T pivot y hy).2 h)
    rw [Set.indicator_of_notMem hmem,
      Set.indicator_of_notMem (s := Set.Icc (-T) T)
        (by rw [Set.mem_Icc, ← abs_le]; exact hyp), zero_mul, mul_zero]

/-! ## The cap-B per-chart angular residual + the directMorse cover (WIP) -/

/-- **The cap-B angular residual finiteness (per chart).** For `c' < p/2`, the angular box-integral of the
inner-`S` integrand over the `r²−1` ratio box is finite. Per `z`, the angular matrix
`R := RmatGnorm (piRatioG.symm (0,z))` has pivot `1` (`RmatGnorm_pivot`) and `|entries| ≤ 1`
(`RmatGnorm_offpivot_le`), so `frobSq_capB_inner_lt_top` gives per-`z` finiteness; the bound is `z`-uniform
(the abstract-`Z` Morse dominator's `Kbound` is `W`-independent, and `c₀` is chosen before `R`), so the
integral over the finite-volume ratio box is finite. WIP — the `z`-uniform constant bound + box integration.
The cap-B analog of `schurRatioResidGen` (NO recursion). -/
theorem schurRatioResidP_capB_lt_top (r N p : ℕ) (hN : r * r = N + 1) (hr : 3 ≤ r)
    (c' : ℝ) (hc0 : 0 < c') (hc' : c' < (p : ℝ) / 2) (pivot : Fin (r * r)) (T : ℝ) (hT : 0 < T) :
    (∫⁻ z in (Set.univ.pi (fun _ : Fin N => Set.Icc (-1 : ℝ) 1)),
        innerSGenP r p c' T pivot ((piRatioG r N hN pivot).symm (0, z)))
      < ⊤ := by
  classical
  -- the z-uniform constant bound (R-free): C := ofReal(c₀^{−c'})·(Kbound p c' (r·T)·vol(matBox(r-1)p(r·T)))
  set C : ℝ≥0∞ :=
    ENNReal.ofReal ((schur_minorPivot_split (r := r) (p := p) 1 (by omega)).choose ^ (-c'))
      * (Kbound p c' ((r : ℕ) * T) * volume (matBox (r - 1) p ((r : ℕ) * T))) with hC
  -- per z ∈ [−1,1]^N: R := RmatGnorm has pivot 1 + |entries| ≤ 1, so innerSGenP ≤ C (frobSq_capB_inner_le)
  have hpt : ∀ z ∈ Set.univ.pi (fun _ : Fin N => Set.Icc (-1 : ℝ) 1),
      innerSGenP r p c' T pivot ((piRatioG r N hN pivot).symm (0, z)) ≤ C := by
    intro z hz
    -- innerSGenP at the carve point = ∫_S frobSq(RmatGnorm·S)^{−c'} (pivot-normalised, Fin p)
    have heq : innerSGenP r p c' T pivot ((piRatioG r N hN pivot).symm (0, z))
        = ∫⁻ S in matBox r p T,
            ENNReal.ofReal ((frobSq (rmatMul (RmatGnorm r N hN hr pivot z) S)) ^ (-c')) := by
      rw [innerSGenP]
      -- the σc row-permutation MP + the frobSq perm identity (Fin p analog of innerSGen_eq_norm)
      set σr := Equiv.swap ((eG r).symm pivot).1 (⟨0, by omega⟩ : Fin r) with hσr
      set σc := Equiv.swap ((eG r).symm pivot).2 (⟨0, by omega⟩ : Fin r) with hσc
      set E := MeasurableEquiv.piCongrLeft (fun _ : Fin r => Fin p → ℝ) σc with hE
      have hmp : MeasurePreserving E.symm volume volume :=
        (volume_measurePreserving_piCongrLeft (fun _ : Fin r => Fin p → ℝ) σc).symm E
      have hpre : matBox r p T = E.symm ⁻¹' (matBox r p T) := by
        ext S
        simp only [Set.mem_preimage, matBox, Set.mem_setOf_eq]
        constructor
        · intro h i k; exact h (σc i) k
        · intro h i k
          have := h (σc.symm i) k
          rw [show E.symm S (σc.symm i) k = S i k from by
            show S (σc (σc.symm i)) k = S i k; rw [Equiv.apply_symm_apply]] at this
          exact this
      have key := hmp.setLIntegral_comp_preimage_emb E.symm.measurableEmbedding
        (fun S => ENNReal.ofReal ((frobSq (rmatMul (RmatGnorm r N hN hr pivot z) S)) ^ (-c')))
        (matBox r p T)
      rw [← hpre] at key
      rw [key.symm]
      refine lintegral_congr (fun S => ?_)
      congr 2
      exact frobSq_rmatMul_permGP (RmatG r pivot ((piRatioG r N hN pivot).symm (0, z))) S σr σc
    rw [heq]
    -- RmatGnorm: pivot 1, |entries| ≤ 1 (on the ratio chart z ∈ [−1,1]^N)
    have hpiv : RmatGnorm r N hN hr pivot z ⟨0, by omega⟩ ⟨0, by omega⟩ = 1 :=
      RmatGnorm_pivot r N hN hr pivot z
    have hbd : ∀ a b, |RmatGnorm r N hN hr pivot z a b| ≤ 1 := by
      intro a b
      by_cases hab : a = ⟨0, by omega⟩ ∧ b = ⟨0, by omega⟩
      · rw [hab.1, hab.2, hpiv]; norm_num
      · exact RmatGnorm_offpivot_le r N hN hr pivot z hz a b hab
    exact frobSq_capB_inner_le r p hr (RmatGnorm r N hN hr pivot z) hpiv hbd c' hc0 hc' T hT
  -- integrate the uniform bound over the finite-volume ratio box
  have hbox : (∫⁻ z in (Set.univ.pi (fun _ : Fin N => Set.Icc (-1 : ℝ) 1)),
        innerSGenP r p c' T pivot ((piRatioG r N hN pivot).symm (0, z)))
      ≤ ∫⁻ _z in (Set.univ.pi (fun _ : Fin N => Set.Icc (-1 : ℝ) 1)), C :=
    setLIntegral_mono_ae' (MeasurableSet.univ_pi (fun _ => measurableSet_Icc))
      (ae_of_all _ (fun z hz => hpt z hz))
  refine lt_of_le_of_lt hbox ?_
  rw [setLIntegral_const]
  -- C < ⊤ (Kbound finite for c' < p/2, vol finite) × ratio-box vol finite
  refine ENNReal.mul_lt_top ?_ ?_
  · refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_
    obtain ⟨pm, hpm⟩ : ∃ pm, p = pm + 1 := by
      refine ⟨p - 1, ?_⟩
      have : 0 < p := by by_contra h; push_neg at h; interval_cases p; simp at hc'; linarith
      omega
    have hcap : c' < ((pm + 1 : ℝ)) / 2 := by rw [hpm] at hc'; push_cast at hc'; exact hc'
    have hKfin := Kbound_lt_top pm ((r : ℕ) * T) (by positivity) c' hcap
    refine ENNReal.mul_lt_top ?_ (matBox_volume_lt_top (r - 1) p ((r : ℕ) * T))
    rw [hpm]; exact hKfin
  · exact (isCompact_univ_pi (fun _ => isCompact_Icc)).measure_lt_top

/-- **The `(r,p)` cap-B per-chart finiteness** (`Fin p` analog of `schur_matBoxG_chart_lt_top`). The
radial blow-up chart integral (Jacobian `|y p|^{r²−1}`) is finite for `0 < c' < min(p,r²)/2`, `r ≥ 3`.
The `piRatioG` MP + Tonelli factor the pivot axis (`radial_aAxis_divisor_lt_top`, `c' < r²/2`) from the
`r²−1` ratios; the ratio residual is the cap-B `schurRatioResidP_capB_lt_top` (`c' < p/2`, NO recursion). -/
theorem schur_matBoxGenP_chart_lt_top (r p : ℕ) (hr : 3 ≤ r)
    (c' : ℝ) (hc0 : 0 < c') (hcp : c' < (p : ℝ) / 2) (hcr : c' < (r ^ 2 : ℝ) / 2)
    (pivot : Fin (r * r)) (T : ℝ) (hT : 0 < T) :
    ∫⁻ y in chartDomOn (Finset.univ : Finset (Fin (r * r))) pivot \ pivotZeroOn pivot,
        ENNReal.ofReal |(pivotBlowupOnDeriv (Finset.univ : Finset (Fin (r * r))) pivot y).det|
          * (flatBoxGen r T).indicator (gFlatGen r p c' T) (pivotBlowupOn
              (Finset.univ : Finset (Fin (r * r))) pivot y)
      < ⊤ := by
  have hrr : 0 < r * r := by positivity
  obtain ⟨N, hN⟩ : ∃ N, r * r = N + 1 := ⟨r * r - 1, by omega⟩
  -- |det| = |y pivot|^{r²−1}
  have hdet : ∀ y : Fin (r * r) → ℝ,
      |(pivotBlowupOnDeriv (Finset.univ : Finset (Fin (r * r))) pivot y).det|
        = |y pivot| ^ (r * r - 1) := by
    intro y
    rw [pivotBlowupOnDeriv_det (Finset.univ : Finset (Fin (r * r))) pivot (Finset.mem_univ pivot) y,
      Finset.card_univ, Fintype.card_fin]
    simp [abs_pow]
  simp only [hdet]
  -- the chart domain is measurable
  have hmsD : MeasurableSet
      (chartDomOn (Finset.univ : Finset (Fin (r * r))) pivot \ pivotZeroOn pivot) := by
    refine MeasurableSet.diff ?_ ?_
    · have heq : chartDomOn (Finset.univ : Finset (Fin (r * r))) pivot
          = ⋂ k ∈ (Finset.univ.erase pivot), {y : Fin (r * r) → ℝ | |y k| ≤ 1} := by
        ext y
        simp only [chartDomOn, Set.mem_setOf_eq, Set.mem_iInter, Finset.mem_erase,
          Finset.mem_univ, true_and, and_true, true_implies]
      rw [heq]
      refine Finset.measurableSet_biInter (Finset.univ.erase pivot) (fun k _ => ?_)
      exact measurableSet_le ((measurable_pi_apply k).abs) measurable_const
    · exact (measurable_pi_apply pivot (measurableSet_singleton 0))
  rw [setLIntegral_congr_fun hmsD
    (fun y hy => chart_integrand_factorGen r p c' hc0 T hT pivot y hy.2 hy.1)]
  -- reshape Fin(r*r)→ℝ ≃ ℝ × (Fin N → ℝ) via piRatioG
  set e := piRatioG r N hN pivot with he
  have hmp : MeasurePreserving e (volume) (volume) := measurePreserving_piRatioG r N hN pivot
  -- the chart domain pulls back to ({a ≠ 0}) ×ˢ (ratio box over Fin N)
  have hpre : (chartDomOn (Finset.univ : Finset (Fin (r * r))) pivot \ pivotZeroOn pivot)
      = e ⁻¹' (({a : ℝ | a ≠ 0}) ×ˢ (Set.univ.pi (fun _ : Fin N => Set.Icc (-1 : ℝ) 1))) := by
    ext y
    simp only [chartDomOn, pivotZeroOn, Set.mem_diff, Set.mem_setOf_eq, Set.mem_preimage,
      Set.mem_prod, Set.mem_pi, Set.mem_univ, true_implies, he]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨by rw [piRatioG_apply_fst]; exact h2, fun j => ?_⟩
      rw [Set.mem_Icc, ← abs_le, piRatioG_apply_snd]
      exact h1 _ (Finset.mem_univ _) (piRatioG_ratioIdx_ne r N hN pivot j)
    · rintro ⟨h1, h2⟩
      rw [piRatioG_apply_fst] at h1
      refine ⟨fun k _ hk => ?_, h1⟩
      have hne : finCongr hN k ≠ finCongr hN pivot := fun h => hk ((finCongr hN).injective h)
      obtain ⟨j, hj⟩ := Fin.exists_succAbove_eq hne
      have hk_eq : k = (finCongr hN).symm ((finCongr hN pivot).succAbove j) := by
        rw [hj]; exact ((finCongr hN).symm_apply_apply k).symm
      have hj2 := h2 j
      rw [Set.mem_Icc, ← abs_le, piRatioG_apply_snd r N hN pivot y j] at hj2
      rw [hk_eq]; exact hj2
  set g : (Fin (r * r) → ℝ) → ℝ≥0∞ := fun y =>
    (Set.Icc (-T) T).indicator
        (fun a => ENNReal.ofReal (|a| ^ (((r * r - 1 : ℕ) : ℝ) - 2 * c'))) (y pivot)
      * innerSGenP r p c' T pivot y with hgdef
  have hgmeas : Measurable g := by
    rw [hgdef]
    refine Measurable.mul ?_ (measurable_innerSGenP r p c' T pivot)
    have hind : Measurable (fun a : ℝ =>
        (Set.Icc (-T) T).indicator
          (fun a => ENNReal.ofReal (|a| ^ (((r * r - 1 : ℕ) : ℝ) - 2 * c'))) a) := by
      refine Measurable.indicator ?_ measurableSet_Icc
      exact ENNReal.measurable_ofReal.comp ((measurable_id.abs).pow_const _)
    exact hind.comp (measurable_pi_apply pivot)
  rw [hpre]
  have hSms : MeasurableSet
      (({a : ℝ | a ≠ 0}) ×ˢ (Set.univ.pi (fun _ : Fin N => Set.Icc (-1 : ℝ) 1))) :=
    MeasurableSet.prod (by measurability) (MeasurableSet.univ_pi (fun _ => measurableSet_Icc))
  have key := hmp.setLIntegral_comp_preimage_emb e.measurableEmbedding (fun q => g (e.symm q))
    (({a : ℝ | a ≠ 0}) ×ˢ (Set.univ.pi (fun _ : Fin N => Set.Icc (-1 : ℝ) 1)))
  have htrans : (∫⁻ y in e ⁻¹' (({a : ℝ | a ≠ 0}) ×ˢ
        (Set.univ.pi (fun _ : Fin N => Set.Icc (-1 : ℝ) 1))), g y)
      = ∫⁻ q in (({a : ℝ | a ≠ 0}) ×ˢ (Set.univ.pi (fun _ : Fin N => Set.Icc (-1 : ℝ) 1))),
          g (e.symm q) := by
    rw [← key]
    refine setLIntegral_congr_fun (e.measurable hSms) (fun y _ => ?_)
    rw [MeasurableEquiv.symm_apply_apply]
  rw [htrans]
  have hgsymm_meas : Measurable (fun q : ℝ × (Fin N → ℝ) => g (e.symm q)) :=
    hgmeas.comp e.symm.measurable
  rw [Measure.volume_eq_prod ℝ (Fin N → ℝ), setLIntegral_prod _ hgsymm_meas.aemeasurable]
  -- the joint factorisation: g (e.symm (a,z)) = radInd a · innerSGenP … (e.symm (0,z))
  have hfactor : ∀ a : ℝ, ∀ z : Fin N → ℝ,
      g (e.symm (a, z))
        = (Set.Icc (-T) T).indicator
            (fun a => ENNReal.ofReal (|a| ^ (((r * r - 1 : ℕ) : ℝ) - 2 * c'))) a
          * innerSGenP r p c' T pivot (e.symm (0, z)) := by
    intro a z
    have hp_eq : (e.symm (a, z)) pivot = a := by rw [he]; exact piRatioG_symm_pivot r N hN pivot a z
    have hoff : innerSGenP r p c' T pivot (e.symm (a, z))
        = innerSGenP r p c' T pivot (e.symm (0, z)) := by
      refine innerSGenP_offpivot r p c' T pivot _ _ (fun i hi => ?_)
      rw [he]; exact piRatioG_symm_offpivot r N hN pivot a 0 z i hi
    show (Set.Icc (-T) T).indicator
        (fun a => ENNReal.ofReal (|a| ^ (((r * r - 1 : ℕ) : ℝ) - 2 * c'))) ((e.symm (a, z)) pivot)
        * innerSGenP r p c' T pivot (e.symm (a, z)) = _
    rw [hp_eq, hoff]
  -- radial-axis factor finite (c' < r²/2 ⟹ exponent (r²−1)−2c' > −1)
  have hN3a : (∫⁻ a in Set.Icc (-T) T,
      ENNReal.ofReal (|a| ^ ((r ^ 2 : ℝ) - 1 - 2 * c'))) < ⊤ :=
    radial_aAxis_divisor_lt_top r (by omega) T hT c' hcr
  have hexp : ((r ^ 2 : ℝ) - 1 - 2 * c') = (((r * r - 1 : ℕ) : ℝ) - 2 * c') := by
    rw [Nat.cast_sub (by omega), Nat.cast_one]; push_cast [pow_two]; ring
  rw [hexp] at hN3a
  have hradfin : (∫⁻ a in {a : ℝ | a ≠ 0},
        (Set.Icc (-T) T).indicator
          (fun a => ENNReal.ofReal (|a| ^ (((r * r - 1 : ℕ) : ℝ) - 2 * c'))) a) < ⊤ := by
    have hle1 : (∫⁻ a in {a : ℝ | a ≠ 0},
          (Set.Icc (-T) T).indicator
            (fun a => ENNReal.ofReal (|a| ^ (((r * r - 1 : ℕ) : ℝ) - 2 * c'))) a)
        ≤ ∫⁻ a, (Set.Icc (-T) T).indicator
            (fun a => ENNReal.ofReal (|a| ^ (((r * r - 1 : ℕ) : ℝ) - 2 * c'))) a := by
      have := lintegral_mono_set (μ := volume) (s := {a : ℝ | a ≠ 0}) (t := Set.univ)
        (Set.subset_univ _)
        (f := (Set.Icc (-T) T).indicator
          (fun a => ENNReal.ofReal (|a| ^ (((r * r - 1 : ℕ) : ℝ) - 2 * c'))))
      rwa [setLIntegral_univ] at this
    have heq2 : (∫⁻ a, (Set.Icc (-T) T).indicator
          (fun a => ENNReal.ofReal (|a| ^ (((r * r - 1 : ℕ) : ℝ) - 2 * c'))) a)
        = ∫⁻ a in Set.Icc (-T) T, ENNReal.ofReal (|a| ^ (((r * r - 1 : ℕ) : ℝ) - 2 * c')) :=
      lintegral_indicator measurableSet_Icc _
    rw [heq2] at hle1
    exact lt_of_le_of_lt hle1 hN3a
  -- ratio residual finite via the cap-B schurRatioResidP_capB_lt_top
  have hratiofin : (∫⁻ z in (Set.univ.pi (fun _ : Fin N => Set.Icc (-1 : ℝ) 1)),
        innerSGenP r p c' T pivot (e.symm (0, z))) < ⊤ :=
    schurRatioResidP_capB_lt_top r N p hN hr c' hc0 hcp pivot T hT
  have hinner : ∀ a : ℝ,
      (∫⁻ z in (Set.univ.pi (fun _ : Fin N => Set.Icc (-1 : ℝ) 1)), g (e.symm (a, z)))
        = (Set.Icc (-T) T).indicator
            (fun a => ENNReal.ofReal (|a| ^ (((r * r - 1 : ℕ) : ℝ) - 2 * c'))) a
          * ∫⁻ z in (Set.univ.pi (fun _ : Fin N => Set.Icc (-1 : ℝ) 1)),
              innerSGenP r p c' T pivot (e.symm (0, z)) := by
    intro a
    have hradne : (Set.Icc (-T) T).indicator
        (fun a => ENNReal.ofReal (|a| ^ (((r * r - 1 : ℕ) : ℝ) - 2 * c'))) a ≠ ⊤ := by
      rw [Set.indicator_apply]; split <;> simp [ENNReal.ofReal_ne_top]
    rw [lintegral_congr (fun z => hfactor a z), lintegral_const_mul' _ _ hradne]
  rw [lintegral_congr hinner, lintegral_mul_const' _ _ hratiofin.ne]
  exact ENNReal.mul_lt_top hradfin hratiofin

/-- **The cap-B directMorse finiteness.** `SchurCore p r c' T` for `0 < c' < min(p, r²)/2` (the cap-B regime,
where the binding stratum is `t = 0`, so `½·minAdm = r²/2 ≤ p/2`). The `r²`-chart radial-`Δ` cover
(`matBoxGen_outer_flat` + `gFlatGen_cover_sum`, DONE `(r,p)`-general) reduces to a sum over `r²` charts; each
chart = the radial axis `|y|^{r²−1−2c'}` (`radial_aAxis_divisor_lt_top`, DONE, `c' < r²/2`) × the angular
residual (`schurRatioResidP_capB_lt_top`, `c' < p/2`). NO recursion (unlike the cap-A firing). -/
theorem schurCoreP_directMorse (p r : ℕ) (hr : 3 ≤ r) (c' : ℝ) (hc0 : 0 < c')
    (hcp : c' < (p : ℝ) / 2) (hcr : c' < (r ^ 2 : ℝ) / 2) (T : ℝ) (hT : 0 < T) :
    SchurCore p r c' T := by
  rw [SchurCore, matBoxGen_outer_flat r p c' T, gFlatGen_cover_sum r p (by positivity) c' T]
  exact ENNReal.sum_lt_top.2
    (fun q _ => schur_matBoxGenP_chart_lt_top r p hr c' hc0 hcp hcr q T hT)

end DLNFibre.DLN.RLCT
