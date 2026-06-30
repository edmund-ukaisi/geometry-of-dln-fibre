import DLNFibre.DLN.RLCT.Validate.RouteMSchurRectShear
import DLNFibre.DLN.RLCT.Validate.RouteMSchurRectPeel
import DLNFibre.DLN.RLCT.Validate.RouteMSchurRect

/-!
# `DLNFibre.DLN.RLCT.Validate.RouteMSchurRectAssemble` — the RECTANGULAR carve heart + assembly (3b-carve + 3b-assemble)

(Renamed from `RouteMSchurRectCarve` to avoid the filename collision with genm-rectfill's
`RouteMSchurRectCarve.lean`, which independently carries 3b-pos + 3b-peel under identical names. The heart
here consumes `frobSqShiftRect_ne_zero_ae` (3b-pos) + `resolvedShiftRRect_le` / `coreSchurValRect` (3b-peel)
BY NAME — currently from `RouteMSchurRectPos` / `RouteMSchurRectPeel`; at integration the import can be
re-pointed to genm-rectfill's `RouteMSchurRectCarve` with no proof edits, since the signatures match.)

The asymmetric (`R : Fin m → Fin n` RECTANGULAR) generalisation of the square `Fin p`-width cap-A carve
(`RouteMSchurCapACarveP.innerSGenCarveP_le` / `schurRatioResidGenP_mid` / `schurRatioResidGenP`, where the
angular matrix is square `Fin r → Fin r`).

* `innerSGenCarveRect_le` — **THE HEART** (the per-`(M,v)` carve bound, `M` free): for the carved angular
  matrix `R = RmatRectNorm (zERect.symm (M,v))` (pivot `1`, `|entries| ≤ 1`), `p/2 < c'`, the inner-`S`
  integral over `matBox n p T` is bounded by `ofReal(c₀^{−c'})` times the per-`M` resolved slice — N2b
  (`t = 1`) lower-bounds `frobSq(R·S)`, the top-row bridge (`frobSqTopRowRect_eq_shear`) + `stepShearRect_r`
  peel the `Fin p` Morse spectator, and `ScCarve_rect_eq` turns `Sc` into `M(a,b) − bgShiftRect v a b`.
* `schurRatioResidRect_mid` / `schurRatioResidRect` — the carve assembly + subcritical fold: the JOINT
  `∫_z∫_S` over the `mn−1` angular ratios is finite below `rectSchurLambda p m n`, via `zERect` CoV +
  `resolvedShiftRRect_le` + the rectangular lower IH `RectSchurLowerIH`.
-/

open MeasureTheory Set
open scoped ENNReal BigOperators
namespace DLNFibre.DLN.RLCT

/-! ## The `zERect` forward readbacks + the lower-IH core finiteness -/

/-- `(zERect z).1 ik = z (zσRect.symm (inl ik))` — the forward `zERect` reads the `M22`-cube slot. The
rectangular analog of `zEG_fst_apply`. -/
theorem zERect_fst_apply (m n N : ℕ) (hN : m * n = N + 1) (hm : 1 ≤ m) (hn : 1 ≤ n)
    (hmn : 2 ≤ m * n) (pv : Fin (m * n)) (z : Fin N → ℝ) (ik : Fin (m - 1) × Fin (n - 1)) :
    (zERect m n N hN hm hn hmn pv z).1 ik = z ((zσRect m n N hN hm hn hmn pv).symm (Sum.inl ik)) := by
  have : (zERect m n N hN hm hn hmn pv z).1 ik
      = MeasurableEquiv.piCongrLeft
          (fun _ : (Fin (m - 1) × Fin (n - 1)) ⊕ (Fin (m - 1) ⊕ Fin (n - 1)) => ℝ)
          (zσRect m n N hN hm hn hmn pv) z (Sum.inl ik) := rfl
  rw [this, ← Equiv.apply_symm_apply (zσRect m n N hN hm hn hmn pv) (Sum.inl ik),
    MeasurableEquiv.piCongrLeft_apply_apply, Equiv.apply_symm_apply]

/-- `(zERect z).2 s = z (zσRect.symm (inr s))` — the forward `zERect` reads the `(g,b)`-cube slot. The
rectangular analog of `zEG_snd_apply`. -/
theorem zERect_snd_apply (m n N : ℕ) (hN : m * n = N + 1) (hm : 1 ≤ m) (hn : 1 ≤ n)
    (hmn : 2 ≤ m * n) (pv : Fin (m * n)) (z : Fin N → ℝ) (s : Fin (m - 1) ⊕ Fin (n - 1)) :
    (zERect m n N hN hm hn hmn pv z).2 s = z ((zσRect m n N hN hm hn hmn pv).symm (Sum.inr s)) := by
  have : (zERect m n N hN hm hn hmn pv z).2 s
      = MeasurableEquiv.piCongrLeft
          (fun _ : (Fin (m - 1) × Fin (n - 1)) ⊕ (Fin (m - 1) ⊕ Fin (n - 1)) => ℝ)
          (zσRect m n N hN hm hn hmn pv) z (Sum.inr s) := rfl
  rw [this, ← Equiv.apply_symm_apply (zσRect m n N hN hm hn hmn pv) (Sum.inr s),
    MeasurableEquiv.piCongrLeft_apply_apply, Equiv.apply_symm_apply]

/-- **The rectangular lower-IH core finiteness.** `coreSchurValRect (m−1) (n−1) p c'' Kr < ⊤` from the
rectangular lower IH at `j = 1`: it is exactly `RectSchurCore (m−1) (n−1) p c'' Kr` (`Iff.rfl`), supplied
by `hIH 1` for `0 < c'' < rectSchurLambda p (m−1) (n−1)`, `0 < Kr`. The rectangular analog of
`coreSchurGenValP_lt_top`. -/
theorem coreSchurValRect_lt_top (m n p : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n)
    (hIH : RectSchurLowerIH p (rectSchurLambda p) m n)
    (c'' : ℝ) (hc0 : 0 < c'') (hclam : c'' < rectSchurLambda p (m - 1) (n - 1))
    (Kr : ℝ) (hKr : 0 < Kr) :
    coreSchurValRect (m - 1) (n - 1) p c'' Kr < ⊤ := by
  have hcore : RectSchurCore (m - 1) (n - 1) p c'' Kr :=
    hIH 1 (le_refl 1) (by omega) (by omega) c'' hc0 hclam Kr hKr
  rwa [RectSchurCore] at hcore

/-! ## The carve heart (the per-`(M,v)` bound, `M` free) -/

/-- **The per-`(M,v)` rectangular carve bound (the firing heart, `M` FREE).** For the carved angular matrix
`R = RmatRectNorm (zERect.symm (M,v))` (pivot `1`, `|entries| ≤ 1` when `M,v ∈ [−1,1]`), `p/2 < c'`, the
inner-`S` integral over `matBox n p T` is bounded by `ofReal(c₀^{−c'})` times the per-`M` resolved slice
(radius `K = max 1 (n·T)`, shift `Sh = bgShiftRect v`). N2b (`t = 1`) lower-bounds `frobSq(R·S)` by
`c₀·(frobSq row0 + frobSq(Sc·S_bot))`; the top-row bridge (`frobSqTopRowRect_eq_shear`) + `stepShearRect_r`
peel the `Fin p` Morse spectator; `ScCarve_rect_eq` turns `Sc` into `M(a,b) − bgShiftRect v a b`. The
rectangular analog of `innerSGenCarveP_le` (residual `Sc : (m−1)×(n−1)`, shear over the `Fin (n−1)`
columns). -/
theorem innerSGenCarveRect_le (m n N p : ℕ) (hN : m * n = N + 1) (hm : 1 ≤ m) (hn : 1 ≤ n)
    (hmn : 2 ≤ m * n) (hp : 0 < p) (c' : ℝ) (hcp : (p : ℝ) / 2 < c')
    (pv : Fin (m * n)) (T : ℝ) (hT : 0 < T)
    (M : (Fin (m - 1) × Fin (n - 1)) → ℝ) (v : (Fin (m - 1) ⊕ Fin (n - 1)) → ℝ)
    (hM : M ∈ Set.univ.pi (fun _ : (Fin (m - 1) × Fin (n - 1)) => Set.Icc (-1 : ℝ) 1))
    (hv : v ∈ Set.univ.pi (fun _ : (Fin (m - 1) ⊕ Fin (n - 1)) => Set.Icc (-1 : ℝ) 1)) :
    (∫⁻ S in matBox n p T,
        ENNReal.ofReal ((frobSq (rmatMul (RmatRectNorm m n N hN hm hn pv
          ((zERect m n N hN hm hn hmn pv).symm (M, v))) S)) ^ (-c')))
      ≤ ENNReal.ofReal
          (((schur_minorPivot_split_rect (m := m) (n := n) (p := p) 1 (by omega) (by omega)).choose)
            ^ (-c'))
        * (∫⁻ S_bot in matBox (n - 1) p (max 1 ((n : ℝ) * T)),
            ∫⁻ T' in morseBox p (max 1 ((n : ℝ) * T)),
              ENNReal.ofReal (((∑ q, (T' q) ^ 2)
                + frobSq (rmatMul (fun a b => M (a, b) - bgShiftRect m n v a b) S_bot)) ^ (-c'))) := by
  classical
  have hc0 : 0 < c' := lt_trans (by positivity) hcp
  set z := (zERect m n N hN hm hn hmn pv).symm (M, v) with hzdef
  set R : Matrix (Fin m) (Fin n) ℝ := Matrix.of (RmatRectNorm m n N hN hm hn pv z) with hRdef
  have hzbox : z ∈ Set.univ.pi (fun _ : Fin N => Set.Icc (-1 : ℝ) 1) := by
    intro k _
    rw [hzdef, zERect_symm_apply]
    rcases (zσRect m n N hN hm hn hmn pv k) with s | s
    · exact hM s (Set.mem_univ s)
    · exact hv s (Set.mem_univ s)
  have hpiv : R ⟨0, by omega⟩ ⟨0, by omega⟩ = 1 := RmatRectNorm_pivot m n N hN hm hn pv z
  have hbd : ∀ a b, |R a b| ≤ 1 := by
    intro a b
    by_cases hab : a = ⟨0, by omega⟩ ∧ b = ⟨0, by omega⟩
    · rw [hab.1, hab.2, hpiv]; norm_num
    · exact RmatRectNorm_offpivot_le m n N hN hm hn pv z hzbox a b hab
  set c₀ := (schur_minorPivot_split_rect (m := m) (n := n) (p := p) 1 (by omega) (by omega)).choose
    with hc₀def
  obtain ⟨c₁, hc₀, hc₁, hN2b⟩ :=
    (schur_minorPivot_split_rect (m := m) (n := n) (p := p) 1 (by omega) (by omega)).choose_spec
  -- the 1×1 pivot minor M11 = [R 0 0] = 1, det 1 ≠ 0
  set M11 : Matrix (Fin 1) (Fin 1) ℝ :=
    Matrix.of (fun a b : Fin 1 => R ⟨a, lt_of_lt_of_le a.2 hm⟩ ⟨b, lt_of_lt_of_le b.2 hn⟩) with hM11
  have hM11_one : M11 = 1 := by
    ext a b; fin_cases a; fin_cases b
    simp only [hM11, Matrix.of_apply, Matrix.one_apply_eq]
    exact hpiv
  have hpivdet : M11.det = 1 := by rw [hM11_one]; simp
  have hpivot : ∀ (I : Fin 1 → Fin m) (J : Fin 1 → Fin n), |(R.submatrix I J).det| ≤ |M11.det| := by
    intro I J
    rw [Matrix.det_fin_one, hpivdet, abs_one, Matrix.submatrix_apply]
    exact hbd (I 0) (J 0)
  have hne : M11.det ≠ 0 := by rw [hpivdet]; norm_num
  -- N2b residual Sc (extract at S = 0 to name it; the per-S split re-derives the same Sc)
  obtain ⟨Sc, hSceq, hlo0, _hup0⟩ := hN2b R (fun _ _ => 0) hbd hpivot hne
  -- the resolved slice integrand X S (top row block + residual Sc·S_bot)
  set X : (Fin n → Fin p → ℝ) → ℝ := fun S =>
    frobSq (fun a : Fin 1 => rmatMul (fun x y => R x y) S ⟨a, lt_of_lt_of_le a.2 hm⟩)
      + frobSq (rmatMul (fun a b => Sc a b) (fun a : Fin (n - 1) => S ⟨1 + a, by omega⟩)) with hXdef
  have hlow : ∀ S, c₀ * X S ≤ frobSq (rmatMul (fun a b => R a b) S) := by
    intro S
    obtain ⟨Sc', hSceq', hlo, _⟩ := hN2b R S hbd hpivot hne
    have hSceq2 : Sc' = Sc := by rw [hSceq', ← hSceq]
    subst hSceq2
    simpa only [hXdef] using hlo
  have hupp : ∀ S, frobSq (rmatMul (fun a b => R a b) S) ≤ c₁ * X S := by
    intro S
    obtain ⟨Sc', hSceq', _, hup⟩ := hN2b R S hbd hpivot hne
    have hSceq2 : Sc' = Sc := by rw [hSceq', ← hSceq]
    subst hSceq2
    simpa only [hXdef] using hup
  have hXnn : ∀ S, 0 ≤ X S := fun S => by
    rw [hXdef]; exact add_nonneg (frobSq_nonneg _) (frobSq_nonneg _)
  have hpt : ∀ S, ENNReal.ofReal ((frobSq (rmatMul (fun a b => R a b) S)) ^ (-c'))
      ≤ ENNReal.ofReal (c₀ ^ (-c')) * ENNReal.ofReal ((X S) ^ (-c')) := by
    intro S
    refine ofReal_rpow_le_const_mul (X S) (frobSq (rmatMul (fun a b => R a b) S)) c₀ c'
      hc0 hc₀ (hXnn S) (frobSq_nonneg _) (hlow S) ?_
    intro hX0
    have := hupp S
    rw [hX0, mul_zero] at this
    exact le_antisymm this (frobSq_nonneg _)
  -- the carve readback: Sc a b = M(a,b) − bgShiftRect v a b
  have hM11_one' : (Matrix.of (fun a b : Fin 1 =>
      R ⟨a, lt_of_lt_of_le a.2 hm⟩ ⟨b, lt_of_lt_of_le b.2 hn⟩))
        = (1 : Matrix (Fin 1) (Fin 1) ℝ) := by
    ext a b; fin_cases a; fin_cases b
    simp only [Matrix.of_apply, Matrix.one_apply_eq]; exact hpiv
  have hM11inv : ∀ s t : Fin 1,
      (Matrix.of (fun a b : Fin 1 =>
        R ⟨a, lt_of_lt_of_le a.2 hm⟩ ⟨b, lt_of_lt_of_le b.2 hn⟩))⁻¹ s t
        = if s = t then 1 else 0 := by
    intro s t; rw [hM11_one']; simp [Matrix.one_apply]
  have hSc_carve : (fun a b => Sc a b)
      = fun (a : Fin (m - 1)) (b : Fin (n - 1)) => M (a, b) - bgShiftRect m n v a b := by
    funext a b
    rw [hSceq]
    simp only [Matrix.sub_apply, Matrix.of_apply, Matrix.mul_apply, hM11inv]
    simp only [Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton, if_true,
      mul_one, mul_ite, mul_zero]
    simp only [hRdef, Matrix.of_apply]
    have hcarve := ScCarve_rect_eq m n N hN hm hn hmn pv M v a b
    have hia : (⟨1 + (a : ℕ), by omega⟩ : Fin m) = ⟨1 + (a : ℕ), by omega⟩ := rfl
    have h0a : (⟨(0 : Fin 1), lt_of_lt_of_le (0 : Fin 1).2 hm⟩ : Fin m) = ⟨0, by omega⟩ := rfl
    have h0b : (⟨(0 : Fin 1), lt_of_lt_of_le (0 : Fin 1).2 hn⟩ : Fin n) = ⟨0, by omega⟩ := rfl
    rw [h0a, h0b] at *
    convert hcarve using 2
  set K := max 1 ((n : ℝ) * T) with hKdef
  have hKpos : 0 < K := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  set bcoup : Fin (n - 1) → ℝ := fun a => R ⟨0, by omega⟩ ⟨1 + (a : ℕ), by omega⟩ with hbcoup
  have hbcoup_le : ∀ a, |bcoup a| ≤ 1 := fun a => hbd _ _
  calc (∫⁻ S in matBox n p T,
          ENNReal.ofReal ((frobSq (rmatMul (fun a b => R a b) S)) ^ (-c')))
      ≤ ∫⁻ S in matBox n p T, ENNReal.ofReal (c₀ ^ (-c')) * ENNReal.ofReal ((X S) ^ (-c')) :=
        lintegral_mono hpt
    _ = ENNReal.ofReal (c₀ ^ (-c'))
          * ∫⁻ S in matBox n p T, ENNReal.ofReal ((X S) ^ (-c')) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ ≤ ENNReal.ofReal (c₀ ^ (-c'))
          * (∫⁻ S_bot in matBox (n - 1) p K, ∫⁻ T' in morseBox p K,
              ENNReal.ofReal (((∑ q, (T' q) ^ 2)
                + frobSq (rmatMul (fun a b => M (a, b) - bgShiftRect m n v a b) S_bot)) ^ (-c'))) := by
        refine mul_le_mul_left' ?_ _
        have hpiv' : (fun x y => R x y) ⟨0, by omega⟩ ⟨0, by omega⟩ = 1 := hpiv
        have hXrw : ∀ S, X S
            = (∑ q, (S ⟨0, by omega⟩ q
                + ∑ a, bcoup a * S ⟨1 + (a : ℕ), by omega⟩ q) ^ 2)
              + frobSq (rmatMul (fun a b => Sc a b) (fun a q => S ⟨1 + (a : ℕ), by omega⟩ q)) := by
          intro S
          simp only [hXdef]
          rw [frobSqTopRowRect_eq_shear m n p hm hn (fun x y => R x y) hpiv' S]
        calc (∫⁻ S in matBox n p T, ENNReal.ofReal ((X S) ^ (-c')))
            = ∫⁻ S in matBox n p T,
                ENNReal.ofReal (((∑ q, (S ⟨0, by omega⟩ q
                    + ∑ a, bcoup a * S ⟨1 + (a : ℕ), by omega⟩ q) ^ 2)
                  + frobSq (rmatMul (fun a b => Sc a b)
                      (fun a q => S ⟨1 + (a : ℕ), by omega⟩ q))) ^ (-c')) := by
              refine lintegral_congr (fun S => ?_); rw [hXrw S]
          _ ≤ ∫⁻ S_bot in matBox (n - 1) p T, ∫⁻ T' in morseBox p ((n : ℕ) * T),
                ENNReal.ofReal (((∑ q, (T' q) ^ 2)
                  + frobSq (rmatMul (fun a b => Sc a b) S_bot)) ^ (-c')) :=
              stepShearRect_r (m - 1) n p hn bcoup hbcoup_le (Matrix.of (fun a b => Sc a b)) T hT c'
          _ ≤ ∫⁻ S_bot in matBox (n - 1) p K, ∫⁻ T' in morseBox p K,
                ENNReal.ofReal (((∑ q, (T' q) ^ 2)
                  + frobSq (rmatMul (fun a b => M (a, b) - bgShiftRect m n v a b) S_bot)) ^ (-c')) := by
              have hSsub : matBox (n - 1) p T ⊆ matBox (n - 1) p K := by
                intro Y hY i k; have := Set.mem_Icc.1 (hY i k); rw [Set.mem_Icc]
                have hTK : T ≤ K := le_trans (le_mul_of_one_le_left hT.le
                  (by exact_mod_cast (show (1:ℕ) ≤ n by omega))) (le_max_right _ _)
                constructor <;> [linarith [this.1]; linarith [this.2]]
              have hTsub : morseBox p ((n : ℕ) * T) ⊆ morseBox p K := by
                intro Y hY
                simp only [morseBox, Set.mem_pi, Set.mem_univ, true_implies] at hY ⊢
                intro i
                have hrTK : ((n : ℕ) : ℝ) * T ≤ K := le_max_right _ _
                have := Set.mem_Icc.1 (hY i); rw [Set.mem_Icc]
                constructor <;> [linarith [this.1]; linarith [this.2]]
              refine le_trans (lintegral_mono_set hSsub) ?_
              refine lintegral_mono (fun S_bot => ?_)
              refine le_trans (lintegral_mono_set hTsub) ?_
              refine lintegral_mono (fun T' => ?_)
              rw [show (fun a b => Sc a b)
                  = (fun (a : Fin (m - 1)) (b : Fin (n - 1)) => M (a, b) - bgShiftRect m n v a b)
                from hSc_carve]

/-! ## The rectangular ratio-residual (the carve assembly, mid case) -/

/-- **The rectangular ratio-residual (the carve heart assembled, mid case `p/2 < c' < rectSchurLambda
p m n`).** The JOINT integral over the `mn−1` angular ratios `z` (pivot axis set to `0` via `piRatioRect`)
and `S` is finite for `p/2 < c' < rectSchurLambda p m n`, `2 ≤ m`, `2 ≤ n`: per `z` the angular
`RmatRectNorm` has pivot `1`, `|entries| ≤ 1`; N2b (`t = 1`) peels the top `Fin p` Morse block (threshold
`p/2`), leaving the residual at `c'' = c' − p/2 ∈ (0, rectSchurLambda p (m−1) (n−1))`; the `M22 ↦ Sc`
carving + the rectangular lower IH `hIH` close it. The rectangular analog of `schurRatioResidGenP_mid`. -/
theorem schurRatioResidRect_mid (m n N p : ℕ) (hN : m * n = N + 1) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (hp : 0 < p) (hIH : RectSchurLowerIH p (rectSchurLambda p) m n)
    (c' : ℝ) (hcp : (p : ℝ) / 2 < c') (hc' : c' < rectSchurLambda p m n)
    (pv : Fin (m * n)) (T : ℝ) (hT : 0 < T) :
    (∫⁻ z in (Set.univ.pi (fun _ : Fin N => Set.Icc (-1 : ℝ) 1)),
        innerSRect m n p c' T pv ((piRatioRect m n N hN pv).symm (0, z)))
      < ⊤ := by
  classical
  have hm1 : 1 ≤ m := by omega
  have hn1 : 1 ≤ n := by omega
  have hmn : 2 ≤ m * n := by nlinarith [hm, hn]
  have hc0 : 0 < c' := lt_trans (by positivity) hcp
  set Mbox := Set.univ.pi (fun _ : (Fin (m - 1) × Fin (n - 1)) => Set.Icc (-1 : ℝ) 1) with hMbox
  set vbox := Set.univ.pi (fun _ : (Fin (m - 1) ⊕ Fin (n - 1)) => Set.Icc (-1 : ℝ) 1) with hvbox
  set K := max 1 ((n : ℝ) * T) with hKdef
  have hKpos : 0 < K := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  set c₀ := (schur_minorPivot_split_rect (m := m) (n := n) (p := p) 1 (by omega) (by omega)).choose
    with hc₀def
  -- (1) rewrite the integrand to the pivot-normalised form (innerSRect_eq_norm)
  rw [setLIntegral_congr_fun (MeasurableSet.univ_pi (fun _ => measurableSet_Icc))
    (fun z _ => innerSRect_eq_norm m n N p hN hm1 hn1 c' T pv z)]
  -- (2) CoV via zERect : z ↦ (M,v); box preimage [-1,1]^N = zERect ⁻¹' (Mbox ×ˢ vbox)
  set H : ((Fin (m - 1) × Fin (n - 1) → ℝ) × ((Fin (m - 1) ⊕ Fin (n - 1)) → ℝ)) → ℝ≥0∞ := fun q =>
    ∫⁻ S in matBox n p T,
      ENNReal.ofReal ((frobSq (rmatMul (RmatRectNorm m n N hN hm1 hn1 pv
        ((zERect m n N hN hm1 hn1 hmn pv).symm q)) S)) ^ (-c'))
    with hHdef
  have hHmeas : Measurable H := by
    rw [hHdef]
    apply Measurable.lintegral_prod_right (f := fun q S =>
      ENNReal.ofReal ((frobSq (rmatMul (RmatRectNorm m n N hN hm1 hn1 pv
        ((zERect m n N hN hm1 hn1 hmn pv).symm q)) S)) ^ (-c')))
    apply ENNReal.measurable_ofReal.comp
    apply Measurable.comp (g := fun t : ℝ => t ^ (-c')) (by fun_prop)
    unfold frobSq rmatMul
    refine Finset.measurable_sum _ (fun i _ => Finset.measurable_sum _ (fun j _ => ?_))
    refine Measurable.pow_const (Finset.measurable_sum _ (fun k _ => ?_)) 2
    refine Measurable.mul ?_ ((measurable_pi_apply j).comp ((measurable_pi_apply k).comp measurable_snd))
    have : Measurable (fun q : (Fin (m - 1) × Fin (n - 1) → ℝ) × ((Fin (m - 1) ⊕ Fin (n - 1)) → ℝ) =>
        RmatRectNorm m n N hN hm1 hn1 pv ((zERect m n N hN hm1 hn1 hmn pv).symm q) i k) := by
      unfold RmatRectNorm
      have hz : Measurable (fun q : (Fin (m - 1) × Fin (n - 1) → ℝ) × ((Fin (m - 1) ⊕ Fin (n - 1)) → ℝ) =>
          (zERect m n N hN hm1 hn1 hmn pv).symm q) := (zERect m n N hN hm1 hn1 hmn pv).symm.measurable
      have hsel : Measurable (fun y : Fin N → ℝ =>
          RmatRect m n pv ((piRatioRect m n N hN pv).symm (0, y))
          ((Equiv.swap ((eRect m n).symm pv).1 ⟨0, by omega⟩) i)
          ((Equiv.swap ((eRect m n).symm pv).2 ⟨0, by omega⟩) k)) := by
        simp only [RmatRect_entry]
        by_cases h : eRect m n ((Equiv.swap ((eRect m n).symm pv).1 ⟨0, by omega⟩) i,
            (Equiv.swap ((eRect m n).symm pv).2 ⟨0, by omega⟩) k) = pv
        · simp only [if_pos h]; exact measurable_const
        · simp only [if_neg h]
          exact (measurable_pi_apply _).comp
            (by fun_prop : Measurable (fun y : Fin N → ℝ => (piRatioRect m n N hN pv).symm (0, y)))
      exact hsel.comp hz
    exact this.comp measurable_fst
  have hpre : (Set.univ.pi (fun _ : Fin N => Set.Icc (-1 : ℝ) 1))
      = (zERect m n N hN hm1 hn1 hmn pv) ⁻¹' (Mbox ×ˢ vbox) := by
    ext z
    simp only [Set.mem_preimage, Set.mem_prod, hMbox, hvbox, Set.mem_pi, Set.mem_univ, true_implies]
    constructor
    · intro h
      refine ⟨fun ik => ?_, fun s => ?_⟩
      · rw [zERect_fst_apply]; exact h _
      · rw [zERect_snd_apply]; exact h _
    · rintro ⟨h1, h2⟩ i
      obtain ⟨s, hs⟩ := (zσRect m n N hN hm1 hn1 hmn pv).symm.surjective i
      rcases s with ik | s
      · have := h1 ik; rw [zERect_fst_apply, hs] at this; exact this
      · have := h2 s; rw [zERect_snd_apply, hs] at this; exact this
  rw [hpre]
  have hintegrand : (∫⁻ x in (zERect m n N hN hm1 hn1 hmn pv) ⁻¹' (Mbox ×ˢ vbox),
      ∫⁻ S in matBox n p T,
        ENNReal.ofReal ((frobSq (rmatMul (RmatRectNorm m n N hN hm1 hn1 pv x) S)) ^ (-c')))
      = ∫⁻ x in (zERect m n N hN hm1 hn1 hmn pv) ⁻¹' (Mbox ×ˢ vbox),
          H (zERect m n N hN hm1 hn1 hmn pv x) := by
    refine lintegral_congr (fun x => ?_)
    rw [hHdef]; simp only [MeasurableEquiv.symm_apply_apply]
  rw [hintegrand]
  -- (3) CoV via zERect (MP), Tonelli to v outer
  rw [(measurePreserving_zERect m n N hN hm1 hn1 hmn pv).setLIntegral_comp_preimage_emb
    (zERect m n N hN hm1 hn1 hmn pv).measurableEmbedding H (Mbox ×ˢ vbox)]
  have hMboxms : MeasurableSet Mbox := MeasurableSet.univ_pi (fun _ => measurableSet_Icc)
  have hvboxms : MeasurableSet vbox := MeasurableSet.univ_pi (fun _ => measurableSet_Icc)
  rw [Measure.volume_eq_prod, setLIntegral_prod _ hHmeas.aemeasurable,
    lintegral_lintegral_swap hHmeas.aemeasurable]
  set curryME : (Fin (m - 1) → Fin (n - 1) → ℝ) ≃ᵐ (Fin (m - 1) × Fin (n - 1) → ℝ) :=
    (MeasurableEquiv.piCurry (fun (_ : Fin (m - 1)) (_ : Fin (n - 1)) => ℝ)).symm.trans
      (MeasurableEquiv.arrowCongr' (Equiv.sigmaEquivProd (Fin (m - 1)) (Fin (n - 1)))
        (MeasurableEquiv.refl ℝ)) with hcurryME
  have hcurryMP : MeasurePreserving curryME (volume : Measure (Fin (m - 1) → Fin (n - 1) → ℝ))
      (volume : Measure (Fin (m - 1) × Fin (n - 1) → ℝ)) := by
    rw [hcurryME]
    refine MeasurePreserving.trans ?_ (volume_preserving_arrowCongr'
      (Equiv.sigmaEquivProd (Fin (m - 1)) (Fin (n - 1))) (MeasurableEquiv.refl ℝ)
      (MeasurePreserving.id _))
    exact (measurePreserving_piCurry (fun (_ : Fin (m - 1)) (_ : Fin (n - 1)) => ℝ)
      (fun _ _ => (volume : Measure ℝ))).symm
      (MeasurableEquiv.piCurry (fun (_ : Fin (m - 1)) (_ : Fin (n - 1)) => ℝ))
  have hperv : ∀ v ∈ vbox, (∫⁻ M in Mbox, H (M, v))
      ≤ ENNReal.ofReal (c₀ ^ (-c'))
        * (ENNReal.ofReal (Cresid p c') * coreSchurValRect (m - 1) (n - 1) p (c' - (p : ℝ) / 2) (K + 1)) := by
    intro v hv
    have hMcarve : ∀ M ∈ Mbox, H (M, v)
        ≤ ENNReal.ofReal (c₀ ^ (-c'))
          * (∫⁻ S_bot in matBox (n - 1) p K, ∫⁻ T' in morseBox p K,
              ENNReal.ofReal (((∑ q, (T' q) ^ 2)
                + frobSq (rmatMul (fun a b => M (a, b) - bgShiftRect m n v a b) S_bot)) ^ (-c'))) := by
      intro M hM
      rw [hHdef]
      exact innerSGenCarveRect_le m n N p hN hm1 hn1 hmn hp c' hcp pv T hT M v hM hv
    calc (∫⁻ M in Mbox, H (M, v))
        ≤ ∫⁻ M in Mbox, ENNReal.ofReal (c₀ ^ (-c'))
            * (∫⁻ S_bot in matBox (n - 1) p K, ∫⁻ T' in morseBox p K,
                ENNReal.ofReal (((∑ q, (T' q) ^ 2)
                  + frobSq (rmatMul (fun a b => M (a, b) - bgShiftRect m n v a b) S_bot)) ^ (-c'))) :=
          setLIntegral_mono_ae' hMboxms (ae_of_all _ (fun M hM => hMcarve M hM))
      _ = ENNReal.ofReal (c₀ ^ (-c'))
            * ∫⁻ M in Mbox, (∫⁻ S_bot in matBox (n - 1) p K, ∫⁻ T' in morseBox p K,
                ENNReal.ofReal (((∑ q, (T' q) ^ 2)
                  + frobSq (rmatMul (fun a b => M (a, b) - bgShiftRect m n v a b) S_bot)) ^ (-c'))) := by
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      _ ≤ ENNReal.ofReal (c₀ ^ (-c'))
            * (ENNReal.ofReal (Cresid p c')
              * coreSchurValRect (m - 1) (n - 1) p (c' - (p : ℝ) / 2) (K + 1)) := by
          refine mul_le_mul_left' ?_ _
          have hvabs : ∀ s, |v s| ≤ 1 := by
            intro s; have := Set.mem_Icc.1 (hv s (Set.mem_univ s)); rw [abs_le]; exact this
          have hSh : ∀ i j, |bgShiftRect m n v i j| ≤ (1 : ℝ) := fun i j =>
            bgShiftRect_entry_le m n v hvabs i j
          set G : (Fin (m - 1) × Fin (n - 1) → ℝ) → ℝ≥0∞ := fun M =>
            ∫⁻ S_bot in matBox (n - 1) p K, ∫⁻ T' in morseBox p K,
              ENNReal.ofReal (((∑ q, (T' q) ^ 2)
                + frobSq (rmatMul (fun a b => M (a, b) - bgShiftRect m n v a b) S_bot)) ^ (-c'))
            with hGdef
          have hcov := hcurryMP.setLIntegral_comp_preimage_emb curryME.measurableEmbedding G Mbox
          have hpresub : curryME ⁻¹' Mbox ⊆ matBox (m - 1) (n - 1) K := by
            intro Δ hΔ i k
            have h1K : (1 : ℝ) ≤ K := le_max_left _ _
            have hmem : curryME Δ ∈ Mbox := hΔ
            have : curryME Δ (i, k) ∈ Set.Icc (-1 : ℝ) 1 := hmem (i, k) (Set.mem_univ _)
            have hΔik : Δ i k ∈ Set.Icc (-1 : ℝ) 1 := by
              rw [hcurryME] at this; exact this
            have := Set.mem_Icc.1 hΔik
            rw [Set.mem_Icc]; constructor <;> [linarith [this.1]; linarith [this.2]]
          have hcurryapp : ∀ (Δ : Fin (m - 1) → Fin (n - 1) → ℝ) (a : Fin (m - 1)) (b : Fin (n - 1)),
              curryME Δ (a, b) = Δ a b := fun Δ a b => rfl
          have hGcurry : ∀ Δ : Fin (m - 1) → Fin (n - 1) → ℝ, G (curryME Δ)
              = ∫⁻ S_bot in matBox (n - 1) p K, ∫⁻ T' in morseBox p K,
                  ENNReal.ofReal (((∑ q, (T' q) ^ 2)
                    + frobSq (rmatMul (fun a b => Δ a b - bgShiftRect m n v a b) S_bot)) ^ (-c')) := by
            intro Δ; rw [hGdef]; simp only [hcurryapp]
          calc (∫⁻ M in Mbox, G M)
              = ∫⁻ Δ in curryME ⁻¹' Mbox, G (curryME Δ) := hcov.symm
            _ = ∫⁻ Δ in curryME ⁻¹' Mbox, ∫⁻ S_bot in matBox (n - 1) p K, ∫⁻ T' in morseBox p K,
                  ENNReal.ofReal (((∑ q, (T' q) ^ 2)
                    + frobSq (rmatMul (fun a b => Δ a b - bgShiftRect m n v a b) S_bot)) ^ (-c')) :=
                lintegral_congr (fun Δ => hGcurry Δ)
            _ ≤ ∫⁻ Δ in matBox (m - 1) (n - 1) K, ∫⁻ S_bot in matBox (n - 1) p K, ∫⁻ T' in morseBox p K,
                  ENNReal.ofReal (((∑ q, (T' q) ^ 2)
                    + frobSq (rmatMul (fun a b => Δ a b - bgShiftRect m n v a b) S_bot)) ^ (-c')) :=
                lintegral_mono_set hpresub
            _ ≤ ENNReal.ofReal (Cresid p c')
                  * coreSchurValRect (m - 1) (n - 1) p (c' - (p : ℝ) / 2) (K + 1) :=
                resolvedShiftRRect_le (m - 1) (n - 1) p (by omega) (by omega) hp
                  (bgShiftRect m n v) 1 hSh K hKpos c' hcp
  calc (∫⁻ v in vbox, ∫⁻ M in Mbox, H (M, v))
      ≤ ∫⁻ _v in vbox, ENNReal.ofReal (c₀ ^ (-c'))
          * (ENNReal.ofReal (Cresid p c')
            * coreSchurValRect (m - 1) (n - 1) p (c' - (p : ℝ) / 2) (K + 1)) :=
        setLIntegral_mono_ae' hvboxms (ae_of_all _ (fun v hv => hperv v hv))
    _ = (ENNReal.ofReal (c₀ ^ (-c'))
          * (ENNReal.ofReal (Cresid p c')
            * coreSchurValRect (m - 1) (n - 1) p (c' - (p : ℝ) / 2) (K + 1))) * volume vbox := by
        rw [setLIntegral_const]
    _ < ⊤ := by
        refine ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
          (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_)) ?_
        · -- coreSchurValRect < ⊤ via the rect IH (c' − p/2 < rectSchurLambda p (m−1) (n−1))
          refine coreSchurValRect_lt_top m n p hm1 hn1 hIH (c' - (p : ℝ) / 2) (by linarith) ?_ (K + 1)
            (by linarith)
          -- c' − p/2 < rectSchurLambda p (m−1) (n−1) via the peel j = 1
          have hpeel := (rectSchurLambda_satisfies_threshold p).peel_le (m := m) (n := n) (j := 1)
            (le_refl 1) (by omega) (by omega)
          simp only [Nat.cast_one, one_mul] at hpeel
          linarith
        · rw [hvbox]
          exact (isCompact_univ_pi (fun _ => isCompact_Icc)).measure_lt_top

/-- **The rectangular ratio-residual, all `0 < c' < rectSchurLambda p m n` (subcritical fold).** Mid case
`p/2 < c'` is `schurRatioResidRect_mid`; subcritical `c' ≤ p/2` dominates `F^{−c'} ≤ 1 + F^{−c''}` and
reduces to the `c'' = ½(p/2 + rectSchurLambda p m n)` mid case (`c'' ∈ (p/2, rectSchurLambda p m n)` since
the interior stratum has `rectSchurLambda p m n > p/2`). The rectangular analog of `schurRatioResidGenP`. -/
theorem schurRatioResidRect (m n N p : ℕ) (hN : m * n = N + 1) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (hp : 0 < p) (hIH : RectSchurLowerIH p (rectSchurLambda p) m n)
    (c' : ℝ) (hc0 : 0 < c') (hc' : c' < rectSchurLambda p m n)
    (hmid : (p : ℝ) / 2 < rectSchurLambda p m n) (pv : Fin (m * n)) (T : ℝ) (hT : 0 < T) :
    (∫⁻ z in (Set.univ.pi (fun _ : Fin N => Set.Icc (-1 : ℝ) 1)),
        innerSRect m n p c' T pv ((piRatioRect m n N hN pv).symm (0, z)))
      < ⊤ := by
  have hm1 : 1 ≤ m := by omega
  have hn1 : 1 ≤ n := by omega
  -- the midpoint `c'' = ½(p/2 + rectSchurLambda p m n) ∈ (p/2, rectSchurLambda p m n)`
  set c'' : ℝ := ((p : ℝ) / 2 + rectSchurLambda p m n) / 2 with hc''def
  have hc''lo : (p : ℝ) / 2 < c'' := by rw [hc''def]; linarith
  have hc''hi : c'' < rectSchurLambda p m n := by rw [hc''def]; linarith
  rcases lt_or_ge ((p : ℝ) / 2) c' with hc2 | hc2
  · exact schurRatioResidRect_mid m n N p hN hm hn hp hIH c' hc2 hc' pv T hT
  · -- c' ≤ p/2: dominate the inner integrand by `1 + (·)^{−c''}`, reduce to the c'' mid case
    set q : (Fin N → ℝ) → (Fin (m * n) → ℝ) := fun z => (piRatioRect m n N hN pv).symm (0, z) with hq
    have hdom : ∀ z : Fin N → ℝ,
        innerSRect m n p c' T pv (q z)
          ≤ volume (matBox n p T) + innerSRect m n p c'' T pv (q z) := by
      intro z
      rw [innerSRect, innerSRect]
      calc (∫⁻ S in matBox n p T,
              ENNReal.ofReal ((frobSq (rmatMul (RmatRect m n pv (q z)) S)) ^ (-c')))
          ≤ ∫⁻ S in matBox n p T,
              (1 + ENNReal.ofReal ((frobSq (rmatMul (RmatRect m n pv (q z)) S)) ^ (-c''))) :=
            lintegral_mono (fun S =>
              ofReal_rpow_neg_le_one_addG _ (frobSq_nonneg _) c' c'' hc0 (by linarith))
        _ = volume (matBox n p T) + ∫⁻ S in matBox n p T,
              ENNReal.ofReal ((frobSq (rmatMul (RmatRect m n pv (q z)) S)) ^ (-c'')) := by
            rw [lintegral_add_left measurable_const, setLIntegral_const, one_mul]
    refine lt_of_le_of_lt (lintegral_mono hdom) ?_
    rw [lintegral_add_left measurable_const, setLIntegral_const]
    refine ENNReal.add_lt_top.2 ⟨?_, ?_⟩
    · exact ENNReal.mul_lt_top (matBox_volume_lt_top n p T)
        (by rw [show (Set.univ.pi (fun _ : Fin N => Set.Icc (-1 : ℝ) 1)) = morseBox N 1 from by
          rw [morseBox]]; exact morseBox_volume_lt_top N 1)
    · exact schurRatioResidRect_mid m n N p hN hm hn hp hIH c'' hc''lo hc''hi pv T hT

end DLNFibre.DLN.RLCT
