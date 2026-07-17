import DLNFibre.DLN.RLCT.Validate.RouteMSJFrontSpectral
import DLNFibre.DLN.RLCT.Validate.RouteMSJGammaAtom
import DLNFibre.DLN.RLCT.Validate.RouteMSJRadialPolar
import DLNFibre.DLN.RLCT.Validate.RouteMSJLeafFinite

/-!
# `DLNFibre.DLN.RLCT.Validate.RouteMSJCorankMorse` — the fixed-`S` corank SVD family (§H hole #1)

**Lane-2 Morse hole.** For a FIXED `S`, `frobSq(Γ·S)` is a Morse (smooth-linear-center) singularity: a
PSD quadratic form in `Γ` of rank exactly `a·rank(S)`, zero-locus the linear subspace `{Γ·S=0}`. Below
the tight threshold `2c' < a·rank(S)` the box integral of its `(−c')`-power is finite. This is the
drop-in filler for `corankSVD_chartFamily_lt_top` in `RouteMSJProductCorankEngine`.

Route (l2svd certificate §§1–4):
1. dispatch `rank S = 0` (vacuous by `hthr`), so `r ≥ 1`;
2. bound `box ⊆ matBox a b T` (bounded → sup-cube), monotone;
3. spectral rewrite `frobSq(Γ·S) = ∑_j λ_j ∑_i ((Γ·Q)_{ij})²` (`frobSq_mul_eq_sum_eigenvalues`) +
   orthogonal CoV `Γ↦Γ·Q` (`lintegral_comp_rightMulₚ`, `|det Q|=1`) over an invariant Frobenius ball;
4. floor `∑_j λ_j t_j ≥ σ² ∑_{j∈active} t_j`;
5. active/free column split → `sumSqND_box_lt_top` on the `a·r` active block + finite free volume.

Consumes banked: `frobSq_mul_eq_sum_eigenvalues`, `lintegral_comp_rightMulₚ`/`det_rightMulₚ`,
`sumSqND_box_lt_top`, `eMatFlat`. All finiteness lemmas are stated over ABSTRACT weights `lam`/frame `Q`
(no spectral term), instantiated with the eigenframe only in the final theorem (whnf-timeout discipline).
UNTRACKED; l2engine wires it.
-/

namespace DLNFibre.DLN.RLCT

open Matrix MeasureTheory
open scoped BigOperators ENNReal

/-! ## Part A — orthogonal invariance of `frobSq` (ball invariance for the CoV) -/

/-- **`frobSq` is invariant under right-multiplication by an orthogonal frame.** For `Q·Qᵀ = 1`,
`frobSq (fun i ↦ Γ i ᵥ* Q) = frobSq Γ`. (Trace algebra: `tr(ΓQ QᵀΓᵀ) = tr(Γ Γᵀ)`.) -/
theorem frobSq_vecMul_right {a b : ℕ} (Q : Matrix (Fin b) (Fin b) ℝ) (hQ : Q * Qᵀ = 1)
    (Γ : Fin a → Fin b → ℝ) : frobSq (fun i => Γ i ᵥ* Q) = frobSq Γ := by
  show frobSq (Matrix.of Γ * Q) = frobSq (Matrix.of Γ)
  rw [frobSq_eq_trace (Matrix.of Γ * Q), frobSq_eq_trace (Matrix.of Γ), Matrix.transpose_mul,
    Matrix.mul_assoc (Matrix.of Γ) Q, ← Matrix.mul_assoc Q Qᵀ, hQ, Matrix.one_mul]

/-! ## Part B — the anisotropic floor (strip the eigenweights down to the active block) -/

/-- **The anisotropic floor, pointwise-everywhere.** For nonneg weights `lam` with a positive one,
`(∑_j lam_j t_j)^{−c'} ≤ σ^{−c'}·(∑_{j∈active} t_j)^{−c'}`, `σ = min positive weight > 0`, `t ≥ 0`.
The `∑_{j∈active} t_j = 0` case collapses both sides (mirrors `frobSq_mul_rpow_le_everywhere`). -/
theorem weighted_rpow_le {b : ℕ} (lam : Fin b → ℝ) (hlam : ∀ j, 0 ≤ lam j)
    (hact : (Finset.univ.filter (fun j => 0 < lam j)).Nonempty)
    (c' : ℝ) (hc0 : 0 ≤ c') (t : Fin b → ℝ) (ht : ∀ j, 0 ≤ t j) :
    (∑ j, lam j * t j) ^ (-c')
      ≤ ((Finset.univ.filter (fun j => 0 < lam j)).inf' hact lam) ^ (-c')
        * (∑ j ∈ Finset.univ.filter (fun j => 0 < lam j), t j) ^ (-c') := by
  classical
  set A := Finset.univ.filter (fun j => 0 < lam j) with hA
  set σ := A.inf' hact lam with hσ
  set W := ∑ j ∈ A, t j with hW
  have hσpos : 0 < σ := by
    rw [hσ, Finset.lt_inf'_iff]
    intro j hj; exact (Finset.mem_filter.mp hj).2
  -- σ·W ≤ ∑_j lam_j t_j
  have hlow : σ * W ≤ ∑ j, lam j * t j := by
    have h1 : σ * W = ∑ j ∈ A, σ * t j := by rw [hW, Finset.mul_sum]
    have h2 : ∑ j ∈ A, σ * t j ≤ ∑ j ∈ A, lam j * t j := by
      refine Finset.sum_le_sum (fun j hj => ?_)
      exact mul_le_mul_of_nonneg_right (Finset.inf'_le lam hj) (ht j)
    have h3 : ∑ j ∈ A, lam j * t j ≤ ∑ j, lam j * t j := by
      refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ A) (fun j _ _ => ?_)
      exact mul_nonneg (hlam j) (ht j)
    calc σ * W = ∑ j ∈ A, σ * t j := h1
      _ ≤ ∑ j ∈ A, lam j * t j := h2
      _ ≤ ∑ j, lam j * t j := h3
  by_cases hW0 : W = 0
  · -- W = 0 ⟹ all active t vanish ⟹ ∑_j lam_j t_j = 0
    have hsum0 : ∑ j, lam j * t j = 0 := by
      refine Finset.sum_eq_zero (fun j _ => ?_)
      by_cases hj : 0 < lam j
      · have hjA : j ∈ A := Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩
        have htj : t j = 0 := (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => ht k)).mp
          (hW.symm.trans hW0) j hjA
        rw [htj, mul_zero]
      · have : lam j = 0 := le_antisymm (not_lt.mp hj) (hlam j)
        rw [this, zero_mul]
    rw [hsum0, hW0]
    rcases eq_or_lt_of_le hc0 with hc'0 | hc'pos
    · rw [← hc'0]; norm_num
    · rw [Real.zero_rpow (by linarith : -c' ≠ 0), mul_zero]
  · -- W > 0
    have hWpos : 0 < W := lt_of_le_of_ne (Finset.sum_nonneg (fun j _ => ht j)) (Ne.symm hW0)
    have hσW : (0:ℝ) < σ * W := mul_pos hσpos hWpos
    calc (∑ j, lam j * t j) ^ (-c')
        ≤ (σ * W) ^ (-c') := Real.rpow_le_rpow_of_nonpos hσW hlow (by linarith)
      _ = σ ^ (-c') * W ^ (-c') := Real.mul_rpow hσpos.le hWpos.le

/-! ## Part C — the sum-of-squares box integral over an arbitrary finite index -/

/-- **`sumSqND_box_lt_top` over an arbitrary finite index `ι`.** Reindex `ι ≃ Fin (card ι)` by
`arrowCongr'` (measure-preserving), then the banked `sumSqND_box_lt_top`. -/
theorem sumSq_genBox_lt_top {ι : Type*} [Fintype ι] (hpos : 0 < Fintype.card ι)
    (c' : ℝ) (hc' : c' < (Fintype.card ι : ℝ) / 2) (T : ℝ) (hT : 0 < T) :
    ∫⁻ x in Set.univ.pi (fun _ : ι => Set.Icc (-T) T),
        ENNReal.ofReal ((∑ k, (x k) ^ 2) ^ (-c')) < ⊤ := by
  classical
  obtain ⟨m, hm⟩ : ∃ m, Fintype.card ι = m + 1 := ⟨Fintype.card ι - 1, by omega⟩
  set eq : ι ≃ Fin (m + 1) := Fintype.equivFinOfCardEq hm with heq
  set e : (ι → ℝ) ≃ᵐ (Fin (m + 1) → ℝ) := MeasurableEquiv.arrowCongr' eq (MeasurableEquiv.refl ℝ)
    with hedef
  have happly : ∀ (x : ι → ℝ) (i : Fin (m + 1)), e x i = x (eq.symm i) := fun x i => rfl
  have hmp : MeasurePreserving e :=
    volume_preserving_arrowCongr' eq (MeasurableEquiv.refl ℝ) (MeasurePreserving.id _)
  -- `e ⁻¹' morseBox (m+1) T = genBox ι T`
  have hpre : e ⁻¹' morseBox (m + 1) T = Set.univ.pi (fun _ : ι => Set.Icc (-T) T) := by
    ext x
    simp only [Set.mem_preimage, morseBox, Set.mem_pi, Set.mem_univ, true_implies, happly]
    exact ⟨fun h k => by simpa using h (eq k), fun h i => h (eq.symm i)⟩
  -- the integrand transports to the flat sum of squares
  have hcongr : ∀ x : ι → ℝ, ENNReal.ofReal ((∑ k, (x k) ^ 2) ^ (-c'))
      = (fun y : Fin (m + 1) → ℝ => ENNReal.ofReal ((∑ i, (y i) ^ 2) ^ (-c'))) (e x) := by
    intro x
    simp only [happly]
    rw [← Equiv.sum_comp eq.symm (fun k => (x k) ^ 2)]
  rw [show (Set.univ.pi (fun _ : ι => Set.Icc (-T) T)) = e ⁻¹' morseBox (m + 1) T from hpre.symm,
    setLIntegral_congr_fun ((morseBox_measurableSet (m + 1) T).preimage e.measurable)
      (fun x _ => hcongr x),
    hmp.setLIntegral_comp_preimage_emb e.measurableEmbedding
      (fun y => ENNReal.ofReal ((∑ i, (y i) ^ 2) ^ (-c'))) (morseBox (m + 1) T)]
  refine sumSqND_box_lt_top m T hT c' ?_
  have : ((m : ℝ) + 1) = (Fintype.card ι : ℝ) := by rw [hm]; push_cast; ring
  rw [this]; exact hc'

/-! ## Part D — the active/free split (integrate out the coordinates the loss ignores) -/

/-- **The subset sum-of-squares box integral is finite below `#active/2`.** For a predicate `p` on
`Fin n` with `1 ≤ #{k // p k}` and `c' < #{k // p k}/2`, the box integral of `(∑_{k∈active}(x k)²)^{−c'}`
is finite: split off the free coordinates (Tonelli), close the active block with `sumSq_genBox_lt_top`. -/
theorem sumSqSubset_morseBox_lt_top {n : ℕ} (p : Fin n → Prop) [DecidablePred p]
    (hpos : 0 < Fintype.card {k // p k}) (c' : ℝ)
    (hc' : c' < (Fintype.card {k // p k} : ℝ) / 2) (T : ℝ) (hT : 0 < T) :
    ∫⁻ x in morseBox n T,
        ENNReal.ofReal ((∑ k ∈ Finset.univ.filter p, (x k) ^ 2) ^ (-c')) < ⊤ := by
  classical
  set boxA : Set ({k // p k} → ℝ) := Set.univ.pi (fun _ => Set.Icc (-T) T) with hboxA
  set boxF : Set ({k // ¬p k} → ℝ) := Set.univ.pi (fun _ => Set.Icc (-T) T) with hboxF
  set e := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Fin n => ℝ) p with hedef
  have hmp : MeasurePreserving e := volume_preserving_piEquivPiSubtypeProd (fun _ : Fin n => ℝ) p
  -- component: `(e x).1 k = x k.val`
  have hfst : ∀ (x : Fin n → ℝ) (k : {k // p k}), (e x).1 k = x k.val := fun x k => rfl
  set G : (({k // p k} → ℝ) × ({k // ¬p k} → ℝ)) → ℝ≥0∞ :=
    fun yz => ENNReal.ofReal ((∑ k, (yz.1 k) ^ 2) ^ (-c')) with hGdef
  have hGmeas : Measurable G := by
    refine ENNReal.measurable_ofReal.comp ((by fun_prop : Measurable fun s : ℝ => s ^ (-c')).comp ?_)
    exact Finset.measurable_sum _ (fun k _ => by fun_prop)
  -- morseBox n T = e ⁻¹' (boxA ×ˢ boxF)
  have hpre : morseBox n T = e ⁻¹' (boxA ×ˢ boxF) := by
    ext x
    simp only [morseBox, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_preimage, Set.mem_prod,
      hboxA, hboxF, hedef]
    constructor
    · intro h; exact ⟨fun k => h k.val, fun k => h k.val⟩
    · rintro ⟨h1, h2⟩ k
      by_cases hk : p k
      · exact h1 ⟨k, hk⟩
      · exact h2 ⟨k, hk⟩
  -- the integrand transports to `G ∘ e`
  have hcongr : ∀ x, ENNReal.ofReal ((∑ k ∈ Finset.univ.filter p, (x k) ^ 2) ^ (-c')) = G (e x) := by
    intro x
    simp only [hGdef, hfst]
    rw [← Finset.sum_subtype (Finset.univ.filter p)
      (fun k => by simp only [Finset.mem_filter, Finset.mem_univ, true_and]) (fun k => (x k) ^ 2)]
  rw [hpre, setLIntegral_congr_fun ((MeasurableSet.univ_pi (fun _ => measurableSet_Icc)).prod
      (MeasurableSet.univ_pi (fun _ => measurableSet_Icc)) |>.preimage e.measurable)
      (fun x _ => hcongr x),
    hmp.setLIntegral_comp_preimage_emb e.measurableEmbedding G (boxA ×ˢ boxF),
    Measure.volume_eq_prod,
    setLIntegral_prod G hGmeas.aemeasurable]
  -- inner integral: `G` is constant in the free block
  have hinner : ∀ y : {k // p k} → ℝ,
      ∫⁻ z in boxF, G (y, z) = ENNReal.ofReal ((∑ k, (y k) ^ 2) ^ (-c')) * volume boxF := by
    intro y
    rw [show (∫⁻ z in boxF, G (y, z))
      = ∫⁻ _ in boxF, ENNReal.ofReal ((∑ k, (y k) ^ 2) ^ (-c')) from rfl, setLIntegral_const]
  simp only [hinner]
  rw [lintegral_mul_const' _ _ (by
    exact ne_of_lt ((isCompact_univ_pi (fun _ => isCompact_Icc)).measure_lt_top))]
  refine ENNReal.mul_lt_top ?_ ((isCompact_univ_pi (fun _ => isCompact_Icc)).measure_lt_top)
  exact sumSq_genBox_lt_top hpos c' hc' T hT

/-- **The active-columns sum-of-squares box integral is finite below `a·#active/2`.** Matrix version of
`sumSqSubset_morseBox_lt_top`: flatten `matBox` to `morseBox (a·b)` via the banked `eMatFlat`, whose
active flat-index count is `a·#{j // P j}`. -/
theorem sumSqActiveCols_matBox_lt_top {a b : ℕ} (P : Fin b → Prop) [DecidablePred P]
    (hpos : 0 < a * Fintype.card {j // P j})
    (c' : ℝ) (hc' : c' < (a * Fintype.card {j // P j} : ℝ) / 2) (T : ℝ) (hT : 0 < T) :
    ∫⁻ Γ in matBox a b T,
        ENNReal.ofReal ((∑ j ∈ Finset.univ.filter P, ∑ i, (Γ i j) ^ 2) ^ (-c')) < ⊤ := by
  let pf : Fin (a * b) → Prop := fun k => P ((sigFlatEquiv a b).symm k).2
  haveI hpfdec : DecidablePred pf := fun k => (inferInstance : Decidable (P _))
  have hmp := measurePreserving_eMatFlat a b
  -- the active double-sum flattens to a filtered flat sum
  have hsum : ∀ Γ : Fin a → Fin b → ℝ,
      (∑ k ∈ Finset.univ.filter pf, (eMatFlat a b Γ k) ^ 2)
        = ∑ j ∈ Finset.univ.filter P, ∑ i, (Γ i j) ^ 2 := by
    intro Γ
    calc ∑ k ∈ Finset.univ.filter pf, (eMatFlat a b Γ k) ^ 2
        = ∑ k, (if pf k then (eMatFlat a b Γ k) ^ 2 else 0) := by rw [Finset.sum_filter]
      _ = ∑ k, (if P ((sigFlatEquiv a b).symm k).2
            then (Γ ((sigFlatEquiv a b).symm k).1 ((sigFlatEquiv a b).symm k).2) ^ 2 else 0) := by
          refine Finset.sum_congr rfl (fun k _ => ?_); rw [eMatFlat_apply]
      _ = ∑ kj : (_ : Fin a) × Fin b, (if P kj.2 then (Γ kj.1 kj.2) ^ 2 else 0) := by
          refine Fintype.sum_equiv (sigFlatEquiv a b).symm
            (fun k => if P ((sigFlatEquiv a b).symm k).2
              then (Γ ((sigFlatEquiv a b).symm k).1 ((sigFlatEquiv a b).symm k).2) ^ 2 else 0)
            (fun kj => if P kj.2 then (Γ kj.1 kj.2) ^ 2 else 0) (fun k => ?_)
          by_cases hk : P ((sigFlatEquiv a b).symm k).2 <;> simp only [hk, if_true, if_false]
      _ = ∑ i, ∑ j, (if P j then (Γ i j) ^ 2 else 0) := by rw [Fintype.sum_sigma]
      _ = ∑ i, ∑ j ∈ Finset.univ.filter P, (Γ i j) ^ 2 := by
          refine Finset.sum_congr rfl (fun i _ => ?_); rw [Finset.sum_filter]
      _ = ∑ j ∈ Finset.univ.filter P, ∑ i, (Γ i j) ^ 2 := Finset.sum_comm
  -- the active flat-index count is `a · #active`
  have hcard : Fintype.card {k // pf k} = a * Fintype.card {j // P j} := by
    rw [Fintype.card_subtype, Fintype.card_subtype, Finset.card_filter, Finset.card_filter]
    calc ∑ k, (if pf k then 1 else 0)
        = ∑ kj : (_ : Fin a) × Fin b, (if P kj.2 then (1 : ℕ) else 0) := by
          refine Fintype.sum_equiv (sigFlatEquiv a b).symm
            (fun k => if P ((sigFlatEquiv a b).symm k).2 then (1 : ℕ) else 0)
            (fun kj => if P kj.2 then (1 : ℕ) else 0) (fun k => ?_)
          by_cases hk : P ((sigFlatEquiv a b).symm k).2 <;> simp only [hk, if_true, if_false]
      _ = ∑ _i : Fin a, ∑ j, (if P j then (1 : ℕ) else 0) := by rw [Fintype.sum_sigma]
      _ = a * ∑ j, (if P j then (1 : ℕ) else 0) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  -- transport `matBox → morseBox` and close with the flat split
  have hpos' : 0 < Fintype.card {k // pf k} := by rw [hcard]; exact hpos
  have hc2 : c' < (Fintype.card {k // pf k} : ℝ) / 2 := by rw [hcard]; push_cast; exact hc'
  rw [matBox_eq_eMatFlat_preimage a b T,
    setLIntegral_congr_fun ((morseBox_measurableSet (a * b) T).preimage (eMatFlat a b).measurable)
      (fun Γ _ => by rw [← hsum Γ]),
    hmp.setLIntegral_comp_preimage_emb (eMatFlat a b).measurableEmbedding
      (fun x => ENNReal.ofReal ((∑ k ∈ Finset.univ.filter pf, (x k) ^ 2) ^ (-c'))) (morseBox (a * b) T)]
  exact sumSqSubset_morseBox_lt_top pf hpos' c' hc2 T hT

/-! ## Part F — the anisotropic (eigen-weighted) box integral is finite below the tight threshold -/

/-- **The anisotropic weighted quadratic form is box-integrable below `a·#active/2`.** For nonneg weights
`lam` with `2c' < a·#{j // 0 < lam j}`, the box integral of `(∑_j lam_j ∑_i Γ_ij²)^{−c'}` is finite:
the floor `weighted_rpow_le` strips it to the active columns, then `sumSqActiveCols_matBox_lt_top`. -/
theorem weightedForm_matBox_lt_top {a b : ℕ} (lam : Fin b → ℝ) (hlam : ∀ j, 0 ≤ lam j)
    (c' : ℝ) (hc0 : 0 ≤ c') (hc' : 2 * c' < (a : ℝ) * (Fintype.card {j // 0 < lam j} : ℝ))
    (T : ℝ) (hT : 0 < T) :
    ∫⁻ Γ in matBox a b T, ENNReal.ofReal ((∑ j, lam j * ∑ i, (Γ i j) ^ 2) ^ (-c')) < ⊤ := by
  classical
  have hcard_pos : 0 < a * Fintype.card {j // 0 < lam j} := by
    have h2 : (0 : ℝ) < (a : ℝ) * (Fintype.card {j // 0 < lam j} : ℝ) := by linarith
    rw [← Nat.cast_mul] at h2; exact_mod_cast h2
  have hact : (Finset.univ.filter (fun j => 0 < lam j)).Nonempty := by
    rw [← Finset.card_pos, ← Fintype.card_subtype]
    exact Nat.pos_of_ne_zero (fun h => by rw [h, Nat.mul_zero] at hcard_pos; omega)
  set σ := (Finset.univ.filter (fun j => 0 < lam j)).inf' hact lam with hσdef
  have hσpos : 0 < σ := by
    rw [hσdef, Finset.lt_inf'_iff]; intro j hj; exact (Finset.mem_filter.mp hj).2
  have hmaj : ∀ Γ : Fin a → Fin b → ℝ,
      ENNReal.ofReal ((∑ j, lam j * ∑ i, (Γ i j) ^ 2) ^ (-c'))
        ≤ ENNReal.ofReal (σ ^ (-c'))
          * ENNReal.ofReal ((∑ j ∈ Finset.univ.filter (fun j => 0 < lam j),
              ∑ i, (Γ i j) ^ 2) ^ (-c')) := by
    intro Γ
    rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hσpos.le _)]
    refine ENNReal.ofReal_le_ofReal ?_
    exact weighted_rpow_le lam hlam hact c' hc0 (fun j => ∑ i, (Γ i j) ^ 2)
      (fun j => Finset.sum_nonneg (fun i _ => sq_nonneg _))
  calc ∫⁻ Γ in matBox a b T, ENNReal.ofReal ((∑ j, lam j * ∑ i, (Γ i j) ^ 2) ^ (-c'))
      ≤ ∫⁻ Γ in matBox a b T, ENNReal.ofReal (σ ^ (-c'))
          * ENNReal.ofReal ((∑ j ∈ Finset.univ.filter (fun j => 0 < lam j),
              ∑ i, (Γ i j) ^ 2) ^ (-c')) := lintegral_mono hmaj
    _ = ENNReal.ofReal (σ ^ (-c'))
          * ∫⁻ Γ in matBox a b T, ENNReal.ofReal ((∑ j ∈ Finset.univ.filter (fun j => 0 < lam j),
              ∑ i, (Γ i j) ^ 2) ^ (-c')) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top
        (sumSqActiveCols_matBox_lt_top (fun j => 0 < lam j) hcard_pos c' (by linarith) T hT)

/-! ## Part G — the count `#positive eigenvalues = rank S` (the active dimension) -/

/-- **The number of positive eigenvalues of the Gram `S·Sᵀ` equals `rank S`.** PSD ⟹ eigenvalues `≥ 0`,
so `0 < λ ⟺ λ ≠ 0`; then `Matrix.IsHermitian.rank_eq_card_non_zero_eigs` + `rank_self_mul_transpose`. -/
theorem card_pos_eigenvalues_eq_rank {b q : ℕ} (S : Matrix (Fin b) (Fin q) ℝ) :
    Fintype.card {j // 0 < (posSemidef_mul_transpose S).isHermitian.eigenvalues j} = S.rank := by
  classical
  have hpsd := posSemidef_mul_transpose S
  have hiff : ∀ j, (0 < hpsd.isHermitian.eigenvalues j) ↔ (hpsd.isHermitian.eigenvalues j ≠ 0) :=
    fun j => ⟨fun h => ne_of_gt h,
      fun h => lt_of_le_of_ne (hpsd.eigenvalues_nonneg j) (Ne.symm h)⟩
  calc Fintype.card {j // 0 < hpsd.isHermitian.eigenvalues j}
      = Fintype.card {j // hpsd.isHermitian.eigenvalues j ≠ 0} :=
        Fintype.card_congr (Equiv.subtypeEquivRight hiff)
    _ = (S * Sᵀ).rank := (hpsd.isHermitian.rank_eq_card_non_zero_eigs).symm
    _ = S.rank := Matrix.rank_self_mul_transpose S

/-! ## Part H — the eigenframe change of variables over a bounded box -/

/-- **The `Γ↦Γ·Q` orthogonal CoV lands the box weighted-form integral (abstract `Q`, `lam`).** For an
orthogonal frame `Q` and nonneg weights, the box integral of `(∑_j lam_j ∑_i ((Γ·Q)_{ij})²)^{−c'}` is
finite below `a·#active/2`: enclose `box` in a `Q`-invariant Frobenius ball (`frobSq_vecMul_right`),
push the ball indicator through the banked full-space CoV `lintegral_comp_rightMulₚ` (finite Jacobian),
then `weightedForm_matBox_lt_top`. -/
theorem weightedFormQ_box_lt_top {a b : ℕ} (Q : Matrix (Fin b) (Fin b) ℝ) (hQ : Q * Qᵀ = 1)
    (lam : Fin b → ℝ) (hlam : ∀ j, 0 ≤ lam j) (c' : ℝ) (hc0 : 0 ≤ c')
    (hc' : 2 * c' < (a : ℝ) * (Fintype.card {j // 0 < lam j} : ℝ))
    (box : Set (Fin a → Fin b → ℝ)) (hbox : Bornology.IsBounded box) :
    ∫⁻ Γ in box,
        ENNReal.ofReal ((∑ j, lam j * ∑ i, ((Matrix.of Γ * Q) i j) ^ 2) ^ (-c')) < ⊤ := by
  classical
  have hQdet : Q.det ≠ 0 := by
    intro h
    have hd : (Q * Qᵀ).det = 0 := by rw [Matrix.det_mul, Matrix.det_transpose, h, mul_zero]
    rw [hQ, Matrix.det_one] at hd; exact one_ne_zero hd
  set F' : (Fin a → Fin b → ℝ) → ℝ≥0∞ :=
    fun Y => ENNReal.ofReal ((∑ j, lam j * ∑ i, (Y i j) ^ 2) ^ (-c')) with hF'def
  have hF'meas : Measurable F' := by
    rw [hF'def]
    exact ENNReal.measurable_ofReal.comp ((by fun_prop : Measurable fun t : ℝ => t ^ (-c')).comp
      (by fun_prop))
  -- box ⊆ matBox a b T
  obtain ⟨R, hR⟩ := hbox.subset_closedBall (0 : Fin a → Fin b → ℝ)
  set T : ℝ := max R 1 with hTdef
  have hTpos : 0 < T := lt_of_lt_of_le one_pos (le_max_right R 1)
  have hboxT : box ⊆ matBox a b T := by
    intro Γ hΓ i k
    have hd : ‖Γ‖ ≤ R := by
      have h := Metric.mem_closedBall.mp (hR hΓ); rwa [dist_zero_right] at h
    have h1 : |Γ i k| ≤ T :=
      calc |Γ i k| = ‖Γ i k‖ := (Real.norm_eq_abs _).symm
        _ ≤ ‖Γ i‖ := norm_le_pi_norm (Γ i) k
        _ ≤ ‖Γ‖ := norm_le_pi_norm Γ i
        _ ≤ T := le_trans hd (le_max_left R 1)
    exact Set.mem_Icc.mpr (abs_le.mp h1)
  -- the `Q`-invariant Frobenius ball
  set ρ2 : ℝ := (a * b : ℝ) * T ^ 2 with hρ2
  set Fset : Set (Fin a → Fin b → ℝ) := {Γ | frobSq Γ ≤ ρ2} with hFsetdef
  have hFsetmeas : MeasurableSet Fset := by
    rw [hFsetdef]; exact measurableSet_le (by unfold frobSq; fun_prop) measurable_const
  have hmatFset : matBox a b T ⊆ Fset := by
    intro Γ hΓ
    rw [hFsetdef, Set.mem_setOf_eq, hρ2]
    calc frobSq Γ = ∑ _i : Fin a, ∑ _j : Fin b, (Γ _i _j) ^ 2 := rfl
      _ ≤ ∑ _i : Fin a, ∑ _j : Fin b, T ^ 2 := by
          refine Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => ?_))
          have h := hΓ i j; rw [Set.mem_Icc] at h; nlinarith [h.1, h.2]
      _ = (a * b : ℝ) * T ^ 2 := by
          rw [Finset.sum_const, Finset.sum_const, Finset.card_univ, Finset.card_univ,
            Fintype.card_fin, Fintype.card_fin, nsmul_eq_mul, nsmul_eq_mul]; push_cast; ring
  set R2 : ℝ := Real.sqrt ρ2 + 1 with hR2def
  have hFsetmat : Fset ⊆ matBox a b R2 := by
    intro Γ hΓ i k
    rw [hFsetdef, Set.mem_setOf_eq] at hΓ
    have hsq : (Γ i k) ^ 2 ≤ ρ2 :=
      calc (Γ i k) ^ 2 ≤ ∑ j, (Γ i j) ^ 2 :=
            Finset.single_le_sum (fun j _ => sq_nonneg _) (Finset.mem_univ k)
        _ ≤ frobSq Γ := Finset.single_le_sum
            (fun i _ => Finset.sum_nonneg (fun j _ => sq_nonneg _)) (Finset.mem_univ i)
        _ ≤ ρ2 := hΓ
    have h2 : |Γ i k| ≤ R2 :=
      calc |Γ i k| = Real.sqrt ((Γ i k) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
        _ ≤ Real.sqrt ρ2 := Real.sqrt_le_sqrt hsq
        _ ≤ R2 := by rw [hR2def]; linarith [Real.sqrt_nonneg ρ2]
    exact Set.mem_Icc.mpr (abs_le.mp h2)
  -- `Fset` is `Γ↦Γ·Q`-invariant, so the full-space CoV applies to the ball integral
  have hinv : ∀ Γ : Fin a → Fin b → ℝ, (Γ ∈ Fset) ↔ ((fun i => Γ i ᵥ* Q) ∈ Fset) := by
    intro Γ; rw [hFsetdef]; simp only [Set.mem_setOf_eq, frobSq_vecMul_right Q hQ Γ]
  have hcov : (∫⁻ Γ in Fset,
        ENNReal.ofReal ((∑ j, lam j * ∑ i, ((Matrix.of Γ * Q) i j) ^ 2) ^ (-c')))
      = ENNReal.ofReal (|Q.det| ^ a)⁻¹ * ∫⁻ Γ in Fset, F' Γ := by
    have e1 : (∫⁻ Γ in Fset,
          ENNReal.ofReal ((∑ j, lam j * ∑ i, ((Matrix.of Γ * Q) i j) ^ 2) ^ (-c')))
        = ∫⁻ Γ : Fin a → Fin b → ℝ, (Fset.indicator F') (fun i => Γ i ᵥ* Q) := by
      rw [← lintegral_indicator hFsetmeas]
      refine lintegral_congr (fun Γ => ?_)
      by_cases hΓ : Γ ∈ Fset
      · rw [Set.indicator_of_mem hΓ, Set.indicator_of_mem ((hinv Γ).mp hΓ)]; rfl
      · rw [Set.indicator_of_notMem hΓ, Set.indicator_of_notMem (fun h => hΓ ((hinv Γ).mpr h))]
    rw [e1, lintegral_comp_rightMulₚ a Q hQdet (Fset.indicator F') (hF'meas.indicator hFsetmeas),
      lintegral_indicator hFsetmeas]
  calc ∫⁻ Γ in box, ENNReal.ofReal ((∑ j, lam j * ∑ i, ((Matrix.of Γ * Q) i j) ^ 2) ^ (-c'))
      ≤ ∫⁻ Γ in matBox a b T,
          ENNReal.ofReal ((∑ j, lam j * ∑ i, ((Matrix.of Γ * Q) i j) ^ 2) ^ (-c')) :=
        lintegral_mono_set hboxT
    _ ≤ ∫⁻ Γ in Fset,
          ENNReal.ofReal ((∑ j, lam j * ∑ i, ((Matrix.of Γ * Q) i j) ^ 2) ^ (-c')) :=
        lintegral_mono_set hmatFset
    _ = ENNReal.ofReal (|Q.det| ^ a)⁻¹ * ∫⁻ Γ in Fset, F' Γ := hcov
    _ ≤ ENNReal.ofReal (|Q.det| ^ a)⁻¹ * ∫⁻ Γ in matBox a b R2, F' Γ :=
        mul_le_mul_left' (lintegral_mono_set hFsetmat) _
    _ < ⊤ := by
        refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_
        rw [hF'def]
        exact weightedForm_matBox_lt_top lam hlam c' hc0 hc' R2
          (by rw [hR2def]; positivity)

/-! ## The §H hole #1 — the fixed-`S` corank SVD family finiteness -/

/-- **The fixed-`S` corank SVD family is finite below threshold (§H hole #1).** For a fixed `b×q` matrix
`S` of rank `r`, `min(a,b) ≥ 2`, and `2c' < a·r`, the integral over any bounded `box` of
`(frobSq(Γ·S))^{−c'}` is finite. Morse singularity: `frobSq(Γ·S)` is a rank-`a·r` PSD form in `Γ`;
spectral rewrite (`frobSq_mul_eq_sum_eigenvalues`) + the unit-Jacobian eigenframe CoV + the active/free
split close it below the tight threshold `2c' < a·rank(S)`. -/
theorem corankSVD_chartFamily_lt_top {a b q : ℕ} (hab : 2 ≤ min a b)
    (S : Matrix (Fin b) (Fin q) ℝ) (c' : NNReal)
    (hthr : 2 * (c' : ℝ) < (a : ℝ) * (S.rank : ℝ))
    (box : Set (Fin a → Fin b → ℝ)) (hbox : Bornology.IsBounded box) :
    ∫⁻ Γ in box, ENNReal.ofReal ((frobSq (Matrix.of Γ * S)) ^ (-(c' : ℝ))) < ⊤ := by
  -- spectral rewrite of the integrand: `frobSq(Γ·S) = ∑_j λ_j ∑_i ((Γ·Q)_{ij})²`
  have hrw : ∀ Γ : Fin a → Fin b → ℝ,
      ENNReal.ofReal ((frobSq (Matrix.of Γ * S)) ^ (-(c' : ℝ)))
        = ENNReal.ofReal ((∑ j, (posSemidef_mul_transpose S).isHermitian.eigenvalues j
            * ∑ i, ((Matrix.of Γ * ((posSemidef_mul_transpose S).isHermitian.eigenvectorUnitary :
                Matrix (Fin b) (Fin b) ℝ)) i j) ^ 2) ^ (-(c' : ℝ))) := by
    intro Γ; rw [frobSq_mul_eq_sum_eigenvalues (Matrix.of Γ) S]
  rw [lintegral_congr_ae (Filter.Eventually.of_forall hrw)]
  -- the eigenframe `Q` is orthogonal
  have hQ : ((posSemidef_mul_transpose S).isHermitian.eigenvectorUnitary : Matrix (Fin b) (Fin b) ℝ)
        * ((posSemidef_mul_transpose S).isHermitian.eigenvectorUnitary :
            Matrix (Fin b) (Fin b) ℝ)ᵀ = 1 := by
    have h := Matrix.mem_unitaryGroup_iff.mp
      (posSemidef_mul_transpose S).isHermitian.eigenvectorUnitary.property
    rwa [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] at h
  refine weightedFormQ_box_lt_top _ hQ _
    (fun j => (posSemidef_mul_transpose S).eigenvalues_nonneg j)
    (c' : ℝ) (NNReal.coe_nonneg c') ?_ box hbox
  rw [card_pos_eigenvalues_eq_rank S]; exact hthr

end DLNFibre.DLN.RLCT
