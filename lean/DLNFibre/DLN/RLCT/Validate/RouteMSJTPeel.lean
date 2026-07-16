import DLNFibre.DLN.RLCT.Validate.RouteMSJShellSubset
import DLNFibre.DLN.RLCT.Validate.RouteMSJResolution
import DLNFibre.DLN.RLCT.Validate.RouteMSJCorankSurvival

set_option linter.style.longLine false

/-!
# `RouteMSJTPeel` — G1, the T-peel: the box → ∑-shell decomposition (arity ≥ 4)

**Thread `genm-tpeel` (aoyagi-full Stage 2), the first step of the arity≥4 (3a) discharge of (□).**
The full-chain layer-product box loss integral `routeMLayerBoxIntegral M c' 1` is bounded by the finite
sum, over singular-value shells `j ≤ r = min(M₀−t, M₁−t)` and pivot charts `(ρ, κ)` at the DEEPER cut
`u = t+j`, of the shell-`j`-restricted, cut-`u` spine integrand `shellSpineIntegrand M (t+j) κ ε r j c'`:

    routeMLayerBoxIntegral M c' 1
      ≤ ∑_{j : Fin (r+1)} ∑_{ρ : Fin (t+j) ↪ Fin M₀} ∑_{κ : Fin (t+j) ↪ Fin M₁}
          shellSpineIntegrand M (t+j) κ ε r j c'.

This is the connective G1 that feeds the landed LINK `shellSpine_le_frontCharge_binding` (per (j,κ):
shellSpine ≤ ∫ front-charge) and G2 (∫ front-charge < ⊤), giving `box < ⊤` = (□) for arity ≥ 4.

## The decomposition (measure-theoretic, no genuinely-new math)

The direction `box ≤ ∑ shellSpine` is the RIGHT way even though the banked `shellSpine_inner_le_matBox`
runs the other way (a SINGLE chart ≤ box, its last step drops the pivot chart). The right fact is the
EQUALITY inside that proof (`chartInner_blockReindex_eq_of_emb` + `chartInner_schurShearFree_eq` +
`frobSq_schur_split_inv`): the freed inner integral at pivot `κ` EQUALS the box inner integral RESTRICTED
to the chart `matBox ∩ pivotChart ρ κ` (ρ-free). Then:

1. **front-split** (`routeMLayerBoxIntegral_front_split`): reduce the box to the tail-outer / front-inner
   iterated integral `∫_{A'∈box(tail)} ∫_{A₀∈matBox} frobSq(rmatMul A₀ (prod(tailChain M) A'))^{−c'}`.
2. **outer shell cover** of the tail parameter `A'` by the singular-value shells of `prod(tailChain M) A'`
   (`lintegral_le_sum_finCover` over the exhaustive `singularShell_iUnion`).
3. **inner pivot cover** (per `A'`, cut `u = t+j`): the low-rank front factors `{rank A₀ < u}` are a
   determinantal null set (`u ≤ min(M₀,M₁)` from `ht` + `j ≤ r`), so the front-factor box is co-null
   covered by the cut-`u` pivot charts (`pivotChartCover_matBox_le_sum` + the co-null fact), and each
   chart integral equals the freed inner (the EQUALITY above), reassembling to the per-shell
   `shellSpineIntegrand` after pulling the finite `(ρ,κ)`-sum out of the `A'`-integral.

S2-FREE: banked measure/matrix plumbing (front-split, pivot-chart cover, shear-freed equality) + the
reused determinantal a.e.-nonzero engine (`ae_matrix_eval_ne_zero`). Native, sorry-free target.
-/

namespace DLNFibre.DLN.RLCT

open Matrix MeasureTheory MvPolynomial
open scoped ENNReal BigOperators

variable {L : ℕ}

/-- **The rank-drop locus is null (determinantal co-null).** For `1 ≤ u ≤ min(p,q)`, a.e. matrix
`A : Matrix (Fin p) (Fin q) ℝ` has `u ≤ A.rank` — the low-rank set `{rank A < u}` is the zero set of
one fixed `u×u` minor (a nonzero polynomial, witnessed by the identity-like matrix), hence Lebesgue-null.
Reuses the banked a.e.-nonzero-polynomial engine `ae_matrix_eval_ne_zero`; parallels
`corank_survival_ae` (simpler — no deep factor). -/
theorem ae_rank_ge {p q u : ℕ} (hu : 1 ≤ u) (hup : u ≤ p) (huq : u ≤ q) :
    ∀ᵐ A : Matrix (Fin p) (Fin q) ℝ, u ≤ A.rank := by
  classical
  obtain ⟨r, rfl⟩ : ∃ r, u = r + 1 := ⟨u - 1, by omega⟩
  set er : Fin (r + 1) → Fin p := Fin.castLE hup with her
  set ec : Fin (r + 1) → Fin q := Fin.castLE huq with hec
  set Agen : Matrix (Fin p) (Fin q) (MvPolynomial (Fin p × Fin q) ℝ) :=
    Matrix.of (fun i j ↦ X (i, j)) with hAgen
  set P : MvPolynomial (Fin p × Fin q) ℝ := (Agen.submatrix er ec).det with hP
  -- encoding: `eval (A ·.1 ·.2) P = det ((Matrix.of A).submatrix er ec)`
  have hencode : ∀ A : Fin p → Fin q → ℝ,
      MvPolynomial.eval (fun ij : Fin p × Fin q ↦ A ij.1 ij.2) P
        = ((Matrix.of A).submatrix er ec).det := by
    intro A
    set pt : Fin p × Fin q → ℝ := fun ij ↦ A ij.1 ij.2 with hpt
    have hmap : (Agen.submatrix er ec).map (⇑(MvPolynomial.eval pt))
        = (Matrix.of A).submatrix er ec := by
      ext i k
      simp only [Matrix.map_apply, Matrix.submatrix_apply, hAgen, Matrix.of_apply,
        MvPolynomial.eval_X, hpt]
    rw [hP, RingHom.map_det]
    exact congrArg Matrix.det hmap
  -- `P ≠ 0`: the identity-like matrix `W₀` has `W₀.submatrix er ec = 1`, det `= 1 ≠ 0`
  have hPne : P ≠ 0 := by
    intro hzero
    set W₀ : Fin p → Fin q → ℝ := fun a b ↦ if (a : ℕ) = (b : ℕ) then 1 else 0 with hW₀
    have hev := hencode W₀
    rw [hzero, map_zero] at hev
    have hsub : (Matrix.of W₀).submatrix er ec = (1 : Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ) := by
      ext i k
      rw [Matrix.submatrix_apply, Matrix.of_apply, hW₀, her, hec]
      simp only [Fin.coe_castLE, Matrix.one_apply]
      by_cases h : i = k
      · subst h; simp
      · rw [if_neg (by rw [Fin.val_inj]; exact h), if_neg h]
    rw [hsub, Matrix.det_one] at hev
    exact one_ne_zero hev.symm
  filter_upwards [ae_matrix_eval_ne_zero P hPne] with A hA
  have hA' : ((Matrix.of A).submatrix er ec).det ≠ 0 := by rw [← hencode]; exact hA
  by_contra hlt
  rw [not_le] at hlt
  exact hA' (Core.submatrix_det_eq_zero_of_rank_le (A := A) (Nat.lt_succ_iff.mp hlt) er ec)

/-- **The per-`A'` chart integral equals the freed inner (general pivot `(ρ, κ)`).** For any pivot cut
`(ρ, κ)` at level `u`, the box inner integral of the front factor `A₀` RESTRICTED to the chart
`matBox ∩ pivotChart ρ κ` equals the freed-`Γ` inner double integral at pivot `κ` — the inner of
`shellSpineIntegrand`. ρ-free (the shear absorbs the pivot rows into the outer domain). Replicates the
`key` equality inside the banked `shellSpine_inner_le_matBox`, generalized off `castLEEmb` to arbitrary
`ρ` (`chartInner_blockReindex_eq_of_emb` is ρ-generic). -/
theorem chartBox_eq_freedInner (M : Fin (L + 1 + 1 + 1) → ℕ) (u : ℕ)
    (ρ : Fin u ↪ Fin (M 0)) (κ : Fin u ↪ Fin (M 1)) (c' : ℝ) (A' : Params (tailChain M)) :
    (∫⁻ A₀ in matBox (M 0) (M 1) 1 ∩ pivotChart ρ κ,
        ENNReal.ofReal ((frobSq (rmatMul A₀ (prod (tailChain M) A'))) ^ (-c')))
      = ∫⁻ x in outerDom u (M 0 - u) (M 1 - u) 1,
          ∫⁻ Γ in {Γ : Fin (M 0 - u) → Fin (M 1 - u) → ℝ |
              Γ + schurShift x ∈ genBox (Fin (M 0 - u)) (Fin (M 1 - u)) 1},
            ENNReal.ofReal ((freedSchurLoss x Γ
              ((prod (tailChain M) A').submatrix (blockSplitEquiv κ) id)) ^ (-c')) := by
  symm
  rw [chartInner_blockReindex_eq_of_emb ρ κ (prod (tailChain M) A') c' 1,
    ← chartInner_schurShearFree_eq ((prod (tailChain M) A').submatrix (blockSplitEquiv κ) id) c' 1]
  refine setLIntegral_congr_fun
    ((measurableSet_genBox 1).inter measurableSet_isUnit_toBlocks₁₁) (fun B hB => ?_)
  exact congrArg (fun s : ℝ => ENNReal.ofReal (s ^ (-c')))
    (frobSq_schur_split_inv (Matrix.of B) hB.2
      ((prod (tailChain M) A').submatrix (blockSplitEquiv κ) id)).symm

/-- **The general-`u` product-level pivot-chart cover.** For the front factor `A₀ : Matrix (Fin m) (Fin n) ℝ`
(with `1 ≤ u ≤ min(m,n)`) times a tail set `s ⊆ β`, the `matBox ×ˢ s` product integral is bounded by the
finite sum, over the cut-`u` pivot charts `(ρ, κ)`, of the `(matBox ∩ pivotChart ρ κ) ×ˢ s` integrals. The
general-`u` analog of the banked `frontBox_pivotCover_le` (`u = 1`): the low-rank locus `{rank A₀ < u}` is
a determinantal null set (`ae_rank_ge`), so `matBox ×ˢ s =ᵐ (matBox ∩ {u ≤ rank}) ×ˢ s`; then
`{u ≤ rank} = ⋃_{ρ,κ} pivotChart ρ κ` (`pivotLocus_eq_iUnion u`), distributed over `×ˢ s` and bounded by
subadditivity. Measurability-free. -/
theorem frontBox_pivotCover_le_gen {m n u : ℕ} (hu : 1 ≤ u) (hum : u ≤ m) (hun : u ≤ n)
    {β : Type*} [MeasureSpace β] [SigmaFinite (volume : Measure β)]
    (T : ℝ) (s : Set β) (f : (Fin m → Fin n → ℝ) × β → ℝ≥0∞) :
    ∫⁻ q in matBox m n T ×ˢ s, f q
      ≤ ∑ ρ : Fin u ↪ Fin m, ∑ κ : Fin u ↪ Fin n,
          ∫⁻ q in (matBox m n T ∩ pivotChart ρ κ) ×ˢ s, f q := by
  classical
  -- the low-rank locus is null (determinantal co-null)
  have hnull0 : (volume : Measure (Matrix (Fin m) (Fin n) ℝ)) {A | A.rank < u} = 0 := by
    have h := ae_rank_ge (p := m) (q := n) hu hum hun
    rw [ae_iff] at h
    convert h using 2
    ext A
    simp only [Set.mem_setOf_eq, not_le]
  -- (i) `matBox ×ˢ s =ᵐ (matBox ∩ {u ≤ rank}) ×ˢ s` (the deficient product is null)
  have hae : (matBox m n T ×ˢ s)
      =ᵐ[volume] ((matBox m n T ∩ {A : Matrix (Fin m) (Fin n) ℝ | u ≤ A.rank}) ×ˢ s) := by
    rw [ae_eq_set]
    refine ⟨?_, ?_⟩
    · have hsub : (matBox m n T ×ˢ s)
          \ ((matBox m n T ∩ {A : Matrix (Fin m) (Fin n) ℝ | u ≤ A.rank}) ×ˢ s)
          ⊆ ({A : Matrix (Fin m) (Fin n) ℝ | A.rank < u} : Set _) ×ˢ s := by
        rintro ⟨A0, b⟩ hq
        rw [Set.mem_diff] at hq
        obtain ⟨hin, hnot⟩ := hq
        rw [Set.mem_prod] at hin
        obtain ⟨hA0, hb⟩ := hin
        refine ⟨?_, hb⟩
        show Matrix.rank A0 < u
        by_contra hge
        exact hnot ⟨Set.mem_inter hA0 (not_lt.mp hge), hb⟩
      have hnull : volume (({A : Matrix (Fin m) (Fin n) ℝ | A.rank < u} : Set _) ×ˢ s) = 0 := by
        rw [Measure.volume_eq_prod, Measure.prod_prod, hnull0, zero_mul]
      exact measure_mono_null hsub hnull
    · rw [Set.diff_eq_empty.mpr (Set.prod_mono Set.inter_subset_left (subset_refl s))]
      exact measure_empty
  -- (ii) cover `{u ≤ rank}` by the cut-`u` pivot charts, distributed over `×ˢ s`
  have hcov : {A : Matrix (Fin m) (Fin n) ℝ | u ≤ A.rank}
      = ⋃ (ρ : Fin u ↪ Fin m) (κ : Fin u ↪ Fin n), pivotChart ρ κ := pivotLocus_eq_iUnion u
  have hdist : (⋃ (ρ : Fin u ↪ Fin m) (κ : Fin u ↪ Fin n), matBox m n T ∩ pivotChart ρ κ)
      = matBox m n T ∩ ⋃ (ρ : Fin u ↪ Fin m) (κ : Fin u ↪ Fin n), pivotChart ρ κ := by
    simp only [Set.inter_iUnion]
  have hset : matBox m n T ∩ {A : Matrix (Fin m) (Fin n) ℝ | u ≤ A.rank}
      = ⋃ (ρ : Fin u ↪ Fin m) (κ : Fin u ↪ Fin n), matBox m n T ∩ pivotChart ρ κ :=
    (congrArg (fun st => matBox m n T ∩ st) hcov).trans hdist.symm
  have hcover : (matBox m n T ∩ {A : Matrix (Fin m) (Fin n) ℝ | u ≤ A.rank}) ×ˢ s
      = ⋃ (ρ : Fin u ↪ Fin m) (κ : Fin u ↪ Fin n), (matBox m n T ∩ pivotChart ρ κ) ×ˢ s := by
    rw [hset]; simp only [Set.iUnion_prod_const]
  rw [setLIntegral_congr hae, hcover]
  calc ∫⁻ q in ⋃ (ρ : Fin u ↪ Fin m) (κ : Fin u ↪ Fin n), (matBox m n T ∩ pivotChart ρ κ) ×ˢ s, f q
      ≤ ∑' ρ : Fin u ↪ Fin m,
          ∫⁻ q in ⋃ κ : Fin u ↪ Fin n, (matBox m n T ∩ pivotChart ρ κ) ×ˢ s, f q :=
        lintegral_iUnion_le _ _
    _ = ∑ ρ : Fin u ↪ Fin m,
          ∫⁻ q in ⋃ κ : Fin u ↪ Fin n, (matBox m n T ∩ pivotChart ρ κ) ×ˢ s, f q := tsum_fintype _
    _ ≤ ∑ ρ : Fin u ↪ Fin m, ∑' κ : Fin u ↪ Fin n,
          ∫⁻ q in (matBox m n T ∩ pivotChart ρ κ) ×ˢ s, f q :=
        Finset.sum_le_sum (fun ρ _ => lintegral_iUnion_le _ _)
    _ = ∑ ρ : Fin u ↪ Fin m, ∑ κ : Fin u ↪ Fin n,
          ∫⁻ q in (matBox m n T ∩ pivotChart ρ κ) ×ˢ s, f q :=
        Finset.sum_congr rfl (fun ρ _ => tsum_fintype _)

/-- **G1 — the T-peel: box ≤ ∑-shell/∑-pivot spine.** For any base cut `t ≤ min(M₀,M₁)`, threshold `ε`,
and exponent `c'`, the full-chain layer-product box loss integral is bounded by the finite sum, over
singular-value shells `j ≤ r = min(M₀−t, M₁−t)` and pivot charts `(ρ, κ)` at the deeper cut `u = t+j`,
of the shell-`j`-restricted cut-`u` spine integrand. The connective G1 feeding the landed LINK
`shellSpine_le_frontCharge_binding` + G2. -/
theorem routeMLayerBox_le_sum_shellSpine (M : Fin (L + 1 + 1 + 1) → ℕ) (t : ℕ)
    (ε c' : ℝ) (ht : t ≤ min (M 0) (M 1)) (ht1 : 1 ≤ t) :
    routeMLayerBoxIntegral M c' 1
      ≤ ∑ j : Fin (min (M 0 - t) (M 1 - t) + 1),
          ∑ ρ : Fin (t + (j : ℕ)) ↪ Fin (M 0), ∑ κ : Fin (t + (j : ℕ)) ↪ Fin (M 1),
            shellSpineIntegrand M (t + (j : ℕ)) κ ε (min (M 0 - t) (M 1 - t)) j c' := by
  classical
  set r : ℕ := min (M 0 - t) (M 1 - t) with hrdef
  have htM0 : t ≤ M 0 := le_trans ht (min_le_left _ _)
  have htM1 : t ≤ M 1 := le_trans ht (min_le_right _ _)
  have hrM0 : r ≤ M 0 - t := hrdef ▸ min_le_left _ _
  have hrM1 : r ≤ M 1 - t := hrdef ▸ min_le_right _ _
  -- Step 1: front-split the box into the tail-outer / front-inner iterated integral.
  rw [routeMLayerBoxIntegral_front_split M c']
  -- Step 2: cover the tail parameter `A'` by the singular-value shells of `prod (tailChain M) A'`.
  refine le_trans (lintegral_le_sum_finCover
    (fun j : Fin (r + 1) => paramsBoxM (tailChain M) 1
      ∩ {A' | prod (tailChain M) A' ∈ singularShell ε r j})
    (fun A' => ∫⁻ A0 in matBox (M 0) (M 1) 1,
      ENNReal.ofReal ((frobSq (rmatMul A0 (prod (tailChain M) A'))) ^ (-c')))
    ?hcov) ?_
  case hcov =>
    intro A' hA'
    have hmem : prod (tailChain M) A' ∈ ⋃ j : Fin (r + 1), singularShell ε r j := by
      rw [singularShell_iUnion]; exact Set.mem_univ _
    rw [Set.mem_iUnion] at hmem
    obtain ⟨j, hj⟩ := hmem
    exact Set.mem_iUnion.mpr ⟨j, hA', hj⟩
  -- Step 3+4: per shell `j`, bound the box piece by the pivot-chart sum, each = `shellSpineIntegrand`.
  refine Finset.sum_le_sum (fun j _ => ?_)
  have hjr : (j : ℕ) ≤ r := Nat.lt_succ_iff.mp j.2
  set Sj : Set (Params (tailChain M)) :=
    paramsBoxM (tailChain M) 1 ∩ {A' | prod (tailChain M) A' ∈ singularShell ε r j} with hSj
  calc (∫⁻ A' in Sj, ∫⁻ A0 in matBox (M 0) (M 1) 1,
            ENNReal.ofReal ((frobSq (rmatMul A0 (prod (tailChain M) A'))) ^ (-c')))
      = ∫⁻ q in matBox (M 0) (M 1) 1 ×ˢ Sj,
          ENNReal.ofReal ((frobSq (rmatMul q.1 (prod (tailChain M) q.2))) ^ (-c')) := by
        rw [Measure.volume_eq_prod,
          setLIntegral_prod_symm _ (measurable_frontIntegrand M c').aemeasurable]
    _ ≤ ∑ ρ : Fin (t + (j : ℕ)) ↪ Fin (M 0), ∑ κ : Fin (t + (j : ℕ)) ↪ Fin (M 1),
          ∫⁻ q in (matBox (M 0) (M 1) 1 ∩ pivotChart ρ κ) ×ˢ Sj,
            ENNReal.ofReal ((frobSq (rmatMul q.1 (prod (tailChain M) q.2))) ^ (-c')) :=
        frontBox_pivotCover_le_gen (u := t + (j : ℕ)) (by omega) (by omega) (by omega) 1 Sj _
    _ = ∑ ρ : Fin (t + (j : ℕ)) ↪ Fin (M 0), ∑ κ : Fin (t + (j : ℕ)) ↪ Fin (M 1),
          shellSpineIntegrand M (t + (j : ℕ)) κ ε r j c' := by
        refine Finset.sum_congr rfl (fun ρ _ => Finset.sum_congr rfl (fun κ _ => ?_))
        rw [Measure.volume_eq_prod,
          setLIntegral_prod_symm _ (measurable_frontIntegrand M c').aemeasurable,
          shellSpineIntegrand]
        exact lintegral_congr (fun A' => chartBox_eq_freedInner M (t + (j : ℕ)) ρ κ c' A')

end DLNFibre.DLN.RLCT
