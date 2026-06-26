import DLNFibre.DLN.RLCT.Skeleton
import DLNFibre.DLN.RLCT.Validate.Case111Bridge

/-!
# `DLNFibre.DLN.RLCT.Validate.Case111` — smallest case end-to-end (validate-small-first GATE)

The first real end-to-end Lean result, for the trivial network `H = (1,1,1)`, `r = 0`, `B = 0`. Here
`dlnLoss (1,1,1) 0 A = (c₁·c₂)²` (the two layers are `1×1`, i.e. scalars `c₁ = A 0 0 0`,
`c₂ = A 1 0 0`) is **already** normal-crossing — no blow-up, no resolution, no `S1`/`L1`/`L2`/`D1`.
The loss is the weighted monomial `(∏|uⱼ|^{2·1})^{−c}` with density `∏|uⱼ|^0 = 1`, i.e. the monomial
data `k = (1,1)`, `h = (0,0)`, `d = 2`.

This is the anti-treadmill checkpoint, now **fully closed and axiom-free**: a sorry-free assembly
that threads the monomial model the resolution feeds (`monomialThreshold`) and lands on the closed
form `aoyagiLambda (1,1,1) 0`, with `#print axioms case111_rlct = [propext, Classical.choice,
Quot.sound]` — no `sorryAx`, no `monomial_rlct`, no `native_decide`. Both sides are `1/2`:

* the monomial threshold `min_j (0+1)/(2·1) = 1/2` (proven directly from Mathlib in `Case111Bridge`,
  `monomialThreshold_case111`), and
* `aoyagiLambda (1,1,1) 0 = [−0²+0·(1+1)]/2 + ½·(Adm).inf' Mval = 0 + ½·1 = 1/2`.

## What is proven sorry-free
* `dlnLoss_case111` — the **monomial-form coercion** of the loss (pure polynomial algebra).
* `case111_monomialThreshold` — `monomialThreshold 2 (1,1) (0,0) = ofReal (aoyagiLambda (1,1,1) 0)`,
  axiom-free (the threshold value is `monomialThreshold_case111`, Fubini + the Mathlib rpow
  integrability iff in `Case111Bridge`).
* `case111_rlct_eq_monomialThreshold` — the **baby-S1.1 bridge**, now proven (see below).

## The `rlctAt`-headline (proven)
`rlctAt (dlnLoss (1,1,1) 0) deepest111 = ofReal (aoyagiLambda (1,1,1) 0)` (`deepest111 = fun _ ↦ 0`,
the deepest fibre point). The bridge `rlctAt H (dlnLoss …) wstar = monomialThreshold …` — `rlctAt`
integrates `|F|^{−c}` over a `Params`-neighbourhood of `wstar`, the box machinery over `[0,1]^d` —
is closed here directly, *not* via the general S1 lemmas: the loss `|F|^{−c'} = |c₁·c₂|^{−2c'}`
depends only on the *product* of the two scalar entries, which the flattening `paramsEquivFlat`
preserves (`prod_paramsEquivFlat`, re-index-invariant), so it transports along the
measure-preserving homeomorphism `entryME : Params (1,1,1) ≃ᵐ ℝ²` to `|x·y|^{−2c'}` on `ℝ²`. The
admissible-exponent set
is then the coerced `{c' < 1/2}` by the two-sided 2-D box iff (`prodBoxSymm_rpow_integrableOn_iff`):
forward exhibits the open box `entryME⁻¹((-1,1)²)`; reverse pushes any neighbourhood of `0` forward
(homeomorphism) to a box `[-ε,ε]²` where divergence forces `c' < 1/2`. Its `sSup` is `1/2`. The
headline `case111_rlct` is `case111_rlct_eq_monomialThreshold ▸ case111_monomialThreshold`.
-/

namespace DLNFibre.DLN.RLCT

open Matrix MeasureTheory Set Filter
open scoped ENNReal Topology BigOperators

/-- The deepest singular point of the `(1,1,1)`, `B = 0` fibre: both scalar layers `0`. (`Params` is
a `def`, so the Pi `Zero` is not synthesised under the bare `0` numeral; the witness is shown.) -/
def deepest111 : Params (![1, 1, 1] : Fin 3 → ℕ) := fun _ => 0

/-- The product over the two-element flat index `FlatIdx (1,1,1)` of a parameter's entries is the
product of its two scalar layer entries `A 0 0 0 · A 1 0 0` (two nested `Fintype.prod_sigma`, then
the `Fin 1`-width per-layer products collapse). -/
theorem prod_entries_case111 (A : Params (![1, 1, 1] : Fin 3 → ℕ)) :
    (∏ q : FlatIdx (![1, 1, 1] : Fin 3 → ℕ), A q.1.1 q.1.2 q.2)
      = A 0 (0 : Fin 1) (0 : Fin 1) * A 1 (0 : Fin 1) (0 : Fin 1) := by
  rw [show (∏ q : FlatIdx (![1, 1, 1] : Fin 3 → ℕ), A q.1.1 q.1.2 q.2)
        = ∏ q : FlatRowIdx (![1, 1, 1] : Fin 3 → ℕ), ∏ j, A q.1 q.2 j from Fintype.prod_sigma _,
      show (∏ q : FlatRowIdx (![1, 1, 1] : Fin 3 → ℕ), ∏ j, A q.1 q.2 j)
        = ∏ s : Fin 2, ∏ i, ∏ j, A s i j from Fintype.prod_sigma _,
      Fin.prod_univ_two,
      show (∏ i, ∏ j, A (0 : Fin 2) i j) = ∏ i : Fin 1, ∏ j : Fin 1, A (0 : Fin 2) i j from rfl,
      show (∏ i, ∏ j, A (1 : Fin 2) i j) = ∏ i : Fin 1, ∏ j : Fin 1, A (1 : Fin 2) i j from rfl,
      Fin.prod_univ_one, Fin.prod_univ_one, Fin.prod_univ_one, Fin.prod_univ_one]

/-! ## The monomial-form coercion of the loss -/

/-- For `H = (1,1,1)`, `B = 0`: the loss is the bare monomial `(c₁·c₂)²` in the two scalar entries
`c₁ = A 0 0 0`, `c₂ = A 1 0 0` (the `1×1` layers). Pure polynomial algebra — no citation. This is
the form the weighted-monomial citation consumes (`k = (1,1)`, `h = (0,0)`). -/
theorem dlnLoss_case111 (A : Params (![1, 1, 1] : Fin 3 → ℕ)) :
    dlnLoss (![1, 1, 1] : Fin 3 → ℕ) 0 A
      = (A 0 (0 : Fin 1) (0 : Fin 1) * A 1 (0 : Fin 1) (0 : Fin 1)) ^ 2 := by
  -- `simp` reduces the layer product `prodAux` (clearing its recursive casts) to `1 * A 0 * A 1`;
  -- `erw` finishes the single-entry read, rewriting up to the defeq `Fin (H s) = Fin 1` widths.
  simp only [dlnLoss, prod]
  simp [prodAux]
  congr 1
  erw [Matrix.sub_apply, Matrix.zero_apply, sub_zero, Matrix.mul_apply, Fin.sum_univ_one,
    Matrix.mul_apply, Fin.sum_univ_one, Matrix.one_apply_eq, one_mul]

/-! ## The monomial-threshold end-to-end (sorry-free, axiom-free) -/

/-- The per-axis ratios for the `(1,1,1)` monomial data `k = (1,1)`, `h = (0,0)` all equal `1/2`, so
their infimum — the S2 threshold — is `1/2`. -/
theorem case111_axisRatio_inf :
    (⨅ j : Fin 2, axisRatio ((![0, 0] : Fin 2 → ℕ) j) ((![1, 1] : Fin 2 → ℕ) j))
      = (1 / 2 : ℝ≥0∞) := by
  have h : ∀ j : Fin 2,
      axisRatio ((![0, 0] : Fin 2 → ℕ) j) ((![1, 1] : Fin 2 → ℕ) j) = (1 / 2 : ℝ≥0∞) :=
    fun j => by fin_cases j <;> simp [axisRatio]
  simp [h]

/-- The closed form for the trivial network: `aoyagiLambda (1,1,1) 0 = 1/2` (regular shift `0`, core
`½·1`). Evaluated by kernel reduction. -/
theorem aoyagiLambda_case111 : aoyagiLambda (![1, 1, 1] : Fin 3 → ℕ) 0 = (1 / 2 : ℚ) := by
  decide +kernel

/-- `ENNReal.ofReal (aoyagiLambda (1,1,1) 0) = 1/2`. -/
theorem ofReal_aoyagiLambda_case111 :
    ENNReal.ofReal (aoyagiLambda (![1, 1, 1] : Fin 3 → ℕ) 0) = (1 / 2 : ℝ≥0∞) := by
  rw [aoyagiLambda_case111, show ((1 / 2 : ℚ) : ℝ) = (1 / 2 : ℝ) by norm_num,
    ENNReal.ofReal_div_of_pos (by norm_num)]
  simp

/-- **The gate (sorry-free, AXIOM-FREE).** The monomial-model threshold the resolution feeds for the
trivial network equals the closed form: both are `1/2`. Now proven **without `monomial_rlct`** — the
threshold value comes from `monomialThreshold_case111` (Fubini + the Mathlib rpow integrability iff,
`Case111Bridge`), so `#print axioms` shows only standard axioms. The end-to-end assembly: monomial
data `(k,h) = ((1,1),(0,0))` ▸ `monomialThreshold = 1/2` (Mathlib) ▸ `aoyagiLambda = 1/2`. -/
theorem case111_monomialThreshold :
    monomialThreshold 2 (![1, 1] : Fin 2 → ℕ) (![0, 0] : Fin 2 → ℕ)
      = ENNReal.ofReal (aoyagiLambda (![1, 1, 1] : Fin 3 → ℕ) 0) := by
  rw [monomialThreshold_case111, ofReal_aoyagiLambda_case111]

/-! ## The `rlctAt`-headline (bridge proven; sorry-free, axiom-free) -/

/-- The deepest point `deepest111` lies in `optimalSet` (`prod 0 = 0`, so the loss vanishes). -/
theorem deepest111_mem_optimalSet :
    deepest111 ∈ optimalSet (![1, 1, 1] : Fin 3 → ℕ) 0 := by
  have hz : dlnLoss (![1, 1, 1] : Fin 3 → ℕ) 0 deepest111 = 0 := by
    rw [dlnLoss_case111]; change ((0 : ℝ) * 0) ^ 2 = 0; ring
  rw [optimalSet_eq_loss_zero]; exact hz

/-! ### The baby-S1.1 transport (the bridge, now proven)

The local RLCT of the `(1,1,1)` loss at the deepest point is computed directly via the
measure-preserving homeomorphism `entryME : Params (1,1,1) ≃ᵐ ℝ²` (`paramsEquivFlat ≫ finTwoArrow`,
`Case111Bridge`). The integrand `|dlnLoss A|^{−c'} = |c₁·c₂|^{−2c'}` depends only on the *product*
of the two scalar entries `c₁ = A 0 0 0`, `c₂ = A 1 0 0`, which `paramsEquivFlat` preserves
(`prod_paramsEquivFlat` — re-index-invariant), so it transports to `|x·y|^{−2c'}` on `ℝ²` regardless
of the opaque flat re-index. The admissible-exponent set is then `{c' : NNReal | c' < 1/2}` by the
two-sided 2-D box iff (`prodBoxSymm_rpow_integrableOn_iff`): forward exhibits the open box
`entryME⁻¹((-1,1)²)`; reverse pushes any neighbourhood of `0` forward (homeomorphism) to a box
`[-ε,ε]²` on which divergence forces `c' < 1/2`. Its `sSup` in `ℝ≥0∞` is `1/2`. -/

/-- The two scalar entries of `A`, packaged as `ℝ²`, via `paramsEquivFlat`: a measure-preserving
homeomorphism `Params (1,1,1) ≃ᵐ ℝ × ℝ`. The transport channel for the `(1,1,1)` RLCT. -/
noncomputable def entryME : Params (![1, 1, 1] : Fin 3 → ℕ) ≃ᵐ (ℝ × ℝ) :=
  (paramsEquivFlat (![1, 1, 1] : Fin 3 → ℕ)).trans MeasurableEquiv.finTwoArrow

/-- `entryME` is measure-preserving (`paramsEquivFlat` is, and `finTwoArrow` is). -/
theorem measurePreserving_entryME : MeasurePreserving entryME
    (volume : Measure (Params (![1, 1, 1] : Fin 3 → ℕ))) (volume : Measure (ℝ × ℝ)) :=
  (measurePreserving_paramsEquivFlat _).trans (measurePreserving_finTwoArrow volume)

/-- `entryME v = (v 0, v 1)`-style continuity (`finTwoArrow ∘ paramsEquivFlat`, both continuous). -/
theorem continuous_entryME : Continuous entryME := by
  have hft : Continuous (MeasurableEquiv.finTwoArrow (α := ℝ)) := by
    rw [show (⇑(MeasurableEquiv.finTwoArrow (α := ℝ))) = fun v : Fin 2 → ℝ => (v 0, v 1) from rfl]
    exact (continuous_apply 0).prodMk (continuous_apply 1)
  exact hft.comp (continuous_paramsEquivFlat _)

/-- `entryME.symm` is continuous, so `entryME` is a homeomorphism (forward image of a neighbourhood
is a neighbourhood). -/
theorem continuous_entryME_symm : Continuous entryME.symm := by
  have hft : Continuous (MeasurableEquiv.finTwoArrow (α := ℝ)).symm := by
    rw [show (⇑(MeasurableEquiv.finTwoArrow (α := ℝ)).symm) = fun p : ℝ × ℝ => ![p.1, p.2] from rfl]
    apply continuous_pi; intro i
    fin_cases i
    · exact continuous_fst
    · exact continuous_snd
  exact (continuous_paramsEquivFlat_symm _).comp hft

/-- `entryME` sends the deepest point (the origin) to `(0,0)`. -/
theorem entryME_deepest111 : entryME deepest111 = (0, 0) := by
  change (MeasurableEquiv.finTwoArrow ((paramsEquivFlat (![1, 1, 1] : Fin 3 → ℕ)) deepest111))
    = (0, 0)
  rw [show (⇑(MeasurableEquiv.finTwoArrow (α := ℝ))) = fun v : Fin 2 → ℝ => (v 0, v 1) from rfl]
  have h0 : (paramsEquivFlat (![1, 1, 1] : Fin 3 → ℕ)) deepest111 (0 : Fin 2) = 0 := rfl
  have h1 : (paramsEquivFlat (![1, 1, 1] : Fin 3 → ℕ)) deepest111 (1 : Fin 2) = 0 := rfl
  simp only [h0, h1]

/-- The product of the two scalar entries equals the product of the two `ℝ²`-coordinates of
`entryME` (`paramsEquivFlat` preserves the full coordinate product). -/
theorem entryME_prod (A : Params (![1, 1, 1] : Fin 3 → ℕ)) :
    A 0 (0 : Fin 1) (0 : Fin 1) * A 1 (0 : Fin 1) (0 : Fin 1) = (entryME A).1 * (entryME A).2 := by
  have h2 : (entryME A).1 * (entryME A).2
      = ∏ i, (paramsEquivFlat (![1, 1, 1] : Fin 3 → ℕ)) A i := by
    rw [show (∏ i, (paramsEquivFlat (![1, 1, 1] : Fin 3 → ℕ)) A i)
          = (paramsEquivFlat (![1, 1, 1] : Fin 3 → ℕ)) A (0 : Fin 2)
            * (paramsEquivFlat (![1, 1, 1] : Fin 3 → ℕ)) A (1 : Fin 2) from Fin.prod_univ_two _]
    rfl
  rw [h2, prod_paramsEquivFlat, prod_entries_case111]

/-- The `(1,1,1)` integrand `|dlnLoss A|^{−c'}` is the pullback of `|x·y|^{−2c'}` along
`entryME`. -/
theorem integrand_eq_comp (c' : NNReal) :
    (fun A : Params (![1, 1, 1] : Fin 3 → ℕ) =>
        |dlnLoss (![1, 1, 1] : Fin 3 → ℕ) 0 A| ^ (-(c' : ℝ)))
      = (fun p : ℝ × ℝ => |p.1 * p.2| ^ (-2 * (c' : ℝ))) ∘ entryME := by
  funext A
  simp only [Function.comp_apply]
  rw [dlnLoss_case111, entryME_prod]
  set t := (entryME A).1 * (entryME A).2 with ht
  rw [show |t ^ 2| = |t| ^ 2 by rw [abs_pow], ← Real.rpow_natCast (|t|) 2,
    ← Real.rpow_mul (abs_nonneg _)]
  norm_num

/-- From a neighbourhood of `(0,0)` in `ℝ²`, extract a symmetric box `[-ε,ε]²` (ε>0) inside it
(`ℝ²` has the sup metric, so a metric ball contains such a box). -/
theorem box_subset_of_mem_nhds (s : Set (ℝ × ℝ)) (hs : s ∈ 𝓝 ((0, 0) : ℝ × ℝ)) :
    ∃ ε > 0, Set.Icc (-ε) ε ×ˢ Set.Icc (-ε) ε ⊆ s := by
  rw [Metric.mem_nhds_iff] at hs
  obtain ⟨δ, hδ, hball⟩ := hs
  refine ⟨δ / 2, by positivity, fun p hp => hball ?_⟩
  simp only [Set.mem_prod, Set.mem_Icc] at hp
  rw [Metric.mem_ball, Prod.dist_eq]
  simp only [dist_zero_right]
  have h1 : |p.1| ≤ δ / 2 := abs_le.mpr ⟨hp.1.1, hp.1.2⟩
  have h2 : |p.2| ≤ δ / 2 := abs_le.mpr ⟨hp.2.1, hp.2.2⟩
  have hmax : max ‖p.1‖ ‖p.2‖ ≤ δ / 2 := by
    simp only [Real.norm_eq_abs]; exact max_le h1 h2
  calc max ‖p.1‖ ‖p.2‖ ≤ δ / 2 := hmax
    _ < δ := by linarith

/-- **The baby-S1.1 bridge (now proven, axiom-free).** The local RLCT of the already-normal-crossing
`(1,1,1)` loss at the deepest point equals the monomial-model threshold `1/2` of its
`(k,h) = ((1,1),(0,0))` data. Proven directly: `rlctAt = 1/2` via the measure-preserving
homeomorphism `entryME : Params (1,1,1) ≃ᵐ ℝ²` (`Case111Bridge`) — the admissible-exponent set is
the coerced `{c' < 1/2}` (`prodBoxSymm_rpow_integrableOn_iff`), whose `sSup` is `1/2`. The RHS is
`1/2`
axiom-free (`monomialThreshold_case111`), so the whole headline is now axiom-free. -/
theorem case111_rlct_eq_monomialThreshold :
    rlctAt (![1, 1, 1] : Fin 3 → ℕ) (dlnLoss (![1, 1, 1] : Fin 3 → ℕ) 0) deepest111
      = monomialThreshold 2 (![1, 1] : Fin 2 → ℕ) (![0, 0] : Fin 2 → ℕ) := by
  rw [monomialThreshold_case111]
  unfold rlctAt
  have hemb : MeasurableEmbedding entryME := entryME.measurableEmbedding
  have hset : { c : ℝ≥0∞ | ∃ c' : NNReal, c = (c' : ℝ≥0∞) ∧
        ∃ U ∈ 𝓝 deepest111,
          IntegrableOn (fun w => |dlnLoss (![1, 1, 1] : Fin 3 → ℕ) 0 w| ^ (-(c' : ℝ))) U volume }
      = { c : ℝ≥0∞ | ∃ c' : NNReal, c = (c' : ℝ≥0∞) ∧ (c' : ℝ) < 1 / 2 } := by
    ext c; constructor
    · rintro ⟨c', rfl, U, hU, hint⟩
      refine ⟨c', rfl, ?_⟩
      have hUeq : U = entryME ⁻¹' (entryME '' U) := (Set.preimage_image_eq _ hemb.injective).symm
      rw [integrand_eq_comp c', hUeq,
        (measurePreserving_entryME).integrableOn_comp_preimage hemb] at hint
      have himg : entryME '' U ∈ 𝓝 ((0, 0) : ℝ × ℝ) := by
        rw [MeasurableEquiv.image_eq_preimage_symm, ← entryME_deepest111]
        exact continuous_entryME_symm.continuousAt.preimage_mem_nhds
          (by rwa [entryME.symm_apply_apply])
      obtain ⟨ε, hε, hsub⟩ := box_subset_of_mem_nhds _ himg
      have hbox : IntegrableOn (fun p : ℝ × ℝ => |p.1 * p.2| ^ (-2 * (c' : ℝ)))
          (Set.Icc (-ε) ε ×ˢ Set.Icc (-ε) ε) (volume.prod volume) := by
        rw [← Measure.volume_eq_prod]; exact hint.mono_set hsub
      exact (prodBoxSymm_rpow_integrableOn_iff _ ε hε).1 hbox
    · rintro ⟨c', rfl, hc⟩
      refine ⟨c', rfl, entryME ⁻¹' (Set.Ioo (-1 : ℝ) 1 ×ˢ Set.Ioo (-1 : ℝ) 1), ?_, ?_⟩
      · apply continuous_entryME.continuousAt.preimage_mem_nhds
        rw [entryME_deepest111]
        exact (isOpen_Ioo.prod isOpen_Ioo).mem_nhds (by constructor <;> constructor <;> norm_num)
      · rw [integrand_eq_comp c', (measurePreserving_entryME).integrableOn_comp_preimage hemb]
        have hbox : IntegrableOn (fun p : ℝ × ℝ => |p.1 * p.2| ^ (-2 * (c' : ℝ)))
            (Set.Icc (-1) 1 ×ˢ Set.Icc (-1) 1) (volume.prod volume) :=
          (prodBoxSymm_rpow_integrableOn_iff _ 1 (by norm_num)).2 hc
        rw [← Measure.volume_eq_prod] at hbox
        exact hbox.mono_set (Set.prod_mono Set.Ioo_subset_Icc_self Set.Ioo_subset_Icc_self)
  rw [hset]
  apply le_antisymm
  · apply sSup_le; rintro c ⟨c', rfl, hc⟩
    rw [show (1 / 2 : ℝ≥0∞) = ((1 / 2 : NNReal) : ℝ≥0∞) by simp]
    rw [ENNReal.coe_le_coe, ← NNReal.coe_le_coe]; push_cast; linarith
  · apply le_of_forall_lt_imp_le_of_dense
    intro q hq
    have hqfin : q ≠ ⊤ := by intro h; rw [h] at hq; simp at hq
    apply le_sSup
    refine ⟨q.toNNReal, (ENNReal.coe_toNNReal hqfin).symm, ?_⟩
    have hqt : q.toReal < (1 / 2 : ℝ) := by
      have := (ENNReal.toReal_lt_toReal hqfin (by simp : (1 / 2 : ℝ≥0∞) ≠ ⊤)).2 hq
      simpa using this
    exact hqt

/-- **The `(1,1,1)` headline (sorry-free, AXIOM-FREE).** The local RLCT of the deep-linear loss at
the deepest point of the `B = 0` fibre equals Aoyagi's closed form `aoyagiLambda (1,1,1) 0 = 1/2`.
The first fully end-to-end `(1,1,1)` result: `#print axioms = [propext, Classical.choice,
Quot.sound]` (no `sorryAx`, no `monomial_rlct`). Assembled from the now-proven baby-S1.1 bridge
`case111_rlct_eq_monomialThreshold` and the sorry-free `case111_monomialThreshold`. -/
theorem case111_rlct :
    rlctAt (![1, 1, 1] : Fin 3 → ℕ) (dlnLoss (![1, 1, 1] : Fin 3 → ℕ) 0) deepest111
      = ENNReal.ofReal (aoyagiLambda (![1, 1, 1] : Fin 3 → ℕ) 0) := by
  rw [case111_rlct_eq_monomialThreshold, case111_monomialThreshold]

/-- **The `(1,1,1)` instance of `resolution_charts` (CORE form; axiom-free).** Matches the
re-scoped (14th-finding) general `resolution_charts`: the core `dlnLoss M 0` on `Params M` at the
origin, `rlctAtOn(core)(0) = ⨅ monomialThreshold`. For the trivial network `M = (1,1,1)` the core IS
the full loss (`r = 0`, regular shift `0`), the deepest point is `deepest111 = 0`, and the datum is
the single identity chart `ι = Unit`, `d = 2`, `k = (1,1)`, `h = (0,0)` (already normal-crossing, no
blow-up). Validates the R1 plumbing against the known answer — `⨅`-over-`Unit` collapses
(`iInf_unique`), `rlctAtOn = rlctAt` on `Params`, to the proven bridge
`case111_rlct_eq_monomialThreshold` (= `1/2`, the value `case111_rlct` lands on). A worked closed
instance of the (core-scoped) `resolution_charts` the general R1 must reproduce. -/
theorem resolution_charts_case111 :
    ∃ (ι : Type) (_ : Fintype ι) (d : ι → ℕ) (k h : (i : ι) → Fin (d i) → ℕ),
      rlctAtOn (fun A : Params (![1, 1, 1] : Fin 3 → ℕ) =>
          dlnLoss (![1, 1, 1] : Fin 3 → ℕ) (0 : Matrix (Fin 1) (Fin 1) ℝ) A) deepest111
        = ⨅ i : ι, monomialThreshold (d i) (k i) (h i) :=
  ⟨Unit, inferInstance, fun _ => 2, fun _ => (![1, 1] : Fin 2 → ℕ), fun _ => (![0, 0] : Fin 2 → ℕ),
    by rw [show (fun A : Params (![1, 1, 1] : Fin 3 → ℕ) =>
              dlnLoss (![1, 1, 1] : Fin 3 → ℕ) (0 : Matrix (Fin 1) (Fin 1) ℝ) A)
            = dlnLoss (![1, 1, 1] : Fin 3 → ℕ) 0 from rfl,
          rlctAtOn_eq_rlctAt, case111_rlct_eq_monomialThreshold, iInf_unique]⟩

end DLNFibre.DLN.RLCT
