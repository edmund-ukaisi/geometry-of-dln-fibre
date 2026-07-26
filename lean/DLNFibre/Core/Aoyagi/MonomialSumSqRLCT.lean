import DLNFibre.Core.Aoyagi.MonomialRLCT
import DLNFibre.Core.Analysis.RLCT.SumSq

/-!
# `Core.Aoyagi.MonomialSumSqRLCT` — the monomial × sum-of-squares product RLCT engine

The value read-off for the **over-vanishing** (3,3,4) leaves. Unlike the clean-144 single-survivor
path (a divisibility CHAIN, `monomialSumSq_integrableAtFilter_of_lt`), the over-vanishing loss
pulls back to a monomial-squared times a NONDEGENERATE sum-of-squares in a DISJOINT block of
`jac`-free coordinates:

`loss ∘ g_c ≥ vm(u)² · ∑_{j ∈ Z} u_j²`   (`vm = ∏_d u_d^{a_d}`, `Z` = the 8 reg-seq coords).

The chain engine is DEAD here: it collapses `∑ bₖ²` to `b_{k₀}²·U` (`U ≥ 1` a UNIT, used as an
UPPER bound `U^{-c} ≤ M`), so it captures only `monomialThreshold(b_{k₀}) = ½` (`jac`-0 on `vm`'s
binding axes) — it discards the sum-of-squares vanishing. The honest value is the PRODUCT threshold

`min( monomialThreshold(vm², jac) , |Z| / 2 )`

— the `|Z|/2` (`= r/2`) comes from the nondegenerate `∑_{j∈Z} u_j²` (`RLCT.SumSq`, `rlctAt_sumSq`),
and it is invisible to the chain engine. Because `Z` is disjoint from `supp(vm) = supp(jac)` and
carries `jac = 0`, the weighted box integral FACTORS over the two coordinate blocks (Tonelli through
`MeasurableEquiv.piEquivPiSubtypeProd`): the `Z`-block gives the sum-of-squares threshold `|Z|/2`,
the complement gives the pure-power monomial threshold. The chart `unit`
(`|det Dg| = jacWeight·|unit|`) COUPLES the two blocks and does NOT factor — for the convergence
(`≥`) direction it is bounded by its `sup` on a compact neighbourhood (elder amendment A), so the
factorization is applied only to the unit-free integrand.

**Direction warning (do not re-derive the naive way).** The toric-LP over the term-ideal
`M = ⟨all monomials of all generators⟩ ⊇ I = ⟨gᵢ⟩` is an UPPER bound on the true RLCT, not a lower
bound: SoS-RLCT is monotone INCREASING under ideal inclusion (`I ⊆ M ⟹ ∑_M h² ≥ ∑_I h²` pointwise
`⟹ rlct(I) ≤ rlct(M)` — more generators = larger sum = less singular = larger RLCT; equality iff `I`
is already monomial, the clean leaves). So the honest over-vanishing LOWER bound is THIS
regular-sequence / sum-of-squares engine, never the toric-LP.

## Scope (honest)
- IN: the network-free product-germ integrability at an arbitrary base point `p`
  (`monoSumSq_integrableAtFilter_of_lt`), the ≥-direction the V-lower wire consumes; plus the
  null-zero guard + measurability the domination leg
  (`wLocalAdmissibleExponents_subset_of_eventually_le`) needs.
- OUT: the two-sided `rlctAt … = min` equality (the `≤` half needs the unit `inf > 0`
  marginalization); the DLN instantiation (the over-vanishing pullback identity
  `loss ∘ gFin c = vm²·∑vf²`, the regular-sequence `Ψ` straightening, the cover) — the
  `DLN.Aoyagi` over-vanishing seat.

## Status
COMPLETE, sorry-free (`#print axioms` = `[propext, Classical.choice, Quot.sound]`): the germ + its
null-zero/measurability/nonneg facts, and the main weighted integrability engine
`monoSumSq_integrableAtFilter_of_lt` (the disjoint-block Tonelli, `-- map: ov-sos-tonelli`). The
Tonelli factors are packaged as three reusable private atoms: `boxSumSqNegPow_integrableOn_fin`
(`Fin`-indexed sum-of-squares ball threshold via `RLCT.SumSq`), `boxSumSqNegPow_integrableOn`
(its `Fintype`-general reindex), and `boxProdRpow_lintegral_lt_top` (`Fintype`-general power box
via `MonomialBox.prodRpow_boxSymm_lt_top`).
-/

open MeasureTheory Set Filter Topology RLCT

namespace DLNFibre.Core.Aoyagi

variable {D : ℕ}

/-- **The monomial × sum-of-squares product germ.** `(∏_d u_d^{a_d})² · ∑_{j ∈ Z} (u_j)²`: the
over-vanishing loss lower bound (monomial `vm = ∏_d u_d^{a_d}` squared, times the nondegenerate
sum-of-squares over the regular-sequence coordinate block `Z`). -/
noncomputable def monoSumSqGerm (a : Fin D → ℕ) (Z : Finset (Fin D)) : (Fin D → ℝ) → ℝ :=
  fun u ↦ (∏ d, (u d) ^ (a d)) ^ 2 * ∑ j ∈ Z, (u j) ^ 2

/-- The product germ is nonnegative. -/
theorem monoSumSqGerm_nonneg (a : Fin D → ℕ) (Z : Finset (Fin D)) (u : Fin D → ℝ) :
    0 ≤ monoSumSqGerm a Z u := by
  unfold monoSumSqGerm
  exact mul_nonneg (sq_nonneg _) (Finset.sum_nonneg fun j _ ↦ sq_nonneg _)

/-- The product germ is measurable (a polynomial in the coordinates). -/
theorem measurable_monoSumSqGerm (a : Fin D → ℕ) (Z : Finset (Fin D)) :
    Measurable (monoSumSqGerm a Z) := by
  unfold monoSumSqGerm
  fun_prop

/-- **The zero set of the product germ is null** (given `Z` nonempty): `monoSumSqGerm a Z u = 0`
forces `∏ u_d^{a_d} = 0` (some binding `u_d = 0`) or `∑_{Z} u_j² = 0` (every `u_j = 0`, `j ∈ Z`) —
either way SOME coordinate vanishes, so the zero set sits inside the finite union of coordinate
hyperplanes `⋃_d {u_d = 0}`, which is null. This is the `LocallyNullZeros` guard the domination leg
(`wLocalAdmissibleExponents_subset_of_eventually_le`) needs. -/
theorem locallyNullZeros_monoSumSqGerm (a : Fin D → ℕ) {Z : Finset (Fin D)} (hZ : Z.Nonempty)
    (p : Fin D → ℝ) : LocallyNullZeros (monoSumSqGerm a Z) p := by
  classical
  obtain ⟨j₀, hj₀⟩ := hZ
  -- each coordinate hyperplane is null.
  have hcoord : ∀ d : Fin D, volume {u : Fin D → ℝ | u d = 0} = 0 := by
    intro d
    have hset : {u : Fin D → ℝ | u d = 0}
        = Set.univ.pi (fun i ↦ if i = d then ({0} : Set ℝ) else Set.univ) := by
      ext u
      simp only [Set.mem_setOf_eq, Set.mem_pi, Set.mem_univ, true_implies]
      constructor
      · intro hud i; split_ifs with hi
        · rw [hi]; exact hud
        · trivial
      · intro hall; have := hall d; simpa using this
    rw [hset, volume_pi_pi]
    exact Finset.prod_eq_zero (Finset.mem_univ d) (by simp)
  -- the zero set is contained in `⋃_d {u_d = 0}`.
  have hsub : {u : Fin D → ℝ | monoSumSqGerm a Z u = 0} ⊆ ⋃ d : Fin D, {u | u d = 0} := by
    intro u hu
    simp only [Set.mem_setOf_eq, monoSumSqGerm] at hu
    rcases mul_eq_zero.mp hu with hvm | hsum
    · -- `(∏ u_d^{a_d})² = 0` ⟹ some factor `u_d^{a_d} = 0` ⟹ `u_d = 0`.
      have hprod : (∏ d, (u d) ^ (a d)) = 0 := (pow_eq_zero_iff (two_ne_zero)).mp hvm
      obtain ⟨d, _, hd⟩ := Finset.prod_eq_zero_iff.mp hprod
      have had : a d ≠ 0 := by rintro h0; rw [h0, pow_zero] at hd; exact one_ne_zero hd
      exact Set.mem_iUnion.mpr ⟨d, (pow_eq_zero_iff had).mp hd⟩
    · -- `∑_{Z} u_j² = 0` ⟹ every `u_j = 0` for `j ∈ Z` ⟹ `u_{j₀} = 0`.
      have hall : ∀ j ∈ Z, (u j) ^ 2 = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg fun j _ ↦ sq_nonneg _).mp hsum
      exact Set.mem_iUnion.mpr ⟨j₀, (pow_eq_zero_iff (two_ne_zero)).mp (hall j₀ hj₀)⟩
  refine ⟨Set.univ, Filter.univ_mem, ?_⟩
  refine measure_mono_null (Set.inter_subset_left.trans hsub) ?_
  exact measure_iUnion_null (fun d ↦ hcoord d)

/-- **The over-vanishing product threshold** `min( monomialThreshold(a, jac), |Z|/2 )`. The value
the product germ's weighted RLCT attains: the monomial threshold of `vm` on its binding axes, capped
by the sum-of-squares threshold `|Z|/2` (`= r/2`) of the regular-sequence block. -/
noncomputable def monoSumSqThreshold (a jac : Fin D → ℕ) (Z : Finset (Fin D))
    (hbind : (bindingAxes a).Nonempty) : ℝ :=
  min (monomialThreshold a jac hbind) (Z.card / 2 : ℝ)

/-! ### Disjoint-block box-integrability atoms (the Tonelli factors) -/

/-- **`Fin`-indexed sum-of-squares box integrability.** On the symmetric box `(−ε, ε)^{m+1}`, the
negative power `(∑ i, (y i)²)^{-cc}` is integrable for `2·cc < m+1`. Transports the `EuclideanSpace`
ball threshold `RLCT.integrableOn_ball_norm_rpow_iff` (`(∑(·)²)^{-cc}=‖·‖^{-2cc}` via `sumSq_ofLp`,
the box sits inside an ℓ²-ball) through the volume-preserving `WithLp.ofLp`. -/
private theorem boxSumSqNegPow_integrableOn_fin {n : ℕ} (hn : 0 < n) {ε cc : ℝ}
    (hε : 0 < ε) (hc0 : 0 ≤ cc) (hsos : 2 * cc < (n : ℝ)) :
    IntegrableOn (fun y : Fin n → ℝ ↦ (∑ i, (y i) ^ 2) ^ (-cc))
      (Set.univ.pi (fun _ : Fin n ↦ Set.Ioo (-ε) ε)) volume := by
  classical
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rcases eq_or_lt_of_le hc0 with hcc | hcc
  · -- `cc = 0`: the germ is the constant `1`; the box has finite measure.
    have hfin : volume (Set.univ.pi (fun _ : Fin (m + 1) ↦ Set.Ioo (-ε) ε)) ≠ (⊤ : ENNReal) := by
      rw [volume_pi_pi]
      refine ENNReal.prod_ne_top (fun i _ ↦ ?_)
      rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top
    have hone : (fun y : Fin (m + 1) → ℝ ↦ (∑ i, (y i) ^ 2) ^ (-cc))
        = fun _ ↦ (1 : ℝ) := by
      funext y; rw [← hcc]; simp
    rw [hone]; exact integrableOn_const hfin
  · -- `cc > 0`: transport to `EuclideanSpace`, dominate by an ℓ²-ball.
    set e : EuclideanSpace ℝ (Fin (m + 1)) → (Fin (m + 1) → ℝ) := WithLp.ofLp with he
    have hemb : MeasurableEmbedding e :=
      (MeasurableEquiv.toLp 2 (Fin (m + 1) → ℝ)).symm.measurableEmbedding
    have hmp : MeasurePreserving e (volume : Measure (EuclideanSpace ℝ (Fin (m + 1)))) volume :=
      PiLp.volume_preserving_ofLp (Fin (m + 1))
    rw [← hmp.integrableOn_comp_preimage hemb]
    -- the pulled-back germ is `‖·‖^{-2cc}`.
    set ρ : ℝ := Real.sqrt ((m + 1 : ℝ) * ε ^ 2) with hρdef
    have hρ : 0 < ρ := by
      rw [hρdef]; apply Real.sqrt_pos.2; positivity
    have hcomp : (fun y : Fin (m + 1) → ℝ ↦ (∑ i, (y i) ^ 2) ^ (-cc)) ∘ e
        = fun x : EuclideanSpace ℝ (Fin (m + 1)) ↦ ‖x‖ ^ (-(2 * cc)) := by
      funext x
      simp only [Function.comp_apply, he]
      rw [show (∑ i, ((WithLp.ofLp x) i) ^ 2) = sumSq (m + 1) (WithLp.ofLp x) from rfl,
        sumSq_ofLp x, ← Real.rpow_natCast ‖x‖ 2, ← Real.rpow_mul (norm_nonneg x)]
      ring_nf
    rw [hcomp]
    have hsub : e ⁻¹' (Set.univ.pi (fun _ : Fin (m + 1) ↦ Set.Ioo (-ε) ε))
        ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin (m + 1))) ρ := by
      intro x hx
      simp only [Set.mem_preimage, he, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Ioo] at hx
      rw [Metric.mem_ball, dist_zero_right, EuclideanSpace.norm_eq, hρdef]
      apply Real.sqrt_lt_sqrt (Finset.sum_nonneg (fun i _ ↦ by positivity))
      calc ∑ i, ‖x i‖ ^ 2 < ∑ _i : Fin (m + 1), ε ^ 2 := by
              refine Finset.sum_lt_sum_of_nonempty ⟨0, Finset.mem_univ 0⟩ (fun i _ ↦ ?_)
              rw [Real.norm_eq_abs, sq_abs]
              have := hx i; exact sq_lt_sq' (by linarith [this.1]) this.2
        _ = (m + 1 : ℝ) * ε ^ 2 := by
              rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]; push_cast; ring
    have hballint : IntegrableOn (fun x : EuclideanSpace ℝ (Fin (m + 1)) ↦ ‖x‖ ^ (-(2 * cc)))
        (Metric.ball 0 ρ) volume :=
      (integrableOn_ball_norm_rpow_iff hρ (by linarith : -(2 * cc) < 0)).2
        (by push_cast at hsos ⊢; linarith)
    exact hballint.mono_set hsub

/-- **Fintype-general sum-of-squares box integrability.** Any nonempty finite index `ι` with
`2·cc < card ι`: reindexes `ι` to `Fin (card ι)` (a coordinate permutation, volume-preserving) and
reads off `boxSumSqNegPow_integrableOn_fin`. -/
private theorem boxSumSqNegPow_integrableOn {ι : Type*} [Fintype ι] [Nonempty ι] {ε cc : ℝ}
    (hε : 0 < ε) (hc0 : 0 ≤ cc) (hsos : 2 * cc < (Fintype.card ι : ℝ)) :
    IntegrableOn (fun y : ι → ℝ ↦ (∑ i, (y i) ^ 2) ^ (-cc))
      (Set.univ.pi (fun _ : ι ↦ Set.Ioo (-ε) ε)) volume := by
  classical
  set φ : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm with hφ
  set eI : (Fin (Fintype.card ι) → ℝ) ≃ᵐ (ι → ℝ) :=
    MeasurableEquiv.piCongrLeft (fun _ : ι ↦ ℝ) φ with heI
  have hmp : MeasurePreserving eI (volume : Measure (Fin (Fintype.card ι) → ℝ)) volume :=
    volume_measurePreserving_piCongrLeft (fun _ : ι ↦ ℝ) φ
  rw [← (hmp.integrableOn_comp_preimage eI.measurableEmbedding)]
  -- the box preimage is the `Fin`-box, and the pulled-back germ is the `Fin` sum-of-squares.
  have hpre : eI ⁻¹' (Set.univ.pi (fun _ : ι ↦ Set.Ioo (-ε) ε))
      = Set.univ.pi (fun _ : Fin (Fintype.card ι) ↦ Set.Ioo (-ε) ε) := by
    ext v
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies, heI]
    constructor
    · intro hall i'; have := hall (φ i'); rwa [MeasurableEquiv.piCongrLeft_apply_apply] at this
    · intro hall i
      obtain ⟨i', rfl⟩ := φ.surjective i
      rw [MeasurableEquiv.piCongrLeft_apply_apply]; exact hall i'
  have hcomp : (fun y : ι → ℝ ↦ (∑ i, (y i) ^ 2) ^ (-cc)) ∘ eI
      = fun v : Fin (Fintype.card ι) → ℝ ↦ (∑ i', (v i') ^ 2) ^ (-cc) := by
    funext v
    simp only [Function.comp_apply, heI]
    congr 1
    rw [← Equiv.sum_comp φ (fun i : ι ↦ ((eI v) i) ^ 2)]
    exact Finset.sum_congr rfl (fun i' _ ↦ by rw [heI, MeasurableEquiv.piCongrLeft_apply_apply])
  rw [hpre, hcomp]
  exact boxSumSqNegPow_integrableOn_fin Fintype.card_pos hε hc0 hsos

/-- **Fintype-general symmetric-box pure-power finiteness.** For any finite index `ι`, a product of
`rpow`s `∏ i, |w i|^{f i}` with every exponent `> −1` has finite box lintegral. Reindexes `ι` to
`Fin (card ι)` and reads off `MonomialBox.prodRpow_boxSymm_lt_top`. -/
private theorem boxProdRpow_lintegral_lt_top {ι : Type*} [Fintype ι] {ε : ℝ} (hε : 0 < ε)
    (f : ι → ℝ) (hf : ∀ i, -1 < f i) :
    ∫⁻ w in Set.univ.pi (fun _ : ι ↦ Set.Ioo (-ε) ε),
        ENNReal.ofReal (∏ i, |w i| ^ (f i)) ∂(volume : Measure (ι → ℝ)) < ⊤ := by
  classical
  set φ : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm with hφ
  set eI : (Fin (Fintype.card ι) → ℝ) ≃ᵐ (ι → ℝ) :=
    MeasurableEquiv.piCongrLeft (fun _ : ι ↦ ℝ) φ with heI
  have hmp : MeasurePreserving eI (volume : Measure (Fin (Fintype.card ι) → ℝ)) volume :=
    volume_measurePreserving_piCongrLeft (fun _ : ι ↦ ℝ) φ
  have htrans := hmp.setLIntegral_comp_preimage_emb eI.measurableEmbedding
    (fun w : ι → ℝ ↦ ENNReal.ofReal (∏ i, |w i| ^ (f i)))
    (Set.univ.pi (fun _ : ι ↦ Set.Ioo (-ε) ε))
  have hpre : eI ⁻¹' (Set.univ.pi (fun _ : ι ↦ Set.Ioo (-ε) ε))
      = Set.univ.pi (fun _ : Fin (Fintype.card ι) ↦ Set.Ioo (-ε) ε) := by
    ext v
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies, heI]
    constructor
    · intro hall i'; have := hall (φ i'); rwa [MeasurableEquiv.piCongrLeft_apply_apply] at this
    · intro hall i
      obtain ⟨i', rfl⟩ := φ.surjective i
      rw [MeasurableEquiv.piCongrLeft_apply_apply]; exact hall i'
  rw [hpre] at htrans
  rw [← htrans]
  have hfun : ∀ v : Fin (Fintype.card ι) → ℝ,
      (∏ i : ι, |(eI v) i| ^ (f i)) = ∏ i' : Fin (Fintype.card ι), |v i'| ^ (f (φ i')) := by
    intro v
    rw [← Equiv.prod_comp φ (fun i : ι ↦ |(eI v) i| ^ (f i))]
    exact Finset.prod_congr rfl (fun i' _ ↦ by rw [heI, MeasurableEquiv.piCongrLeft_apply_apply])
  simp_rw [hfun]
  exact MonomialBox.prodRpow_boxSymm_lt_top hε (fun i' ↦ f (φ i')) (fun i' ↦ hf (φ i'))

/-- **The over-vanishing weighted integrability engine (≥ direction).** For a weight `W` that near
`p` factors as the monomial Jacobian weight `jacWeight jac` times a continuous nonvanishing `unit`,
and for `cc` below BOTH the monomial threshold of `vm` on its binding axes AND the sum-of-squares
threshold `|Z|/2`, the weighted product germ `W · (vm²·∑_{Z} u_j²)^{-cc}` is integrable on a
neighbourhood of `p`. The regular-sequence block `Z` is disjoint from `supp(vm)` and carries
`jac = 0` there (`hZjac`, `hZa`), so — after bounding `unit` by its `sup` near `p` (elder amendment
A: the unit COUPLES the blocks and does not factor) — the unit-free box integral factors (Tonelli,
`MeasurableEquiv.piEquivPiSubtypeProd`) into the `Z`-block sum-of-squares integral (finite for
`2·cc < |Z|`, `RLCT.SumSq`) and the complement pure-power monomial box integral (finite for the
threshold, `MonomialBox`).

The `≥`-direction (convergence) is what the V-lower wire consumes; the two-sided `= min` equality is
OUT (needs the unit `inf > 0` marginalization). -/
theorem monoSumSq_integrableAtFilter_of_lt
    {a jac : Fin D → ℕ} {Z : Finset (Fin D)} {W unit : (Fin D → ℝ) → ℝ} {p : Fin D → ℝ} {cc : ℝ}
    (hbind : (bindingAxes a).Nonempty) (hZne : Z.Nonempty)
    (hZa : ∀ j ∈ Z, a j = 0) (hZjac : ∀ j ∈ Z, jac j = 0)
    (hc0 : 0 ≤ cc)
    (hthr : cc < monomialThreshold a jac hbind) (hsos : 2 * cc < (Z.card : ℝ))
    (hunit : ContinuousAt unit p) (hunit0 : unit p ≠ 0) (hunitmeas : Measurable unit)
    (hW : ∀ᶠ u in 𝓝 p, W u = jacWeight jac u * unit u) :
    IntegrableAtFilter (fun u ↦ W u * negPow (monoSumSqGerm a Z) cc u) (𝓝 p) := by
  -- map: ov-sos-tonelli — the disjoint-block Tonelli factorization (Z-block sum-of-squares via
  -- RLCT.SumSq × complement pure-power box via MonomialBox), after the unit-sup reduction.
  classical
  -- pin the coordinate-subtype `Fintype`s to `Subtype.fintype` so the split-equiv transport measure
  -- forms agree with the box factors' `volume` (dodges a `FinsetCoe`/`Subtype` instance diamond).
  letI : Fintype {x // x ∈ Z} := Subtype.fintype _
  letI : Fintype {x // ¬ x ∈ Z} := Subtype.fintype _
  -- reduced per-axis exponents `ev d = jac_d − 2·a_d·cc`: all `> −1` below threshold, `= 0` on `Z`.
  set ev : Fin D → ℝ := fun d ↦ (jac d : ℝ) - 2 * (a d : ℝ) * cc with hev
  have hβ : ∀ d, -1 < ev d :=
    (monomial_forall_neg_one_lt_iff_lt_threshold (fun _ : Fin 1 ↦ a) jac 0 hbind cc).mpr hthr
  have hevZ : ∀ d ∈ Z, ev d = 0 := by
    intro d hd; simp only [hev, hZa d hd, hZjac d hd]; norm_num
  -- the unit-free integrand `g = mono · sos^{-cc}` and its split factors over `Z ⊔ Zᶜ`.
  set mono : (Fin D → ℝ) → ℝ :=
    fun u ↦ jacWeight jac u * ((∏ d, (u d) ^ (a d)) ^ 2) ^ (-cc) with hmonodef
  set sos : (Fin D → ℝ) → ℝ := fun u ↦ ∑ j ∈ Z, (u j) ^ 2 with hsosdef
  set g : (Fin D → ℝ) → ℝ := fun u ↦ mono u * (sos u) ^ (-cc) with hgdef
  set e : (Fin D → ℝ) ≃ᵐ (({i // i ∈ Z} → ℝ) × ({i // ¬ i ∈ Z} → ℝ)) :=
    MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Fin D ↦ ℝ) (· ∈ Z) with hedef
  set Fsub : ({i // i ∈ Z} → ℝ) → ℝ := fun y ↦ (∑ i, (y i) ^ 2) ^ (-cc) with hFsubdef
  set Gsub : ({i // ¬ i ∈ Z} → ℝ) → ℝ := fun w ↦ ∏ d, |w d| ^ (ev ↑d) with hGsubdef
  set H : (({i // i ∈ Z} → ℝ) × ({i // ¬ i ∈ Z} → ℝ)) → ℝ :=
    fun z ↦ Fsub z.1 * Gsub z.2 with hHdef
  -- component read-off of the split equiv.
  have he1 : ∀ (u : Fin D → ℝ) (i : {i // i ∈ Z}), (e u).1 i = u ↑i := fun _ _ ↦ rfl
  have he2 : ∀ (u : Fin D → ℝ) (i : {i // ¬ i ∈ Z}), (e u).2 i = u ↑i := fun _ _ ↦ rfl
  -- measurability / nonnegativity of `g`.
  have hmono_meas : Measurable mono := by rw [hmonodef]; unfold jacWeight; fun_prop
  have hg_meas : Measurable g := by
    rw [hgdef, hsosdef]; exact hmono_meas.mul (by fun_prop)
  have hmono_nonneg : ∀ u, 0 ≤ mono u := fun u ↦ by
    rw [hmonodef]
    exact mul_nonneg (Finset.prod_nonneg fun d _ ↦ pow_nonneg (abs_nonneg _) _)
      (Real.rpow_nonneg (sq_nonneg _) _)
  have hg_nonneg : ∀ u, 0 ≤ g u := fun u ↦ by
    rw [hgdef]
    exact mul_nonneg (hmono_nonneg u)
      (Real.rpow_nonneg (Finset.sum_nonneg fun j _ ↦ sq_nonneg _) _)
  -- coordinate hyperplanes are null, so `mono` factors into a pure `rpow`-product a.e.
  have hnull : ∀ d : Fin D, volume {u : Fin D → ℝ | u d = 0} = 0 := by
    intro d
    have hset : {u : Fin D → ℝ | u d = 0}
        = Set.univ.pi (fun i ↦ if i = d then ({0} : Set ℝ) else Set.univ) := by
      ext u
      simp only [Set.mem_setOf_eq, Set.mem_pi, Set.mem_univ, true_implies]
      constructor
      · intro hud i; split_ifs with hi
        · rw [hi]; exact hud
        · trivial
      · intro hall; have := hall d; simpa using this
    rw [hset, volume_pi_pi]
    exact Finset.prod_eq_zero (Finset.mem_univ d) (by simp)
  have hae_nonzero : ∀ᵐ u : Fin D → ℝ, ∀ d, u d ≠ 0 := by
    rw [ae_all_iff]; intro d; rw [ae_iff]; simpa using hnull d
  have hfactor : ∀ u : Fin D → ℝ, (∀ d, u d ≠ 0) → mono u = ∏ d, |u d| ^ (ev d) := by
    intro u hu
    rw [hmonodef]; simp only [jacWeight, hev]
    rw [show ((∏ d, (u d) ^ (a d))) ^ 2 = ∏ d, |u d| ^ (2 * a d) from ?_]
    · rw [← Real.finset_prod_rpow _ _ (fun d _ ↦ pow_nonneg (abs_nonneg _) _) (-cc),
        ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl (fun d _ ↦ ?_)
      rw [← Real.rpow_natCast (|u d|) (jac d), ← Real.rpow_natCast (|u d|) (2 * a d),
        ← Real.rpow_mul (abs_nonneg _), ← Real.rpow_add (by rw [abs_pos]; exact hu d)]
      congr 1; push_cast; ring
    · rw [← Finset.prod_pow]
      refine Finset.prod_congr rfl (fun d _ ↦ ?_)
      rw [pow_right_comm, ← sq_abs, ← pow_mul]
  -- the a.e. disjoint-block factorization `g = H ∘ e`.
  have hg_ae : g =ᵐ[volume] (fun u ↦ H (e u)) := by
    filter_upwards [hae_nonzero] with u hu
    show mono u * (sos u) ^ (-cc) = Fsub ((e u).1) * Gsub ((e u).2)
    have hFs : Fsub ((e u).1) = (sos u) ^ (-cc) := by
      simp only [hFsubdef, hsosdef]
      congr 1
      simp_rw [he1]
      exact (Finset.sum_subtype Z (fun _ ↦ Iff.rfl) (fun j ↦ (u j) ^ 2)).symm
    have hGs : Gsub ((e u).2) = mono u := by
      rw [hfactor u hu, hGsubdef]
      simp_rw [he2]
      rw [← Fintype.prod_subtype_mul_prod_subtype (· ∈ Z) (fun d ↦ |u d| ^ (ev d))]
      have hZ1 : ∀ i : {x // x ∈ Z}, |u ↑i| ^ (ev ↑i) = 1 :=
        fun i ↦ by rw [hevZ ↑i i.2, Real.rpow_zero]
      simp only [hZ1, Finset.prod_const_one, one_mul]
    rw [hFs, hGs]; ring
  -- the origin-centred symmetric box containing `p`.
  set R : ℝ := (∑ d, |p d|) + 1 with hRdef
  have hR : 0 < R := by
    have : (0 : ℝ) ≤ ∑ d, |p d| := Finset.sum_nonneg (fun d _ ↦ abs_nonneg _)
    rw [hRdef]; linarith
  have hpR : ∀ d, |p d| < R := by
    intro d
    have hle : |p d| ≤ ∑ d, |p d| :=
      Finset.single_le_sum (f := fun d ↦ |p d|) (fun i _ ↦ abs_nonneg _) (Finset.mem_univ d)
    rw [hRdef]; linarith
  set box : Set (Fin D → ℝ) := Set.univ.pi (fun _ : Fin D ↦ Set.Ioo (-R) R) with hboxdef
  set boxZ : Set ({i // i ∈ Z} → ℝ) := Set.univ.pi (fun _ ↦ Set.Ioo (-R) R) with hboxZdef
  set boxC : Set ({i // ¬ i ∈ Z} → ℝ) := Set.univ.pi (fun _ ↦ Set.Ioo (-R) R) with hboxCdef
  have hbox_mem : box ∈ 𝓝 p := by
    refine IsOpen.mem_nhds (isOpen_set_pi Set.finite_univ (fun _ _ ↦ isOpen_Ioo)) ?_
    simp only [hboxdef, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Ioo]
    intro d; have := hpR d; rw [abs_lt] at this; exact ⟨this.1, this.2⟩
  -- the two Tonelli factors are integrable on their boxes.
  haveI hZnesub : Nonempty {i // i ∈ Z} := by obtain ⟨j, hj⟩ := hZne; exact ⟨⟨j, hj⟩⟩
  have hcardN : Fintype.card {i // i ∈ Z} = Z.card := by
    rw [Fintype.card_subtype]; exact congrArg Finset.card (Finset.filter_univ_mem Z)
  have hF : IntegrableOn Fsub boxZ volume := by
    rw [hFsubdef, hboxZdef]
    refine boxSumSqNegPow_integrableOn hR hc0 ?_
    rw [hcardN]; exact hsos
  have hG_int : IntegrableOn Gsub boxC volume := by
    rw [hGsubdef, hboxCdef]
    refine ⟨(by fun_prop : Measurable (fun w : {i // ¬ i ∈ Z} → ℝ ↦
      ∏ d, |w d| ^ (ev ↑d))).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal
      (ae_of_all _ (fun w ↦ Finset.prod_nonneg fun d _ ↦ Real.rpow_nonneg (abs_nonneg _) _))]
    exact boxProdRpow_lintegral_lt_top (ι := {i // ¬ i ∈ Z}) hR (fun d ↦ ev ↑d) (fun d ↦ hβ ↑d)
  -- combine over the product measure, transport back to the `p`-box.
  have hmp := measurePreserving_piEquivPiSubtypeProd (fun _ : Fin D ↦ (volume : Measure ℝ)) (· ∈ Z)
  have hpre2 : e ⁻¹' (boxZ ×ˢ boxC) = box := by
    ext u
    simp only [hboxdef, hboxZdef, hboxCdef, Set.mem_preimage, Set.mem_prod, Set.mem_pi,
      Set.mem_univ, true_implies, he1, he2]
    constructor
    · rintro ⟨h1, h2⟩ d
      by_cases hd : d ∈ Z
      · exact h1 ⟨d, hd⟩
      · exact h2 ⟨d, hd⟩
    · intro hall
      exact ⟨fun i ↦ hall ↑i, fun i ↦ hall ↑i⟩
  have hg_box : IntegrableOn g box volume := by
    have hmodel : IntegrableOn (H ∘ e) box
        (Measure.pi (fun _ : Fin D ↦ (volume : Measure ℝ))) := by
      rw [← hpre2]
      refine (hmp.integrableOn_comp_preimage e.measurableEmbedding (f := H)
        (s := boxZ ×ˢ boxC)).mpr ?_
      rw [IntegrableOn, ← Measure.prod_restrict, hHdef]
      exact hF.mul_prod hG_int
    exact hmodel.congr (Filter.EventuallyEq.restrict hg_ae.symm)
  -- bound `|unit|` near `p`; pick a ball `B ⊆ box ∩ {W-model} ∩ {|unit|<Mub}`.
  set Mub : ℝ := |unit p| + 1 with hMubdef
  have hunitabs_cont : ContinuousAt (fun u ↦ |unit u|) p :=
    continuous_abs.continuousAt.comp hunit
  have hVub : ∀ᶠ u in 𝓝 p, |unit u| < Mub := by
    filter_upwards [hunitabs_cont.eventually (Iio_mem_nhds (lt_add_one _))]
      with u hu using Set.mem_Iio.mp hu
  obtain ⟨ε₀, hε₀, hε₀sub⟩ :=
    Metric.mem_nhds_iff.1 (Filter.inter_mem hbox_mem (Filter.inter_mem hW hVub))
  set B := Metric.ball p ε₀ with hBdef
  have hBmeas : MeasurableSet B := measurableSet_ball
  have hg_intB : IntegrableOn g B := hg_box.mono_set (fun u hu ↦ (hε₀sub hu).1)
  -- the actual integrand equals `g · unit` on `B`, dominated by `Mub · g`.
  have hival : ∀ u ∈ B, W u * negPow (monoSumSqGerm a Z) cc u = g u * unit u := by
    intro u hu
    rw [(hε₀sub hu).2.1, negPow_apply, monoSumSqGerm,
      Real.mul_rpow (sq_nonneg _) (Finset.sum_nonneg fun j _ ↦ sq_nonneg _),
      hgdef, hmonodef, hsosdef]
    ring
  refine ⟨B, Metric.ball_mem_nhds p hε₀, ?_⟩
  refine (hg_intB.const_mul Mub).mono' ?_ ?_
  · have haem : (fun u ↦ W u * negPow (monoSumSqGerm a Z) cc u)
        =ᵐ[volume.restrict B] (fun u ↦ g u * unit u) :=
      (ae_restrict_iff' hBmeas).mpr (ae_of_all _ (fun u hu ↦ hival u hu))
    exact (hg_meas.mul hunitmeas).aestronglyMeasurable.congr haem.symm
  · refine (ae_restrict_iff' hBmeas).mpr (ae_of_all _ (fun u hu ↦ ?_))
    rw [Real.norm_eq_abs, hival u hu, abs_mul, abs_of_nonneg (hg_nonneg u)]
    calc g u * |unit u| ≤ g u * Mub :=
          mul_le_mul_of_nonneg_left (le_of_lt (hε₀sub hu).2.2) (hg_nonneg u)
      _ = Mub * g u := by ring

end DLNFibre.Core.Aoyagi
