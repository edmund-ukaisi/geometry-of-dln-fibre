import DLNFibre.DLN.RLCT.Foundations.Rlct
import DLNFibre.DLN.RLCT.Foundations.S1Fubini
import Mathlib.MeasureTheory.Measure.Prod

/-!
# `DLNFibre.DLN.RLCT.Foundations.S1ProductMin` — the product-MIN RLCT lemma

For a loss that factors as `F(x,y) = G(x)·H(y)` over disjoint variable blocks, the RLCT is the
**minimum** of the block RLCTs: `rlctAtOn (G·H) (0,0) = min (rlctAtOn G 0) (rlctAtOn H 0)`. The L2
ladder consumes this for the (2,1,2) headline (`‖AB‖² = (a₁²+a₂²)(b₁²+b₂²)`, block×block) and the
(2,2,2) δ-leaf (monomial×block) — one lemma, both cases (pp's unification).

## Why MIN (not SUM) — the load-bearing distinction
The threshold integrand splits: `∫⁻_{U×V} |G·H|^{−c} = (∫⁻_U |G|^{−c})·(∫⁻_V |H|^{−c})`
(`lintegral_prod_mul` after `mul_rpow`). Over `ℝ≥0∞` the product is finite iff **both** factors are
finite — i.e. `c < rlctAtOn G ∧ c < rlctAtOn H` — so `sSup{adm} = min`. (Contrast S1.5's `F²+G²`
SUM ⟹ ADD; a `F·G` PRODUCT ⟹ MIN.)

## The 0·∞ positivity care (load-bearing)
"product finite ⟺ both finite" is FALSE in `ℝ≥0∞` when a factor is `0` (`0·∞ = 0 < ⊤`). The `≤`
direction needs the OTHER factor's integral strictly positive. The lemma carries this as the
`hGpos`/`hHpos` hypotheses (`0 < ∫⁻ G^{−c}` on open nbhds) — discharged at the use-site from `G ≠ 0`
a.e. (monomial zero-set = null hyperplanes; block = `{0}`; via `setLIntegral_pos_iff`).
The `≥` direction takes the per-factor down-set extractors `hdown`/`hdownH` (discharged from
`core_admissible_of_lt`). Stated over a product `X × Y` of `[BorelSpace] [SecondCountableTopology]`
measure spaces (so `OpensMeasurableSpace (X × Y)` holds — true for the `Fin p → ℝ` flat factors).
-/

open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace DLNFibre.DLN.RLCT

variable {X Y : Type*} [MeasureSpace X] [MeasureSpace Y] [TopologicalSpace X] [TopologicalSpace Y]
    [SFinite (volume : Measure X)] [SFinite (volume : Measure Y)] [Zero X] [Zero Y]
    [BorelSpace X] [BorelSpace Y] [SecondCountableTopology X] [SecondCountableTopology Y]

omit [TopologicalSpace X] [Zero X] [BorelSpace X] [SecondCountableTopology X]
    [SFinite (volume : Measure X)] in
private theorem intOn_iff_lt (f : X → ℝ) (hf : Measurable f) (hfnn : ∀ x, 0 ≤ f x) (U : Set X) :
    IntegrableOn f U volume ↔ ∫⁻ x in U, ENNReal.ofReal (f x) < ⊤ := by
  rw [IntegrableOn, Integrable, hasFiniteIntegral_iff_ofReal (ae_of_all _ hfnn)]
  simp only [hf.aestronglyMeasurable, true_and]

omit [TopologicalSpace X] [TopologicalSpace Y] [Zero X] [Zero Y] [BorelSpace X] [BorelSpace Y]
    [SecondCountableTopology X] [SecondCountableTopology Y] in
private theorem rect_split (G : X → ℝ) (H : Y → ℝ) (hGm : Measurable G) (hHm : Measurable H)
    (c : ℝ) (U : Set X) (V : Set Y) :
    ∫⁻ p in U ×ˢ V, ENNReal.ofReal (|G p.1 * H p.2| ^ (-c))
      = (∫⁻ x in U, ENNReal.ofReal (|G x| ^ (-c)))
        * (∫⁻ y in V, ENNReal.ofReal (|H y| ^ (-c))) := by
  have hsplit : (fun p : X × Y => ENNReal.ofReal (|G p.1 * H p.2| ^ (-c)))
      = (fun p => ENNReal.ofReal (|G p.1| ^ (-c)) * ENNReal.ofReal (|H p.2| ^ (-c))) := by
    funext p; rw [← ENNReal.ofReal_mul (Real.rpow_nonneg (abs_nonneg _) _)]
    congr 1; rw [abs_mul, Real.mul_rpow (abs_nonneg _) (abs_nonneg _)]
  rw [hsplit, Measure.volume_eq_prod, ← Measure.prod_restrict]
  exact lintegral_prod_mul
    ((by fun_prop : Measurable (fun x : X => ENNReal.ofReal (|G x| ^ (-c)))).aemeasurable)
    ((by fun_prop : Measurable (fun y : Y => ENNReal.ofReal (|H y| ^ (-c)))).aemeasurable)

omit [TopologicalSpace X] [Zero X] [BorelSpace X] [SecondCountableTopology X]
    [SFinite (volume : Measure X)] in
private theorem absrpow_meas (G : X → ℝ) (hGm : Measurable G) (c : ℝ) :
    Measurable (fun x => |G x| ^ (-c)) := by fun_prop

-- the ≤ direction (one side): rlctAtOn F (0,0) ≤ rlctAtOn G 0, given H-positivity.
-- jointAdm c' ⟹ rectangle U×ˢV ⊆ Ω finite ⟹ (split) (∫⁻_U G^{-c'})·(∫⁻_V H^{-c'}) < ⊤
--   ⟹ [H-factor > 0] ∫⁻_U G^{-c'} < ⊤ ⟹ G-adm c'.
omit [SecondCountableTopology X] in
private theorem pmr_le_left (G : X → ℝ) (H : Y → ℝ) (hGm : Measurable G) (hHm : Measurable H)
    (hHpos : ∀ (c' : ℝ) (V : Set Y), IsOpen V → (0:Y) ∈ V →
      0 < ∫⁻ y in V, ENNReal.ofReal (|H y| ^ (-c'))) :
    rlctAtOn (fun p : X × Y => G p.1 * H p.2) (0, 0) ≤ rlctAtOn G 0 := by
  unfold rlctAtOn weightedThreshold
  apply sSup_le_sSup
  rintro c ⟨c', rfl, Ω, hΩopen, hmem, hint⟩
  obtain ⟨U, V, hUopen, hVopen, h0U, h0V, hsub⟩ := isOpen_prod_iff.1 hΩopen 0 0 (hmem rfl)
  refine ⟨c', rfl, U, hUopen, Set.singleton_subset_iff.2 h0U, ?_⟩
  -- joint integrable on Ω ⟹ on U×ˢV (mono) ⟹ split finite ⟹ G-factor finite
  have hjoint_int : IntegrableOn (fun p : X × Y => |G p.1 * H p.2| ^ (-(c':ℝ)) * (fun _ => (1:ℝ)) p)
      (U ×ˢ V) volume := hint.mono_set (by intro p hp; exact hsub ⟨hp.1, hp.2⟩)
  have hjoint_lt : ∫⁻ p in U ×ˢ V, ENNReal.ofReal (|G p.1 * H p.2| ^ (-(c':ℝ))) < ⊤ := by
    have hjm : Measurable (fun p : X × Y => |G p.1 * H p.2| ^ (-(c':ℝ))) := by
      have : Measurable (fun p : X × Y => G p.1 * H p.2) :=
        (hGm.comp measurable_fst).mul (hHm.comp measurable_snd)
      fun_prop
    rw [← intOn_iff_lt _ hjm (fun p => Real.rpow_nonneg (abs_nonneg _) _) (U ×ˢ V)]
    exact hjoint_int.congr_fun (fun p _ => by rw [mul_one]) (hUopen.prod hVopen).measurableSet
  rw [rect_split G H hGm hHm c' U V] at hjoint_lt
  -- (∫⁻_U)(∫⁻_V) < ⊤, ∫⁻_V > 0 ⟹ ∫⁻_U < ⊤
  have hVpos := hHpos (c':ℝ) V hVopen h0V
  have hUlt : ∫⁻ x in U, ENNReal.ofReal (|G x| ^ (-(c':ℝ))) < ⊤ := by
    rw [ENNReal.mul_lt_top_iff] at hjoint_lt
    rcases hjoint_lt with ⟨h1, _⟩ | h1 | h2
    · exact h1
    · rw [h1]; exact ENNReal.zero_lt_top
    · exact absurd h2 hVpos.ne'
  -- G-adm: IntegrableOn |G|^{-c'}·1 U ; drop the ·1, use hUlt via intOn_iff_lt
  have hGint : IntegrableOn (fun x => |G x|^(-(c':ℝ))) U volume :=
    (intOn_iff_lt _ (by fun_prop) (fun x => Real.rpow_nonneg (abs_nonneg _) _) U).mpr hUlt
  exact hGint.congr_fun (fun x _ => by rw [mul_one]) hUopen.measurableSet

-- mirror: rlctAtOn F (0,0) ≤ rlctAtOn H 0, via G-positivity.
omit [SecondCountableTopology X] in
private theorem pmr_le_right (G : X → ℝ) (H : Y → ℝ) (hGm : Measurable G) (hHm : Measurable H)
    (hGpos : ∀ (c' : ℝ) (U : Set X), IsOpen U → (0:X) ∈ U →
      0 < ∫⁻ x in U, ENNReal.ofReal (|G x| ^ (-c'))) :
    rlctAtOn (fun p : X × Y => G p.1 * H p.2) (0, 0) ≤ rlctAtOn H 0 := by
  unfold rlctAtOn weightedThreshold
  apply sSup_le_sSup
  rintro c ⟨c', rfl, Ω, hΩopen, hmem, hint⟩
  obtain ⟨U, V, hUopen, hVopen, h0U, h0V, hsub⟩ := isOpen_prod_iff.1 hΩopen 0 0 (hmem rfl)
  refine ⟨c', rfl, V, hVopen, Set.singleton_subset_iff.2 h0V, ?_⟩
  have hjoint_int : IntegrableOn (fun p : X × Y => |G p.1 * H p.2| ^ (-(c':ℝ)) * (fun _ => (1:ℝ)) p)
      (U ×ˢ V) volume := hint.mono_set (by intro p hp; exact hsub ⟨hp.1, hp.2⟩)
  have hjoint_lt : ∫⁻ p in U ×ˢ V, ENNReal.ofReal (|G p.1 * H p.2| ^ (-(c':ℝ))) < ⊤ := by
    have hjm : Measurable (fun p : X × Y => |G p.1 * H p.2| ^ (-(c':ℝ))) := by
      have : Measurable (fun p : X × Y => G p.1 * H p.2) :=
        (hGm.comp measurable_fst).mul (hHm.comp measurable_snd)
      fun_prop
    rw [← intOn_iff_lt _ hjm (fun p => Real.rpow_nonneg (abs_nonneg _) _) (U ×ˢ V)]
    exact hjoint_int.congr_fun (fun p _ => by rw [mul_one]) (hUopen.prod hVopen).measurableSet
  rw [rect_split G H hGm hHm c' U V] at hjoint_lt
  have hUpos := hGpos (c':ℝ) U hUopen h0U
  have hVlt : ∫⁻ y in V, ENNReal.ofReal (|H y| ^ (-(c':ℝ))) < ⊤ := by
    rw [ENNReal.mul_lt_top_iff] at hjoint_lt
    rcases hjoint_lt with ⟨_, h2⟩ | h1 | h2
    · exact h2
    · exact absurd h1 hUpos.ne'
    · rw [h2]; exact ENNReal.zero_lt_top
  have hHint : IntegrableOn (fun y => |H y|^(-(c':ℝ))) V volume :=
    (intOn_iff_lt _ (by fun_prop) (fun y => Real.rpow_nonneg (abs_nonneg _) _) V).mpr hVlt
  exact hHint.congr_fun (fun y _ => by rw [mul_one]) hVopen.measurableSet

-- ≥ direction: min(rlctAtOn G, rlctAtOn H) ≤ rlctAtOn F.
-- for q < min: q < rlctAtOn G ⟹ G-adm (down-set), q < rlctAtOn H ⟹ H-adm; product finite ⟹
-- joint-adm.
-- need a down-set extractor: q < rlctAtOn G 0 (q:NNReal) ⟹ ∃ U open ∋0, IntegrableOn |G|^{-q} U.
-- (admissible down-set: smaller exponent stays integrable on a bounded nbhd) — reuse structure.
-- For the ≥ direction I use the lt_sSup extraction directly (q < sSup ⟹ ∃ adm d ≥ q ⟹ q adm by
-- down-set).
-- This needs a per-factor down-set; given session scope, state the ≥ via the GAdm/HAdm sets
-- directly.
omit [BorelSpace X] [BorelSpace Y] [SecondCountableTopology X] [SecondCountableTopology Y] in
private theorem pmr_ge (G : X → ℝ) (H : Y → ℝ) (hGm : Measurable G) (hHm : Measurable H)
    (hdown : ∀ (q : NNReal), (q:ℝ≥0∞) < rlctAtOn G 0 →
      ∃ U : Set X, IsOpen U ∧ (0:X) ∈ U ∧ IntegrableOn (fun x => |G x| ^ (-(q : ℝ))) U volume)
    (hdownH : ∀ (q : NNReal), (q:ℝ≥0∞) < rlctAtOn H 0 →
      ∃ V : Set Y, IsOpen V ∧ (0:Y) ∈ V ∧ IntegrableOn (fun y => |H y| ^ (-(q : ℝ))) V volume) :
    min (rlctAtOn G 0) (rlctAtOn H 0) ≤ rlctAtOn (fun p : X × Y => G p.1 * H p.2) (0,0) := by
  apply le_of_forall_lt_imp_le_of_dense
  intro q hq
  rw [lt_min_iff] at hq
  obtain ⟨hqG, hqH⟩ := hq
  have hqfin : q ≠ ⊤ := hqG.ne_top
  set q' := q.toNNReal with hq'
  have hq'e : (q' : ℝ≥0∞) = q := ENNReal.coe_toNNReal hqfin
  obtain ⟨U, hUopen, h0U, hUint⟩ := hdown q' (hq'e ▸ hqG)
  obtain ⟨V, hVopen, h0V, hVint⟩ := hdownH q' (hq'e ▸ hqH)
  -- joint integrable on U×ˢV: split = (∫⁻_U)·(∫⁻_V), both finite
  apply le_sSup
  refine ⟨q', hq'e.symm, U ×ˢ V, hUopen.prod hVopen, Set.singleton_subset_iff.2 ⟨h0U, h0V⟩, ?_⟩
  have hUlt := (intOn_iff_lt _ (by fun_prop)
    (fun x => Real.rpow_nonneg (abs_nonneg _) _) U).mp hUint
  have hVlt := (intOn_iff_lt _ (by fun_prop)
    (fun y => Real.rpow_nonneg (abs_nonneg _) _) V).mp hVint
  have hjm : Measurable (fun p : X × Y => |G p.1 * H p.2| ^ (-(q':ℝ))) := by
    have : Measurable (fun p : X × Y => G p.1 * H p.2) :=
      (hGm.comp measurable_fst).mul (hHm.comp measurable_snd)
    fun_prop
  refine (intOn_iff_lt (fun p => |G p.1 * H p.2|^(-(q':ℝ)) * (fun _ => (1:ℝ)) p)
    (by fun_prop) (fun p => by positivity) (U ×ˢ V)).mpr ?_
  simp only [mul_one]
  rw [rect_split G H hGm hHm (q':ℝ) U V]
  exact ENNReal.mul_lt_top hUlt hVlt

-- main: product_min_rlct via le_antisymm. Takes the directly-usable hyps (caller derives from
-- hGne):
-- hGpos/hHpos (positivity on open nbhds) for ≤; hdown/hdownH (down-set extractors) for ≥.
omit [SecondCountableTopology X] in
theorem product_min_rlct (G : X → ℝ) (H : Y → ℝ) (hGm : Measurable G) (hHm : Measurable H)
    (hGpos : ∀ (c' : ℝ) (U : Set X), IsOpen U → (0:X) ∈ U →
      0 < ∫⁻ x in U, ENNReal.ofReal (|G x| ^ (-c')))
    (hHpos : ∀ (c' : ℝ) (V : Set Y), IsOpen V → (0:Y) ∈ V →
      0 < ∫⁻ y in V, ENNReal.ofReal (|H y| ^ (-c')))
    (hdown : ∀ (q : NNReal), (q:ℝ≥0∞) < rlctAtOn G 0 →
      ∃ U : Set X, IsOpen U ∧ (0:X) ∈ U ∧ IntegrableOn (fun x => |G x| ^ (-(q : ℝ))) U volume)
    (hdownH : ∀ (q : NNReal), (q:ℝ≥0∞) < rlctAtOn H 0 →
      ∃ V : Set Y, IsOpen V ∧ (0:Y) ∈ V ∧ IntegrableOn (fun y => |H y| ^ (-(q : ℝ))) V volume) :
    rlctAtOn (fun p : X × Y => G p.1 * H p.2) (0,0)
      = min (rlctAtOn G 0) (rlctAtOn H 0) := by
  apply le_antisymm
  · apply le_min (pmr_le_left G H hGm hHm hHpos)
    exact pmr_le_right G H hGm hHm hGpos
  · exact pmr_ge G H hGm hHm hdown hdownH

/-! ## The FINAL-form corollary — `product_min_rlct_of_ne` (`hGne`/`hHne` guards)

The agreed call-site interface (the (2,1,2) hand-off card, FINAL form): take the a.e.-nonvanishing
guards `hGne : G ≠ 0 a.e.` / `hHne : H ≠ 0 a.e.` directly and discharge the four core hypotheses of
`product_min_rlct` internally. ONE lemma covers block×block (2,1,2), monomial×block (δ-leaf),
monomial×monomial — `hGne` is `≠0 a.e.`, true for both consumers (block zero-set `{0}` null;
monomial zero-set = coordinate hyperplanes null).

- `hGpos`/`hHpos` (positivity) ← `hGne` + `IsOpen.measure_pos`: on open `U ∋ 0`,
  `support (ofReal |G|^{−c'}) ⊇ {G ≠ 0}` (positive-base rpow is positive), `{G = 0}` null, so
  `μ(support ∩ U) ≥ μ U > 0` (`setLIntegral_pos_iff`).
- `hdown`/`hdownH` (down-set extractors) ← `core_admissible_of_lt` (S1Fubini), needing only
  measurability + the proper/locally-finite core instances (no nonvanishing hypothesis). -/

section OfNe

/-- **Positivity from a.e.-nonvanishing.** If `G ≠ 0 a.e.` and `U` is an open set containing `0`,
then `0 < ∫⁻_U |G|^{−c'}`. The other-factor positivity that discharges the `0·∞` corner of
`product_min_rlct` (`hGpos`/`hHpos`). -/
private theorem pos_of_ne_ae {A : Type*} [TopologicalSpace A] [MeasureSpace A]
    [BorelSpace A] [MeasureTheory.Measure.IsOpenPosMeasure (volume : Measure A)] [Zero A]
    (G : A → ℝ) (hGm : Measurable G)
    (hGne : ∀ᵐ x ∂(volume : Measure A), G x ≠ 0)
    (c' : ℝ) (U : Set A) (hU : IsOpen U) (h0 : (0 : A) ∈ U) :
    0 < ∫⁻ x in U, ENNReal.ofReal (|G x| ^ (-c')) := by
  set f : A → ℝ≥0∞ := fun x => ENNReal.ofReal (|G x| ^ (-c')) with hf
  have hfmeas : Measurable f := by fun_prop
  rw [setLIntegral_pos_iff hfmeas]
  -- {G ≠ 0} ⊆ support f : positive base ⟹ positive rpow ⟹ ofReal positive
  have hsub : {x : A | G x ≠ 0} ⊆ Function.support f := by
    intro x hx
    have hpos : 0 < |G x| := abs_pos.2 hx
    have hxp : 0 < |G x| ^ (-c') := Real.rpow_pos_of_pos hpos _
    simp only [Function.mem_support, hf, ne_eq, ENNReal.ofReal_eq_zero, not_le]
    exact hxp
  -- {G = 0} is null ⟹ μ(U) ≤ μ({G≠0} ∩ U)
  have hnull : (volume : Measure A) {x | G x = 0} = 0 := by
    rw [show {x : A | G x = 0} = {x : A | G x ≠ 0}ᶜ by ext x; simp]
    exact (MeasureTheory.ae_iff.1 hGne)
  have hUle : (volume : Measure A) U ≤ volume ({x | G x ≠ 0} ∩ U) := by
    have hsplit : U ⊆ ({x | G x ≠ 0} ∩ U) ∪ ({x | G x = 0} ∩ U) := by
      intro x hx; by_cases hg : G x = 0
      · exact Or.inr ⟨hg, hx⟩
      · exact Or.inl ⟨hg, hx⟩
    calc (volume : Measure A) U
        ≤ volume (({x | G x ≠ 0} ∩ U) ∪ ({x | G x = 0} ∩ U)) := measure_mono hsplit
      _ ≤ volume ({x | G x ≠ 0} ∩ U) + volume ({x | G x = 0} ∩ U) := measure_union_le _ _
      _ = volume ({x | G x ≠ 0} ∩ U) :=
          by rw [measure_inter_null_of_null_left U hnull, add_zero]
  calc (0 : ℝ≥0∞) < volume U := hU.measure_pos _ ⟨0, h0⟩
    _ ≤ volume ({x | G x ≠ 0} ∩ U) := hUle
    _ ≤ volume (Function.support f ∩ U) := measure_mono (Set.inter_subset_inter_left U hsub)

/-- **`product_min_rlct`, FINAL form.** For `G : A → ℝ`, `H : B → ℝ` measurable and
a.e.-nonvanishing,
`rlctAtOn (G·H) (0,0) = min (rlctAtOn G 0) (rlctAtOn H 0)`. The single call-site interface for the
(2,1,2) headline and the (2,2,2) δ-leaf — the four core hypotheses are discharged from `hGne`/`hHne`
(`pos_of_ne_ae`) and `core_admissible_of_lt` (down-set). The instances all hold for the consumers'
flat factors `Fin p → ℝ` / `EuclideanSpace ℝ (Fin n)`. -/
theorem product_min_rlct_of_ne
    {A B : Type*}
    [PseudoMetricSpace A] [MeasureSpace A] [ProperSpace A]
    [IsFiniteMeasureOnCompacts (volume : Measure A)]
    [MeasureTheory.Measure.IsOpenPosMeasure (volume : Measure A)]
    [SFinite (volume : Measure A)] [Zero A] [BorelSpace A] [SecondCountableTopology A]
    [PseudoMetricSpace B] [MeasureSpace B] [ProperSpace B]
    [IsFiniteMeasureOnCompacts (volume : Measure B)]
    [MeasureTheory.Measure.IsOpenPosMeasure (volume : Measure B)]
    [SFinite (volume : Measure B)] [Zero B] [BorelSpace B] [SecondCountableTopology B]
    (G : A → ℝ) (H : B → ℝ) (hGm : Measurable G) (hHm : Measurable H)
    (hGne : ∀ᵐ x ∂(volume : Measure A), G x ≠ 0)
    (hHne : ∀ᵐ y ∂(volume : Measure B), H y ≠ 0) :
    rlctAtOn (fun p : A × B => G p.1 * H p.2) (0, 0)
      = min (rlctAtOn G 0) (rlctAtOn H 0) := by
  apply product_min_rlct G H hGm hHm
  · exact fun c' U hU h0 => pos_of_ne_ae G hGm hGne c' U hU h0
  · exact fun c' V hV h0 => pos_of_ne_ae H hHm hHne c' V hV h0
  · exact fun q hq => core_admissible_of_lt G hGm 0 q hq
  · exact fun q hq => core_admissible_of_lt H hHm 0 q hq

end OfNe

end DLNFibre.DLN.RLCT

