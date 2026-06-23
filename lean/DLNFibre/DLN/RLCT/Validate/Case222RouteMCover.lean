import DLNFibre.DLN.RLCT.Validate.RouteMCoverLemmas
import DLNFibre.DLN.RLCT.Validate.Case222CoverGETail

/-!
# `DLNFibre.DLN.RLCT.Validate.Case222RouteMCover` — the `(2,2,2)` cover facts (fm3)

The CONCRETE `(2,2,2)` discharge of the two `IsRouteMCover` integral facts (`cover_le` / `cover_ge_div`)
+ `Fmeas` / `Uopen` / `Umem`, as STANDALONE theorems over the geometric data `F = myF222`,
`U = openBox = (−1,1)^8`, and the single binding-leaf family `(d, k, h) = (8, unitK8, unitH8)`
(threshold `3/2`). These are exactly the `IsRouteMCover` field shapes; crux2 packages them into the
`IsRouteMCover myF222 openBox (Fin 1 / Unit) …` instance on `route-m-atlas` (`IsRouteMCover` is defined
there, not here — single-writer; this file delivers the facts it consumes).

The two analytic facts reduce, via the abstract `RouteMCoverLemmas`, to BANKED `(2,2,2)` atoms:
- `cover_le` ← `routeM_coverLe_of_finiteness` + `myF222_threshold_lt_top'` (below-threshold finiteness)
  + the single-leaf RHS positivity.
- `cover_ge_div` ← `routeM_coverGeDiv_of_boxDiverges` + the `(2,2,2)` box divergence (the content of
  `rlctAtOn_myF222_le`'s `≤`-leg, at-and-above the threshold).

`myF222` is the flat `(2,2,2)` core; here `F = myF222` throughout (these facts say NOTHING about
`dlnLoss H222 0` directly). The seam to the network loss is NOT a bare equality: `dlnLoss222_eq_myF222`
(`Case222Algebra`) proves `dlnLoss H222 0 = myF222 ∘ e222`, i.e. `myF222` precomposed with a coordinate
REINDEX `e222` (a measure-preserving linear change). So lifting these `myF222`-cover facts to a
`dlnLoss H222 0` RLCT statement requires transporting across `e222` (`rlctAtOn_dlnLoss222_transport`,
banked) — the `e222` reindex must stay explicit in that chain, not be elided. The cover facts here are
honestly scoped to the flat core; the `e222`-transport to the network loss is the consumer's
(crux2's) step.
-/

open MeasureTheory
open scoped BigOperators ENNReal
namespace DLNFibre.DLN.RLCT

/-- The `(2,2,2)` binding-leaf family: a single leaf (`Fin 1`), dimension `8`, exponents
`(unitK8, unitH8) = (![1,0,1,0,…], ![3,0,2,0,…])`, threshold `monomialThreshold 8 unitK8 unitH8 = 3/2`
(`unitMonomialThreshold_ge` / `_le`). This is the `(2,2,2)` cover's binding leaf (the `phiUnit` chart). -/
def routeM222D : Fin 1 → ℕ := fun _ => 8
/-- The `(2,2,2)` binding-leaf loss exponents. -/
def routeM222K : (i : Fin 1) → Fin (routeM222D i) → ℕ := fun _ => unitK8
/-- The `(2,2,2)` binding-leaf Jacobian exponents. -/
def routeM222H : (i : Fin 1) → Fin (routeM222D i) → ℕ := fun _ => unitH8

/-- `monomialThreshold` of the single `(2,2,2)` leaf is `3/2` (`le_antisymm` of the banked halves). -/
theorem routeM222_leaf_threshold (i : Fin 1) :
    monomialThreshold (routeM222D i) (routeM222K i) (routeM222H i) = 3 / 2 :=
  le_antisymm unitMonomialThreshold_le unitMonomialThreshold_ge

/-- The `⨅` over the single-leaf family is `3/2` (`iInf` over `Fin 1` collapses). -/
theorem routeM222_iInf_threshold :
    (⨅ i : Fin 1, monomialThreshold (routeM222D i) (routeM222K i) (routeM222H i)) = 3 / 2 := by
  rw [iInf_unique]
  exact routeM222_leaf_threshold default

/-- **`Fmeas`** : `myF222` is measurable (a polynomial flat core). -/
theorem routeM222_Fmeas : Measurable myF222 := by unfold myF222; fun_prop

/-- **`Uopen`** : the base nbhd `openBox = (−1,1)^8` is open. -/
theorem routeM222_Uopen : IsOpen openBox := isOpen_openBox

/-- **`Umem`** : `0 ∈ openBox`. -/
theorem routeM222_Umem : (0 : Fin 8 → ℝ) ∈ openBox := mem_openBox_zero

/-! ## The cover_le finiteness facts (the two `routeM_coverLe_of_finiteness` hypotheses) -/

/-- The single-leaf RHS sum is the `i = 0` leaf integral (the `Fin 1` sum collapses). -/
theorem routeM222_rhs_eq (c' : NNReal) :
    (∑ i : Fin 1, ∫⁻ y in unitBox (routeM222D i),
        ENNReal.ofReal (monomialIntegrand (routeM222D i) (routeM222K i) (routeM222H i) (c' : ℝ) y))
      = ∫⁻ y in unitBox 8, ENNReal.ofReal (monomialIntegrand 8 unitK8 unitH8 (c' : ℝ) y) := by
  rw [Fin.sum_univ_one]; rfl

/-- **(`hpos`) The single-leaf RHS is nonzero.** The integrand `monomialIntegrand 8 unitK8 unitH8 c'`
is `> 0` on the interior `(0,1)^8` (all `|uⱼ| > 0` ⟹ each monomial/`rpow` factor positive), a
positive-measure subset of `unitBox 8`, so the lintegral is `≠ 0` (`lintegral_eq_zero_iff` contrapositive
via the open interior). -/
theorem routeM222_rhs_ne_zero (c' : NNReal) :
    (∑ i : Fin 1, ∫⁻ y in unitBox (routeM222D i),
        ENNReal.ofReal (monomialIntegrand (routeM222D i) (routeM222K i) (routeM222H i) (c' : ℝ) y))
      ≠ 0 := by
  rw [routeM222_rhs_eq]
  set f := fun y => ENNReal.ofReal (monomialIntegrand 8 unitK8 unitH8 (c' : ℝ) y) with hf
  have hmeas : Measurable f := by
    rw [hf]; exact ENNReal.measurable_ofReal.comp (by unfold monomialIntegrand; fun_prop)
  -- positive on the interior box `S = (1/2,1)^8 ⊆ unitBox 8` (positive measure), so `∫⁻ > 0`.
  set S : Set (Fin 8 → ℝ) := Set.univ.pi (fun _ => Set.Ioo (1/2 : ℝ) 1) with hS
  have hSsub : S ⊆ unitBox 8 := fun x hx i _ => by
    have := hx i (Set.mem_univ i); simp only [Set.mem_Ioo] at this
    simp only [unitBox, Set.mem_Icc]; exact ⟨by linarith [this.1], by linarith [this.2]⟩
  have hSpos : 0 < volume S := by
    rw [hS, Real.volume_pi_Ioo]
    refine CanonicallyOrderedAdd.prod_pos.2 (fun _ _ => ?_)
    rw [ENNReal.ofReal_pos]; norm_num
  -- `f > 0` (support membership) on `S`
  have hsupp : S ⊆ Function.support f := by
    intro x hx
    rw [Function.mem_support, hf]
    simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    have hxpos : ∀ j, (0 : ℝ) < |x j| := by
      intro j
      have := hx j (Set.mem_univ j); simp only [Set.mem_Ioo] at this
      rw [abs_of_pos (by linarith [this.1])]; linarith [this.1]
    unfold monomialIntegrand
    exact mul_pos (Finset.prod_pos (fun j _ => pow_pos (hxpos j) _))
      (Real.rpow_pos_of_pos (Finset.prod_pos (fun j _ => pow_pos (hxpos j) _)) _)
  -- positive-measure `support ∩ unitBox`, so `∫⁻ > 0` ⟹ `≠ 0`
  rw [← pos_iff_ne_zero, setLIntegral_pos_iff hmeas]
  exact lt_of_lt_of_le hSpos (measure_mono (fun x hx => ⟨hsupp hx, hSsub hx⟩))

/-- **(`hfin`) Below-threshold finiteness.** If the single-leaf RHS is finite, then `c' < 3/2` (else the
RHS box integral is `⊤` by `monomialIntegrand_lintegral_box_eq_top`), and so `∫⁻_{openBox} |myF222|^{−c'}
< ⊤` (`myF222_threshold_lt_top'`). The contrapositive routes the divergence atom; `unitBox 8 = [0,1]^8`
matches the atom's box at `ε = 1`, and `ofReal (monomialIntegrand) = ofReal |monomialIntegrand|`
(`monomialIntegrand ≥ 0`). -/
theorem routeM222_below_threshold_fin (c' : NNReal)
    (hB : (∑ i : Fin 1, ∫⁻ y in unitBox (routeM222D i),
        ENNReal.ofReal (monomialIntegrand (routeM222D i) (routeM222K i) (routeM222H i) (c' : ℝ) y)) < ⊤) :
    ∫⁻ x in openBox, ENNReal.ofReal (|myF222 x| ^ (-(c' : ℝ))) < ⊤ := by
  -- first: `c' < 3/2` (else the RHS box integral is `⊤`).
  have hc'lt : (c' : ℝ) < 3 / 2 := by
    by_contra hge
    rw [not_lt] at hge
    have hc'0 : (0 : ℝ) < (c' : ℝ) := lt_of_lt_of_le (by norm_num) hge
    have h32 : (3 : ℝ≥0∞) / 2 ≤ ENNReal.ofReal (c' : ℝ) := by
      rw [show (3 : ℝ≥0∞) / 2 = ENNReal.ofReal (3 / 2) by
        rw [ENNReal.ofReal_div_of_pos (by norm_num)]; norm_num]
      exact ENNReal.ofReal_le_ofReal hge
    have hthr : monomialThreshold 8 unitK8 unitH8 ≤ ENNReal.ofReal (c' : ℝ) :=
      le_trans unitMonomialThreshold_le h32
    have htop := monomialIntegrand_lintegral_box_eq_top 8 unitK8 unitH8 ⟨2, unitK8_binding⟩
      (c' : ℝ) hthr hc'0 (show (0:ℝ) < 1 by norm_num)
    -- the atom's box `[0,1]^8` is `unitBox 8`; drop `|·|` (integrand ≥ 0)
    rw [routeM222_rhs_eq] at hB
    have hbox : ∫⁻ y in unitBox 8, ENNReal.ofReal (monomialIntegrand 8 unitK8 unitH8 (c' : ℝ) y) = ⊤ := by
      rw [show unitBox 8 = Set.univ.pi (fun _ : Fin 8 => Set.Icc (0 : ℝ) 1) from rfl]
      rw [← htop]
      refine setLIntegral_congr_fun (MeasurableSet.univ_pi (fun _ => measurableSet_Icc)) (fun y _ => ?_)
      rw [abs_of_nonneg (by unfold monomialIntegrand; positivity)]
    rw [hbox] at hB; exact absurd hB (lt_irrefl _)
  -- then: `myF222_threshold_lt_top'` gives the `openBox` finiteness.
  exact myF222_threshold_lt_top' c' hc'lt

/-- **`cover_le`** : the `(2,2,2)` cover_le field — `∀ c', ∃ C < ⊤, ∫⁻_{openBox} |myF222|^{−c'} ≤
C · Σ_leaf`. Via the abstract `routeM_coverLe_of_finiteness` + the single-leaf finiteness facts
(`routeM222_rhs_ne_zero`, `routeM222_below_threshold_fin`). -/
theorem routeM222_cover_le :
    ∀ c' : NNReal, ∃ C : ℝ≥0∞, C < ⊤ ∧
      ∫⁻ x in openBox, ENNReal.ofReal (|myF222 x| ^ (-(c' : ℝ)))
        ≤ C * ∑ i : Fin 1, ∫⁻ y in unitBox (routeM222D i),
            ENNReal.ofReal (monomialIntegrand (routeM222D i) (routeM222K i) (routeM222H i) (c' : ℝ) y) :=
  routeM_coverLe_of_finiteness myF222 openBox routeM222D routeM222K routeM222H
    routeM222_rhs_ne_zero (fun c' hB => routeM222_below_threshold_fin c' hB)

/-! ## The cover_ge_div divergence fact (the `routeM_coverGeDiv_of_boxDiverges` hypothesis) -/

/-- **The `(2,2,2)` `ε`-uniform box divergence (NON-strict, at-and-above threshold).** For `c'` with
`3/2 ≤ c'` (so `c' ≥ monomialThreshold`) and `0 < c'`, the `|myF222|^{−c'}` integral over every cube
`[−ε, ε]^8` is `⊤`. This is the `(2,2,2)` `≤`-direction analytic content (`rlctAtOn_myF222_le`'s calc),
hoisted to a standalone NON-strict lemma: dominate `[−ε,ε]^8` by the binding leaf chart's image
(`phiUnit_image_subset_cubeBox` + `lintegral_mono_set`), transport by the composite c-o-v (`phiUnit_cov`),
match the integrand (`myF222_phiUnit_leaf_integrand`, pivot loci dropped null via `coordZero_null`), and
diverge (`leaf_box_div`, whose threshold premise is non-strict). The endpoint `c' = 3/2` is included
(unlike the `> 3/2` `rlctAtOn_myF222_le`), as `cover_ge_div`'s `monomialThreshold ≤ c'` premise needs. -/
theorem routeM222_box_diverges (c' : NNReal) (hc' : monomialThreshold 8 unitK8 unitH8 ≤ (c' : ℝ≥0∞))
    (ε : ℝ) (hε : 0 < ε) :
    ∫⁻ x in cubeBox 8 ε, ENNReal.ofReal (|myF222 x| ^ (-(c' : ℝ))) = ⊤ := by
  -- `3/2 ≤ monomialThreshold ≤ c'` ⟹ `0 < c'` + the non-strict chart-threshold premise.
  have h32c' : (3 : ℝ≥0∞) / 2 ≤ (c' : ℝ≥0∞) := le_trans unitMonomialThreshold_ge hc'
  have hc'0 : (0 : ℝ) < (c' : ℝ) := by
    rw [show (3 : ℝ≥0∞) / 2 = ENNReal.ofReal (3 / 2) by
      rw [ENNReal.ofReal_div_of_pos (by norm_num)]; norm_num, ENNReal.ofReal_le_iff_le_toReal
      (by simp), ENNReal.coe_toReal] at h32c'
    linarith
  have hthr : monomialThreshold 8 unitK8 unitH8 ≤ ENNReal.ofReal (c' : ℝ) := by
    rw [ENNReal.ofReal_coe_nnreal]; exact hc'
  obtain ⟨δ, hδ, hsub⟩ := phiUnit_image_subset_cubeBox ε hε
  set P := Set.univ.pi (fun _ : Fin 8 => Set.Icc (0 : ℝ) δ) with hP
  have hPmeas : MeasurableSet P := MeasurableSet.univ_pi (fun _ => measurableSet_Icc)
  have hPsub : P ⊆ cubeBox 8 δ := fun x hx i _ => by
    have := hx i (Set.mem_univ i); simp only [Set.mem_Icc] at this ⊢
    exact ⟨by linarith [this.1], by linarith [this.2]⟩
  have hdiffnull : ∫⁻ x in (P \ {x | x 2 = 0}) \ {x | x 0 = 0},
        ENNReal.ofReal (|x 0| ^ 3 * |x 2| ^ 2) * ENNReal.ofReal (|myF222 (phiUnit x)| ^ (-(c' : ℝ)))
      = ∫⁻ x in P, ENNReal.ofReal (|x 0| ^ 3 * |x 2| ^ 2)
          * ENNReal.ofReal (|myF222 (phiUnit x)| ^ (-(c' : ℝ))) := by
    apply setLIntegral_congr
    rw [Set.diff_diff]
    exact MeasureTheory.diff_ae_eq_self.2 (measure_mono_null Set.inter_subset_right
      (by rw [measure_union_null_iff]; exact ⟨coordZero_null 2, coordZero_null 0⟩))
  apply top_le_iff.1
  calc (⊤ : ℝ≥0∞)
      = ∫⁻ u in P,
          ENNReal.ofReal (monomialIntegrand 8 unitK8 unitH8 (c' : ℝ) u * (Uval u) ^ (-(c' : ℝ))) :=
        (leaf_box_div (c' : ℝ) hc'0 hthr ⟨2, by decide⟩ δ hδ).symm
    _ = ∫⁻ u in P, ENNReal.ofReal (|u 0| ^ 3 * |u 2| ^ 2)
          * ENNReal.ofReal (|myF222 (phiUnit u)| ^ (-(c' : ℝ))) := by
        refine setLIntegral_congr_fun hPmeas (fun u _ => ?_)
        rw [← ENNReal.ofReal_mul (by positivity), myF222_phiUnit_leaf_integrand]
    _ = ∫⁻ x in (P \ {x | x 2 = 0}) \ {x | x 0 = 0},
          ENNReal.ofReal (|x 0| ^ 3 * |x 2| ^ 2)
            * ENNReal.ofReal (|myF222 (phiUnit x)| ^ (-(c' : ℝ))) := hdiffnull.symm
    _ = ∫⁻ x in phiUnit '' ((P \ {x | x 2 = 0}) \ {x | x 0 = 0}),
          ENNReal.ofReal (|myF222 x| ^ (-(c' : ℝ))) :=
        (phiUnit_cov P hPmeas (fun x => ENNReal.ofReal (|myF222 x| ^ (-(c' : ℝ))))).symm
    _ ≤ ∫⁻ x in cubeBox 8 ε, ENNReal.ofReal (|myF222 x| ^ (-(c' : ℝ))) :=
        lintegral_mono_set (subset_trans
          (Set.image_mono ((Set.diff_subset.trans Set.diff_subset).trans hPsub)) hsub)

/-- **`cover_ge_div`** : the `(2,2,2)` cover_ge_div field — for `c'` at-or-above the leaf threshold,
`|myF222|^{−c'}` is non-integrable on every open `Ω ∋ 0`. Via `routeM_coverGeDiv_of_boxDiverges` + the
`(2,2,2)` box divergence (`routeM222_box_diverges`). -/
theorem routeM222_cover_ge_div :
    ∀ c' : NNReal, (∃ i : Fin 1, monomialThreshold (routeM222D i) (routeM222K i) (routeM222H i)
        ≤ (c' : ℝ≥0∞)) →
      ∀ Ω : Set (Fin 8 → ℝ), IsOpen Ω → (0 : Fin 8 → ℝ) ∈ Ω →
        ¬ IntegrableOn (fun x => |myF222 x| ^ (-(c' : ℝ)) * (fun _ => (1 : ℝ)) x) Ω volume :=
  routeM_coverGeDiv_of_boxDiverges myF222 routeM222D routeM222K routeM222H
    (fun c' ⟨_, hi⟩ ε hε => routeM222_box_diverges c' hi ε hε)

end DLNFibre.DLN.RLCT
