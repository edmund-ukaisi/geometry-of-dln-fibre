import DLNFibre.Core.FibreNormalForm
import DLNFibre.DLN.RLCT.Validate.RouteMSJCornerGate
import DLNFibre.DLN.RLCT.Validate.RouteMSJRadialPolar
import DLNFibre.DLN.RLCT.Validate.RouteMSJRadialInt

set_option linter.style.longLine false

/-!
# `RouteMSJRankRCodim` — the rank-`r` codimension integrability (Brick D-B)

**Thread `genm-sj5` (aoyagi-full Stage 2), Brick D-B — the C_hle finiteness core.** The banked
`RouteMSJGoodChart.twoMatBox_injectiveLinear_lintegral_lt_top` / `RouteMSJCornerGate.corner_block_cube_lintegral_lt_top_of_injective`
handle an INJECTIVE linear loss `L`, with the full threshold `c' < n/2`. This module EXTENDS that to a
NON-injective linear map of rank `r` (`finrank (range L) = r`), with the sharp threshold `c' < r/2` —
exactly the `s1-Chle-cert §3` correction of `§A.4` (the pivot-block absorbed integral converges iff
`c'' < u·ρ/2`, `ρ = rank Q`, NOT the over-predicted `u·M₁/2`).

## What lands here (network-free, no `monomial_rlct`, no `cited_aoyagi_dln`)

* **`lintegral_comp_linearMap`** — the finite-dim linear-map CoV on the raw pi type `Fin n → ℝ`:
  `∫⁻ y, g (T y) = ofReal |det T|⁻¹ · ∫⁻ y, g y`, `det T ≠ 0` (mirrors the banked
  `RouteMSJDecoratedPeelMeas.lintegral_comp_mulLeftₚ` for a general `T`, via
  `map_linearMap_addHaar_eq_smul_addHaar`).
* **`Pcanon`** (`= ιcanon ∘ ρcanon`), the canonical rank-`r` map (first-`r`-coords projection then a
  zero-pad injection), with `finrank_range_Pcanon = r` and the squared-sum identity
  `sq_sum_Pcanon : ∑ (Pcanon x)² = ∑_{j:Fin r} (x (castLE j))²`.
* **`exists_pos_coercive`** — an injective linear `e : (Fin m → ℝ) ≃ₗ (Fin m → ℝ)` is coercive:
  `∃ a > 0, ∀ w, a · (∑ w²) ≤ ∑ (e w)²` (via the banked compact-sphere lower bound
  `exists_pos_lower_bound_on_sphere` + degree-2 homogeneity).
* **`lintegral_box_firstCoords_sq_neg_lt_top`** — the ball/box finiteness of the FIRST-`r`-coordinate
  squared-norm loss: `∫_{box_n} (∑_{j:Fin r} y_{castLE j}²)^{−c'} < ⊤` for `c' < r/2` (Fubini over the
  `Fin r ⊕ Fin (n−r)` coordinate split; the inner `Fin r`-block via the banked ball radial lemma).
* **`lintegral_cube_frobSq_neg_of_finrank_range`** — the headline: for `L` of rank `r`,
  `∫_{[-1,1]^n} (∑ (L x)²)^{−c'} < ⊤` when `c' < r/2`. Route: normal form `L = eL⁻¹ ∘ Pcanon ∘ eR⁻¹`
  (`Core.FibreNormalForm.exists_conj`), coercivity of `eL⁻¹`, the box CoV under `eR⁻¹`, then the
  first-coordinate ball finiteness.
* **`twoMatBox_rankR_lintegral_lt_top`** — the directly-consumable two-matrix-box form (a measure-preserving
  flatten `E` + rank-`rk` `L`), EXTENDING the banked injective `twoMatBox_injectiveLinear_lintegral_lt_top`
  (injective/`n/2`) to the rank-deficient case (`rk/2`). This is the shape the D-assembly's C_hle finiteness
  consumes.

Axiom target: `[propext, Classical.choice, Quot.sound]`.
-/

namespace DLNFibre.DLN.RLCT

open MeasureTheory Matrix Set
open scoped ENNReal BigOperators

/-! ## The finite-dim linear-map change of variables (raw pi type) -/

/-- **The finite-dim linear-map CoV on `Fin n → ℝ`.** For `T` a linear endomorphism with `det T ≠ 0`
and `g` measurable, `∫⁻ y, g (T y) = ofReal |det T|⁻¹ · ∫⁻ y, g y`. Mirrors the banked
`RouteMSJDecoratedPeelMeas.lintegral_comp_mulLeftₚ` for a general `T`
(`map_linearMap_addHaar_eq_smul_addHaar` + `lintegral_map` + `lintegral_smul_measure`). -/
theorem lintegral_comp_linearMap {n : ℕ} (T : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ))
    (hT : LinearMap.det T ≠ 0) (g : (Fin n → ℝ) → ℝ≥0∞) (hg : Measurable g) :
    ∫⁻ y : Fin n → ℝ, g (T y)
      = ENNReal.ofReal (|LinearMap.det T|⁻¹) * ∫⁻ y : Fin n → ℝ, g y := by
  have hTmeas : Measurable T := T.continuous_of_finiteDimensional.measurable
  rw [← lintegral_map hg hTmeas, Measure.map_linearMap_addHaar_eq_smul_addHaar volume hT,
    lintegral_smul_measure, smul_eq_mul, abs_inv]

/-! ## The canonical rank-`r` map -/

variable {n m r : ℕ}

/-- The first-`r`-coordinates projection `(Fin n → ℝ) →ₗ (Fin r → ℝ)` (`funLeft (castLE)`). -/
noncomputable def ρcanon (hrn : r ≤ n) : (Fin n → ℝ) →ₗ[ℝ] (Fin r → ℝ) :=
  LinearMap.funLeft ℝ ℝ (Fin.castLE hrn)

theorem ρcanon_apply (hrn : r ≤ n) (x : Fin n → ℝ) (j : Fin r) :
    ρcanon hrn x j = x (Fin.castLE hrn j) := rfl

theorem ρcanon_surjective (hrn : r ≤ n) : Function.Surjective (ρcanon hrn) :=
  LinearMap.funLeft_surjective_of_injective ℝ ℝ _ (Fin.castLE_injective hrn)

/-- The zero-pad injection `(Fin r → ℝ) →ₗ (Fin m → ℝ)`: copy the `r` entries into the first `r` slots,
zero elsewhere. -/
noncomputable def ιcanon : (Fin r → ℝ) →ₗ[ℝ] (Fin m → ℝ) where
  toFun v := fun i => if h : (i : ℕ) < r then v ⟨i, h⟩ else 0
  map_add' v w := by funext i; by_cases h : (i : ℕ) < r <;> simp [h]
  map_smul' c v := by funext i; by_cases h : (i : ℕ) < r <;> simp [h]

theorem ιcanon_apply (v : Fin r → ℝ) (i : Fin m) :
    (ιcanon v : Fin m → ℝ) i = if h : (i : ℕ) < r then v ⟨i, h⟩ else 0 := rfl

theorem ιcanon_injective (hrm : r ≤ m) : Function.Injective (ιcanon (r := r) (m := m)) := by
  intro v w hvw
  funext j
  have hj : ((Fin.castLE hrm j : Fin m) : ℕ) < r := by simpa using j.2
  have := congrFun hvw (Fin.castLE hrm j)
  rw [ιcanon_apply, ιcanon_apply, dif_pos hj] at this
  simpa using this

/-- The zero-pad injection is a squared-norm isometry: `∑ (ιcanon v)² = ∑ v²` (needs `r ≤ m`). -/
theorem sq_sum_ιcanon (hrm : r ≤ m) (v : Fin r → ℝ) :
    ∑ i : Fin m, ((ιcanon v : Fin m → ℝ) i) ^ 2 = ∑ j : Fin r, (v j) ^ 2 := by
  classical
  have hval : ∀ j : Fin r, (ιcanon v : Fin m → ℝ) (Fin.castLE hrm j) = v j := by
    intro j
    rw [ιcanon_apply, dif_pos (show ((Fin.castLE hrm j : Fin m) : ℕ) < r by simpa using j.2)]
    exact congrArg v (Fin.ext (by simp))
  have key : ∑ j : Fin r, (v j) ^ 2
      = ∑ i ∈ (Finset.univ.image (fun j : Fin r => Fin.castLE hrm j)),
          ((ιcanon v : Fin m → ℝ) i) ^ 2 := by
    rw [Finset.sum_image (fun a _ b _ h => Fin.castLE_injective hrm h)]
    exact Finset.sum_congr rfl (fun j _ => by rw [hval j])
  rw [key]
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro i _ hi
  have hir : ¬ ((i : ℕ) < r) := by
    intro hlt
    exact hi (Finset.mem_image.mpr ⟨⟨i, hlt⟩, Finset.mem_univ _, by apply Fin.ext; simp⟩)
  simp [ιcanon_apply, hir]

/-- The canonical rank-`r` map `(Fin n → ℝ) →ₗ (Fin m → ℝ)`: project to the first `r` coordinates, then
zero-pad. -/
noncomputable def Pcanon (hrn : r ≤ n) : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ) :=
  (ιcanon (m := m)).comp (ρcanon hrn)

theorem sq_sum_Pcanon (hrn : r ≤ n) (hrm : r ≤ m) (x : Fin n → ℝ) :
    ∑ i : Fin m, ((Pcanon (m := m) hrn x) i) ^ 2 = ∑ j : Fin r, (x (Fin.castLE hrn j)) ^ 2 := by
  change ∑ i : Fin m, ((ιcanon (ρcanon hrn x) : Fin m → ℝ) i) ^ 2 = _
  rw [sq_sum_ιcanon hrm (ρcanon hrn x)]
  exact Finset.sum_congr rfl (fun j _ => by rw [ρcanon_apply])

theorem finrank_range_Pcanon (hrn : r ≤ n) (hrm : r ≤ m) :
    Module.finrank ℝ (LinearMap.range (Pcanon (m := m) hrn)) = r := by
  rw [Pcanon, LinearMap.range_comp, LinearMap.range_eq_top.mpr (ρcanon_surjective hrn),
    Submodule.map_top, LinearMap.finrank_range_of_inj (ιcanon_injective hrm),
    Module.finrank_fin_fun]

/-! ## Coercivity of an injective endomorphism -/

/-- **An injective linear endomorphism of `Fin m → ℝ` is coercive** (squared-norm form): there is
`a > 0` with `a · (∑ w²) ≤ ∑ (e w)²` for all `w`. The compact-sphere positive minimum
(`exists_pos_lower_bound_on_sphere`, applied to the continuous, sphere-positive `w ↦ ∑ (e w)²`) plus
degree-2 homogeneity. -/
theorem exists_pos_coercive (e : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ)) (he : Function.Injective e) :
    ∃ a : ℝ, 0 < a ∧ ∀ w : Fin m → ℝ, a * (∑ i, (w i) ^ 2) ≤ ∑ i, (e w i) ^ 2 := by
  classical
  set g : (Fin m → ℝ) → ℝ := fun w => ∑ i, (e w i) ^ 2 with hgdef
  have hecont : Continuous (fun w : Fin m → ℝ => e w) := e.continuous_of_finiteDimensional
  have hgc : Continuous g :=
    continuous_finset_sum _ (fun i _ => ((continuous_apply i).comp hecont).pow 2)
  have hhom : ∀ (c : ℝ) (w : Fin m → ℝ), g (c • w) = c ^ 2 * g w := by
    intro c w
    simp only [hgdef, map_smul, Pi.smul_apply, smul_eq_mul, mul_pow, Finset.mul_sum]
  -- sphere positivity (`e` injective ⟹ `∑ (e w)² > 0` off the origin)
  have hpos : ∀ ω : Metric.sphere (0 : EuclideanSpace ℝ (Fin m)) 1,
      0 < g (WithLp.ofLp (ω : EuclideanSpace ℝ (Fin m))) := by
    intro ω
    have hnorm : ‖(ω : EuclideanSpace ℝ (Fin m))‖ = 1 := mem_sphere_zero_iff_norm.mp ω.2
    have hωne : (WithLp.ofLp (ω : EuclideanSpace ℝ (Fin m)) : Fin m → ℝ) ≠ 0 := by
      intro h
      rw [WithLp.ofLp_eq_zero] at h
      rw [h, norm_zero] at hnorm; exact one_ne_zero hnorm.symm
    have hene : e (WithLp.ofLp (ω : EuclideanSpace ℝ (Fin m))) ≠ 0 :=
      fun h => hωne (he (by rw [h, map_zero]))
    obtain ⟨i0, hi0⟩ := Function.ne_iff.mp hene
    exact Finset.sum_pos' (fun i _ => sq_nonneg _)
      ⟨i0, Finset.mem_univ _, lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hi0))⟩
  obtain ⟨a, ha, hlb⟩ := exists_pos_lower_bound_on_sphere g hgc hpos
  refine ⟨a, ha, fun w => ?_⟩
  rcases eq_or_ne w 0 with rfl | hw
  · simp [map_zero]
  · -- the Euclidean point of `w`, and its normalisation on the sphere
    set z : EuclideanSpace ℝ (Fin m) := (WithLp.equiv 2 (Fin m → ℝ)).symm w with hz
    have hsz : ‖z‖ ^ 2 = ∑ i, (w i) ^ 2 := by
      rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
      exact Finset.sum_congr rfl (fun i _ => by rw [Real.norm_eq_abs, sq_abs]; rfl)
    have hoz : WithLp.ofLp z = w := rfl
    have hznorm : ‖z‖ ≠ 0 := by
      rw [norm_ne_zero_iff]
      intro hz0
      apply hw
      rw [show w = WithLp.ofLp z from hoz.symm, WithLp.ofLp_eq_zero]
      exact hz0
    have hzpos : (0 : ℝ) < ‖z‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hznorm)
    have hmem : ‖z‖⁻¹ • z ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin m)) 1 := by
      rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hznorm]
    have hofLp : WithLp.ofLp (‖z‖⁻¹ • z) = ‖z‖⁻¹ • w := by
      rw [WithLp.ofLp_smul, hoz]
    have key := hlb ⟨‖z‖⁻¹ • z, hmem⟩
    rw [hofLp, hhom] at key
    -- `a ≤ (‖z‖⁻¹)² · g w`; clear denominators
    have hgw : g w = ∑ i, (e w i) ^ 2 := rfl
    have hsz' : (‖z‖⁻¹) ^ 2 = (∑ i, (w i) ^ 2)⁻¹ := by
      rw [inv_pow, hsz]
    rw [hsz'] at key
    have hspos : (0 : ℝ) < ∑ i, (w i) ^ 2 := by rw [← hsz]; positivity
    calc a * (∑ i, (w i) ^ 2)
        ≤ ((∑ i, (w i) ^ 2)⁻¹ * g w) * (∑ i, (w i) ^ 2) :=
          mul_le_mul_of_nonneg_right key hspos.le
      _ = g w := by field_simp

/-! ## Box finiteness of the pure squared-norm loss -/

/-- **The pure squared-norm loss is integrable over any `r`-dim box** (`c' < r/2`):
`∫_{[-R,R]^r} (∑ x²)^{−c'} < ⊤`. Transport to `EuclideanSpace` (`ofLp`), dominate the box by a closed
ball, apply the banked `corner_block_lintegral_lt_top` (with `a = 1` on the sphere). -/
theorem lintegral_box_sq_neg_lt_top (hr1 : 1 ≤ r) (R : ℝ)
    {c' : ℝ} (hc0 : 0 ≤ c') (hc' : c' < (r : ℝ) / 2) :
    ∫⁻ x in Set.univ.pi (fun _ : Fin r => Set.Icc (-R) R),
        ENNReal.ofReal ((∑ j, (x j) ^ 2) ^ (-c')) < ⊤ := by
  haveI : NeZero r := ⟨by omega⟩
  set g : (Fin r → ℝ) → ℝ := fun x => ∑ j, (x j) ^ 2 with hgdef
  have hg : Measurable g := by
    rw [hgdef]; exact continuous_finset_sum _ (fun j _ => ((continuous_apply j).pow 2)) |>.measurable
  have hof : Measurable (WithLp.ofLp : EuclideanSpace ℝ (Fin r) → (Fin r → ℝ)) :=
    (PiLp.volume_preserving_ofLp (Fin r)).measurable
  have hom' : ∀ (t : ℝ) (y : EuclideanSpace ℝ (Fin r)),
      g (WithLp.ofLp (t • y)) = t ^ 2 * g (WithLp.ofLp y) := by
    intro t y
    rw [WithLp.ofLp_smul]
    simp only [hgdef, Pi.smul_apply, smul_eq_mul, mul_pow, Finset.mul_sum]
  have hfmeas : Measurable (fun x : Fin r → ℝ => ENNReal.ofReal ((g x) ^ (-c'))) :=
    ENNReal.measurable_ofReal.comp ((by fun_prop : Measurable fun t : ℝ => t ^ (-c')).comp hg)
  have hbox_meas : MeasurableSet (Set.univ.pi (fun _ : Fin r => Set.Icc (-R) R)) :=
    MeasurableSet.univ_pi (fun _ => measurableSet_Icc)
  have hsub : (WithLp.ofLp : EuclideanSpace ℝ (Fin r) → (Fin r → ℝ)) ⁻¹'
        (Set.univ.pi (fun _ : Fin r => Set.Icc (-R) R))
      ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin r)) (Real.sqrt ((r : ℝ) * R ^ 2)) := by
    intro y hy
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Icc] at hy
    rw [Metric.mem_closedBall, dist_zero_right, EuclideanSpace.norm_eq]
    apply Real.sqrt_le_sqrt
    calc ∑ i, ‖(y : EuclideanSpace ℝ (Fin r)) i‖ ^ 2
        ≤ ∑ _i : Fin r, R ^ 2 := by
          refine Finset.sum_le_sum (fun i _ => ?_)
          rw [Real.norm_eq_abs]
          have hb : |(WithLp.ofLp (y : EuclideanSpace ℝ (Fin r))) i| ≤ R := abs_le.mpr (hy i)
          nlinarith [abs_nonneg (WithLp.ofLp (y : EuclideanSpace ℝ (Fin r)) i),
            sq_abs (WithLp.ofLp (y : EuclideanSpace ℝ (Fin r)) i), hb]
      _ = (r : ℝ) * R ^ 2 := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]; ring
  have hlb : ∀ ω : Metric.sphere (0 : EuclideanSpace ℝ (Fin r)) 1,
      (1 : ℝ) ≤ (fun y => g (WithLp.ofLp y)) (ω : EuclideanSpace ℝ (Fin r)) := by
    intro ω
    have hnorm : ‖(ω : EuclideanSpace ℝ (Fin r))‖ = 1 := mem_sphere_zero_iff_norm.mp ω.2
    have h2 := EuclideanSpace.norm_eq (ω : EuclideanSpace ℝ (Fin r))
    rw [hnorm] at h2
    have hsq : (∑ i, ‖(ω : EuclideanSpace ℝ (Fin r)) i‖ ^ 2) = 1 := by
      nlinarith [Real.sq_sqrt (by positivity :
        (0 : ℝ) ≤ ∑ i, ‖(ω : EuclideanSpace ℝ (Fin r)) i‖ ^ 2), h2.symm]
    rw [hgdef]
    rw [show (fun x : Fin r → ℝ => ∑ j, (x j) ^ 2) (WithLp.ofLp (ω : EuclideanSpace ℝ (Fin r)))
          = ∑ i, ‖(ω : EuclideanSpace ℝ (Fin r)) i‖ ^ 2 from
        Finset.sum_congr rfl (fun i _ => by rw [Real.norm_eq_abs, sq_abs])]
    rw [hsq]
  calc ∫⁻ x in Set.univ.pi (fun _ : Fin r => Set.Icc (-R) R),
          ENNReal.ofReal ((g x) ^ (-c'))
      = ∫⁻ y in (WithLp.ofLp : EuclideanSpace ℝ (Fin r) → (Fin r → ℝ)) ⁻¹'
            (Set.univ.pi (fun _ : Fin r => Set.Icc (-R) R)),
          ENNReal.ofReal ((g (WithLp.ofLp y)) ^ (-c')) :=
        ((PiLp.volume_preserving_ofLp (Fin r)).setLIntegral_comp_preimage hbox_meas hfmeas).symm
    _ ≤ ∫⁻ y in Metric.closedBall (0 : EuclideanSpace ℝ (Fin r)) (Real.sqrt ((r : ℝ) * R ^ 2)),
          ENNReal.ofReal ((g (WithLp.ofLp y)) ^ (-c')) := lintegral_mono_set hsub
    _ < ⊤ := corner_block_lintegral_lt_top (fun y => g (WithLp.ofLp y)) (hg.comp hof)
        hom' c' hc0 hc' 1 one_pos hlb

/-! ## First-coordinate ball finiteness -/

/-- **The first-`r`-coordinate squared-norm loss is integrable over any box.** For `c' < r/2`,
`∫_{[-R,R]^n} (∑_{j:Fin r} y_{castLE j}²)^{−c'} < ⊤`. Fubini over `Fin n = Fin r ⊕ Fin (n−r)`; the inner
`Fin r`-block is the banked ball radial finiteness, the outer factor is a bounded box. -/
theorem lintegral_box_firstCoords_sq_neg_lt_top (hrn : r ≤ n) (hr1 : 1 ≤ r) (R : ℝ)
    {c' : ℝ} (hc0 : 0 ≤ c') (hc' : c' < (r : ℝ) / 2) :
    ∫⁻ y in Set.univ.pi (fun _ : Fin n => Set.Icc (-R) R),
        ENNReal.ofReal ((∑ j : Fin r, (y (Fin.castLE hrn j)) ^ 2) ^ (-c')) < ⊤ := by
  classical
  have hn : r + (n - r) = n := Nat.add_sub_cancel' hrn
  set e : Fin r ⊕ Fin (n - r) ≃ Fin n := finSumFinEquiv.trans (finCongr hn) with he
  have hel : ∀ j : Fin r, e (Sum.inl j) = Fin.castLE hrn j := by
    intro j; apply Fin.ext; simp [he, finSumFinEquiv]
  -- the measure-preserving splitter `(Fin n → ℝ) ≃ᵐ (Fin r → ℝ) × (Fin (n-r) → ℝ)`
  set E : (Fin n → ℝ) ≃ᵐ (Fin r → ℝ) × (Fin (n - r) → ℝ) :=
    (MeasurableEquiv.piCongrLeft (fun _ : Fin n => ℝ) e).symm.trans
      (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin r ⊕ Fin (n - r) => ℝ)) with hEdef
  have hEmp : MeasurePreserving E (volume : Measure (Fin n → ℝ)) volume :=
    (volume_measurePreserving_piCongrLeft (fun _ : Fin n => ℝ) e).symm.trans
      (volume_measurePreserving_sumPiEquivProdPi (fun _ : Fin r ⊕ Fin (n - r) => ℝ))
  have hEval : ∀ (y : Fin n → ℝ) (j : Fin r), (E y).1 j = y (Fin.castLE hrn j) := by
    intro y j
    have h1 : (E y).1 j = y (e (Sum.inl j)) := rfl
    rw [h1, hel]
  -- `f` on the product; the domain and integrand match under `E`
  set f : (Fin r → ℝ) × (Fin (n - r) → ℝ) → ℝ≥0∞ :=
    fun w => ENNReal.ofReal ((∑ j : Fin r, (w.1 j) ^ 2) ^ (-c')) with hfdef
  have hbox_meas : MeasurableSet
      ((Set.univ.pi (fun _ : Fin r => Set.Icc (-R) R))
        ×ˢ (Set.univ.pi (fun _ : Fin (n - r) => Set.Icc (-R) R))) :=
    (MeasurableSet.univ_pi (fun _ => measurableSet_Icc)).prod
      (MeasurableSet.univ_pi (fun _ => measurableSet_Icc))
  have hfmeas : Measurable f := by
    rw [hfdef]
    refine ENNReal.measurable_ofReal.comp ((by fun_prop : Measurable fun t : ℝ => t ^ (-c')).comp ?_)
    exact continuous_finset_sum _ (fun j _ =>
      (((continuous_apply j).comp continuous_fst).pow 2)) |>.measurable
  have hpre : Set.univ.pi (fun _ : Fin n => Set.Icc (-R) R)
      = E ⁻¹' ((Set.univ.pi (fun _ : Fin r => Set.Icc (-R) R))
          ×ˢ (Set.univ.pi (fun _ : Fin (n - r) => Set.Icc (-R) R))) := by
    ext y
    simp only [Set.mem_preimage, Set.mem_prod, Set.mem_pi, Set.mem_univ, true_implies]
    constructor
    · intro hy
      exact ⟨fun j => hy (e (Sum.inl j)), fun j => hy (e (Sum.inr j))⟩
    · rintro ⟨h1, h2⟩ i
      -- every index `i : Fin n` is `e (inl _)` or `e (inr _)`
      obtain ⟨b, rfl⟩ := e.surjective i
      cases b with
      | inl j => exact h1 j
      | inr j => exact h2 j
  have hintegrand : ∀ y : Fin n → ℝ,
      ENNReal.ofReal ((∑ j : Fin r, (y (Fin.castLE hrn j)) ^ 2) ^ (-c')) = f (E y) := by
    intro y
    simp only [hfdef, hEval]
  rw [show (∫⁻ y in Set.univ.pi (fun _ : Fin n => Set.Icc (-R) R),
        ENNReal.ofReal ((∑ j : Fin r, (y (Fin.castLE hrn j)) ^ 2) ^ (-c')))
      = ∫⁻ y in Set.univ.pi (fun _ : Fin n => Set.Icc (-R) R), f (E y) from
        lintegral_congr (fun y => hintegrand y)]
  rw [hpre, hEmp.setLIntegral_comp_preimage_emb E.measurableEmbedding f
    ((Set.univ.pi (fun _ : Fin r => Set.Icc (-R) R))
      ×ˢ (Set.univ.pi (fun _ : Fin (n - r) => Set.Icc (-R) R)))]
  rw [Measure.volume_eq_prod (Fin r → ℝ) (Fin (n - r) → ℝ),
    setLIntegral_prod f hfmeas.aemeasurable]
  -- integrand is independent of the `Fin (n-r)` factor
  have hinner : ∀ x : Fin r → ℝ,
      ∫⁻ _y in Set.univ.pi (fun _ : Fin (n - r) => Set.Icc (-R) R), f (x, _y)
        = ENNReal.ofReal ((∑ j : Fin r, (x j) ^ 2) ^ (-c'))
            * volume (Set.univ.pi (fun _ : Fin (n - r) => Set.Icc (-R) R)) := by
    intro x
    rw [hfdef]
    simp only
    rw [setLIntegral_const]
  rw [lintegral_congr hinner]
  rw [lintegral_mul_const _ (by
    exact ENNReal.measurable_ofReal.comp ((by fun_prop : Measurable fun t : ℝ => t ^ (-c')).comp
      (continuous_finset_sum _ (fun j _ => ((continuous_apply j).pow 2)) |>.measurable)))]
  refine ENNReal.mul_lt_top ?_ ?_
  · exact lintegral_box_sq_neg_lt_top hr1 R hc0 hc'
  · exact (isCompact_univ_pi (fun _ => isCompact_Icc)).measure_lt_top

/-! ## The headline -/

/-- **Rank-`r` codimension integrability.** For a linear map `L : (Fin n → ℝ) →ₗ (Fin m → ℝ)` of rank
`r` (`finrank (range L) = r`), the cube-box integral of the squared-loss power is finite below the sharp
threshold `c' < r/2`:

    ∫_{[-1,1]^n} (∑ⱼ (L x)ⱼ²)^{−c'} < ⊤.

Extends `corner_block_cube_lintegral_lt_top_of_injective` (`r = n`, threshold `n/2`) to the rank-deficient
case. Route: `exists_conj` conjugates `L` to the canonical `Pcanon` (`L = eL⁻¹ ∘ Pcanon ∘ eR⁻¹`); the
coercivity of `eL⁻¹` bounds `∑ (L x)² ≥ a · ∑_{j<r} (eR⁻¹ x)_{castLE j}²`; the box CoV under `eR⁻¹`
(`lintegral_comp_linearMap`, image bounded) reduces to `lintegral_box_firstCoords_sq_neg_lt_top`. -/
theorem lintegral_cube_frobSq_neg_of_finrank_range
    (L : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ)) (hL : Module.finrank ℝ (LinearMap.range L) = r)
    {c' : ℝ} (hc0 : 0 ≤ c') (hc' : c' < (r : ℝ) / 2) :
    ∫⁻ x in Set.univ.pi (fun _ : Fin n => Set.Icc (-1 : ℝ) 1),
        ENNReal.ofReal ((∑ j, (L x j) ^ 2) ^ (-c')) < ⊤ := by
  classical
  -- dimension bounds
  have hr1 : 1 ≤ r := by
    rcases Nat.eq_zero_or_pos r with h0 | hpos
    · exfalso; rw [h0] at hc'; norm_num at hc'; linarith
    · exact hpos
  have hrn : r ≤ n := by
    have h := LinearMap.finrank_range_le L
    rw [hL, Module.finrank_fin_fun] at h; exact h
  have hrm : r ≤ m := by
    have h := Submodule.finrank_le (LinearMap.range L)
    rw [hL, Module.finrank_fin_fun] at h; exact h
  -- normal form: `L = eL⁻¹ ∘ Pcanon ∘ eR⁻¹`
  have hranP : Module.finrank ℝ (LinearMap.range (Pcanon (m := m) hrn)) = r :=
    finrank_range_Pcanon hrn hrm
  have hran : Module.finrank ℝ (LinearMap.range L)
      = Module.finrank ℝ (LinearMap.range (Pcanon (m := m) hrn)) := by rw [hL, hranP]
  have hker : Module.finrank ℝ (LinearMap.ker L)
      = Module.finrank ℝ (LinearMap.ker (Pcanon (m := m) hrn)) := by
    have e1 := LinearMap.finrank_range_add_finrank_ker L
    have e2 := LinearMap.finrank_range_add_finrank_ker (Pcanon (m := m) hrn)
    rw [Module.finrank_fin_fun] at e1 e2
    rw [hL] at e1; rw [hranP] at e2; omega
  obtain ⟨eL, eR, hconj⟩ := DLNFibre.Core.exists_conj L (Pcanon (m := m) hrn) hker hran
  have hLx : ∀ x, L x = eL.symm (Pcanon (m := m) hrn (eR.symm x)) := by
    intro x
    have hc := LinearMap.congr_fun hconj (eR.symm x)
    rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.coe_coe,
      LinearEquiv.apply_symm_apply] at hc
    rw [hc, LinearEquiv.symm_apply_apply]
  -- coercivity of `eL⁻¹`
  obtain ⟨a, ha, hcoer⟩ := exists_pos_coercive (eL.symm : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ))
    eL.symm.injective
  -- `c' = 0` is the constant integrand `= 1`
  rcases eq_or_lt_of_le hc0 with hc0eq | hc0pos
  · obtain rfl : c' = 0 := hc0eq.symm
    simp only [neg_zero, Real.rpow_zero, ENNReal.ofReal_one]
    rw [setLIntegral_const, one_mul]
    exact (isCompact_univ_pi (fun _ => isCompact_Icc)).measure_lt_top
  -- the pointwise domination `ofReal(E^{-c'}) ≤ ofReal(a^{-c'}) · ofReal(S^{-c'})`
  have hpt : ∀ x : Fin n → ℝ,
      ENNReal.ofReal ((∑ i, (L x i) ^ 2) ^ (-c'))
        ≤ ENNReal.ofReal (a ^ (-c'))
          * ENNReal.ofReal ((∑ j : Fin r, (eR.symm x) (Fin.castLE hrn j) ^ 2) ^ (-c')) := by
    intro x
    have hEeq : (∑ i, (L x i) ^ 2)
        = ∑ i, (eL.symm (Pcanon (m := m) hrn (eR.symm x)) i) ^ 2 :=
      Finset.sum_congr rfl (fun i _ => by rw [hLx x])
    have hSeq : (∑ i, (Pcanon (m := m) hrn (eR.symm x) i) ^ 2)
        = ∑ j : Fin r, (eR.symm x) (Fin.castLE hrn j) ^ 2 := sq_sum_Pcanon hrn hrm (eR.symm x)
    have hSx0 : (0 : ℝ) ≤ ∑ j : Fin r, (eR.symm x) (Fin.castLE hrn j) ^ 2 :=
      Finset.sum_nonneg (fun j _ => sq_nonneg _)
    have hle : a * (∑ j : Fin r, (eR.symm x) (Fin.castLE hrn j) ^ 2) ≤ ∑ i, (L x i) ^ 2 := by
      rw [← hSeq, hEeq]; exact hcoer (Pcanon (m := m) hrn (eR.symm x))
    rcases eq_or_lt_of_le hSx0 with hS0 | hSpos
    · -- `S = 0 ⟹ E = 0`
      have hwzero : Pcanon (m := m) hrn (eR.symm x) = 0 := by
        have hsum0 : ∑ i, (Pcanon (m := m) hrn (eR.symm x) i) ^ 2 = 0 := by rw [hSeq, ← hS0]
        funext i
        exact pow_eq_zero_iff (by norm_num : 2 ≠ 0) |>.mp
          ((Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg _)).mp hsum0 i (Finset.mem_univ i))
      have hEzero : (∑ i, (L x i) ^ 2) = 0 := by
        rw [hEeq, hwzero, map_zero]; simp
      rw [hEzero, ← hS0, Real.zero_rpow (by linarith : -c' ≠ 0)]
      simp
    · have haSpos : 0 < a * (∑ j : Fin r, (eR.symm x) (Fin.castLE hrn j) ^ 2) := mul_pos ha hSpos
      have hExpos : 0 < ∑ i, (L x i) ^ 2 := lt_of_lt_of_le haSpos hle
      rw [← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ a ^ (-c'))]
      apply ENNReal.ofReal_le_ofReal
      calc (∑ i, (L x i) ^ 2) ^ (-c')
          ≤ (a * (∑ j : Fin r, (eR.symm x) (Fin.castLE hrn j) ^ 2)) ^ (-c') :=
            Real.rpow_le_rpow_of_nonpos haSpos hle (by linarith : -c' ≤ 0)
        _ = a ^ (-c') * (∑ j : Fin r, (eR.symm x) (Fin.castLE hrn j) ^ 2) ^ (-c') :=
            Real.mul_rpow ha.le hSx0
  -- integrate the pointwise bound, then the box change of variables under `eR⁻¹`
  refine lt_of_le_of_lt (lintegral_mono hpt) ?_
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_
  -- the box CoV: `∫_{cube} H(eR⁻¹ x) ≤ ofReal|det|⁻¹ · ∫_{box} H < ⊤`
  set T : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ) := (eR.symm : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) with hT
  have hTdet : LinearMap.det T ≠ 0 := by
    rw [hT]; exact (LinearEquiv.isUnit_det' eR.symm).ne_zero
  set H : (Fin n → ℝ) → ℝ≥0∞ :=
    fun y => ENNReal.ofReal ((∑ j : Fin r, (y (Fin.castLE hrn j)) ^ 2) ^ (-c')) with hHdef
  have hHmeas : Measurable H := by
    rw [hHdef]
    refine ENNReal.measurable_ofReal.comp ((by fun_prop : Measurable fun t : ℝ => t ^ (-c')).comp ?_)
    exact continuous_finset_sum _ (fun j _ =>
      ((continuous_apply (Fin.castLE hrn j)).pow 2)) |>.measurable
  -- `T '' cube` is compact, hence contained in a box `[-R₀,R₀]^n`
  have hcompact : IsCompact (T '' (Set.univ.pi (fun _ : Fin n => Set.Icc (-1 : ℝ) 1))) :=
    (isCompact_univ_pi (fun _ => isCompact_Icc)).image T.continuous_of_finiteDimensional
  obtain ⟨R₀, hR₀⟩ := (hcompact.isBounded).subset_closedBall (0 : Fin n → ℝ)
  have hTcube_box : T '' (Set.univ.pi (fun _ : Fin n => Set.Icc (-1 : ℝ) 1))
      ⊆ Set.univ.pi (fun _ : Fin n => Set.Icc (-R₀) R₀) := by
    intro y hy
    have hyb := hR₀ hy
    rw [Metric.mem_closedBall, dist_zero_right] at hyb
    simp only [Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Icc]
    intro i
    have : |y i| ≤ R₀ := le_trans (by rw [← Real.norm_eq_abs]; exact norm_le_pi_norm y i) hyb
    exact abs_le.mp this
  -- reduce the cube integral of `H ∘ T` to the full-space CoV via the indicator trick
  have hind : ∀ x, (Set.univ.pi (fun _ : Fin n => Set.Icc (-1 : ℝ) 1)).indicator (fun x => H (T x)) x
      = (T '' (Set.univ.pi (fun _ : Fin n => Set.Icc (-1 : ℝ) 1))).indicator H (T x) := by
    intro x
    by_cases hx : x ∈ Set.univ.pi (fun _ : Fin n => Set.Icc (-1 : ℝ) 1)
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (Set.mem_image_of_mem T hx)]
    · have hnotmem : T x ∉ T '' (Set.univ.pi (fun _ : Fin n => Set.Icc (-1 : ℝ) 1)) := by
        rintro ⟨x', hx', hxx'⟩
        have hTinj : Function.Injective (⇑T : (Fin n → ℝ) → (Fin n → ℝ)) := eR.symm.injective
        rw [hTinj hxx'] at hx'
        exact hx hx'
      rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hnotmem]
  calc ∫⁻ x in Set.univ.pi (fun _ : Fin n => Set.Icc (-1 : ℝ) 1),
          ENNReal.ofReal ((∑ j : Fin r, (eR.symm x) (Fin.castLE hrn j) ^ 2) ^ (-c'))
      = ∫⁻ x, (Set.univ.pi (fun _ : Fin n => Set.Icc (-1 : ℝ) 1)).indicator
            (fun x => H (T x)) x := by
        rw [lintegral_indicator (MeasurableSet.univ_pi (fun _ => measurableSet_Icc))]
        refine setLIntegral_congr_fun (MeasurableSet.univ_pi (fun _ => measurableSet_Icc))
          (fun x _ => ?_)
        simp only [hHdef, hT, LinearEquiv.coe_coe]
    _ = ∫⁻ x, (T '' (Set.univ.pi (fun _ : Fin n => Set.Icc (-1 : ℝ) 1))).indicator H (T x) :=
        lintegral_congr hind
    _ = ENNReal.ofReal (|LinearMap.det T|⁻¹)
          * ∫⁻ y, (T '' (Set.univ.pi (fun _ : Fin n => Set.Icc (-1 : ℝ) 1))).indicator H y :=
        lintegral_comp_linearMap T hTdet
          ((T '' (Set.univ.pi (fun _ : Fin n => Set.Icc (-1 : ℝ) 1))).indicator H)
          (hHmeas.indicator (hcompact.isClosed.measurableSet))
    _ = ENNReal.ofReal (|LinearMap.det T|⁻¹)
          * ∫⁻ y in T '' (Set.univ.pi (fun _ : Fin n => Set.Icc (-1 : ℝ) 1)), H y := by
        rw [lintegral_indicator hcompact.isClosed.measurableSet]
    _ ≤ ENNReal.ofReal (|LinearMap.det T|⁻¹)
          * ∫⁻ y in Set.univ.pi (fun _ : Fin n => Set.Icc (-R₀) R₀), H y :=
        mul_le_mul_left' (lintegral_mono_set hTcube_box) _
    _ < ⊤ :=
        ENNReal.mul_lt_top ENNReal.ofReal_lt_top
          (lintegral_box_firstCoords_sq_neg_lt_top hrn hr1 R₀ hc0 hc')

/-- **The two-matrix-box rank-`rk` codimension integrability** — the directly-consumable form (extends
`RouteMSJGoodChart.twoMatBox_injectiveLinear_lintegral_lt_top` from injective/`n/2` to rank-`rk`/`rk/2`).
Given a measure-preserving flatten `E` of the matrix-product box `matBox p q 1 ×ˢ matBox a b 1` onto the
cube `[-1,1]^N`, and a linear `L : (Fin N → ℝ) →ₗ (Fin M → ℝ)` of rank `rk` (`finrank (range L) = rk`),
the matrix-box integral of `(∑ (L (E x))²)^{−c'}` is finite below `c' < rk/2`. Pure transport onto
`lintegral_cube_frobSq_neg_of_finrank_range`. -/
theorem twoMatBox_rankR_lintegral_lt_top {p q a b N M rk : ℕ} [NeZero N]
    (E : ((Fin p → Fin q → ℝ) × (Fin a → Fin b → ℝ)) ≃ᵐ (Fin N → ℝ))
    (hE : MeasurePreserving E
      (volume : Measure ((Fin p → Fin q → ℝ) × (Fin a → Fin b → ℝ)))
      (volume : Measure (Fin N → ℝ)))
    (hbox : matBox p q 1 ×ˢ matBox a b 1
      = E ⁻¹' Set.univ.pi (fun _ : Fin N => Set.Icc (-1 : ℝ) 1))
    (L : (Fin N → ℝ) →ₗ[ℝ] (Fin M → ℝ)) (hL : Module.finrank ℝ (LinearMap.range L) = rk)
    {c' : ℝ} (hc0 : 0 ≤ c') (hc' : c' < (rk : ℝ) / 2) :
    ∫⁻ x in matBox p q 1 ×ˢ matBox a b 1,
        ENNReal.ofReal ((∑ j, (L (E x) j) ^ 2) ^ (-c')) < ⊤ := by
  rw [hbox, hE.setLIntegral_comp_preimage_emb E.measurableEmbedding
    (fun z => ENNReal.ofReal ((∑ j, (L z j) ^ 2) ^ (-c')))
    (Set.univ.pi (fun _ : Fin N => Set.Icc (-1 : ℝ) 1))]
  exact lintegral_cube_frobSq_neg_of_finrank_range L hL hc0 hc'

/-- **Non-vacuity witness.** The rank-`1` identity on `Fin 1 → ℝ` with `c' = 0` (threshold `1/2`)
satisfies the hypotheses of `lintegral_cube_frobSq_neg_of_finrank_range`, so it is not vacuous. -/
example : True := by
  have hinj : Function.Injective (⇑(LinearMap.id : (Fin 1 → ℝ) →ₗ[ℝ] (Fin 1 → ℝ))) :=
    fun a b h => h
  have _ := lintegral_cube_frobSq_neg_of_finrank_range (n := 1) (m := 1) (r := 1)
    (LinearMap.id) (by rw [LinearMap.finrank_range_of_inj hinj, Module.finrank_fin_fun])
    (le_refl (0 : ℝ)) (by norm_num)
  trivial

end DLNFibre.DLN.RLCT
