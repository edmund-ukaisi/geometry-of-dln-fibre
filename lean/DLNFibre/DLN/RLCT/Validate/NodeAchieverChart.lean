import DLNFibre.DLN.RLCT.Validate.RouteMLayerCoverGE
import DLNFibre.DLN.RLCT.Validate.Case222Cover
import DLNFibre.DLN.RLCT.Validate.Case222Resolution

/-!
# `NodeAchieverChart` — the reusable general-`M` achiever chart bundle + the M-agnostic assembly

The `(3,3,4)` achiever box-divergence (`RouteMLayerCoverGEL2.routeM334_box_diverges`) was built from a
chart bundle (`L2AchieverChart`) + a divergence ASSEMBLY (`routeM334_box_diverges_of_chart`), the
assembly being M-agnostic GIVEN the bundle (per the design certificate
`threads/26-r1-genM-chart/`). This file lifts that template to **arbitrary `M`**:

* **`NodeAchieverChart M`** — the `L2AchieverChart` fields generalized to `M` (no hard-coded `Fin 21`
  / `(3,3,4)` / two-axis Jacobian). A chart `phi`, a binding pivot axis `p`, the genuine Jacobian
  exponents `leafH` (with `leafH p = minAdm M − 1` and threshold `½·minAdm M`), the unit factor `Ufun`
  with its compact bound + a.e.-positivity, the leaf-integrand identity, the composite
  change-of-variables, and the image containment.

* **`routeMCore_box_diverges_of_nodeChart`** — the REUSABLE core: the achiever-path box-divergence
  atom's conclusion for `M`, proven FROM a `NodeAchieverChart M`, by the `(3,3,4)` assembly chain
  (`nodeLeaf_box_div` + the dominate / transport / match / drop / diverge calc), now M-agnostic. The
  single M-specific input — `monomialThreshold N (nodeLeafK p) leafH ≤ ½·minAdm M` — is discharged
  INSIDE the structure from the binding-axis fields (`leafH p = minAdm M − 1` via
  `monomialThreshold_le_regularSeq`).

This banks the bundle + assembly infrastructure (the `(4,4,2,2)` instance lives in `RouteM4422`). It
does NOT close the general-`M` atom (that needs a uniform `φ_M` for all `M`, designed separately); it
banks the reusable shape and the assembly that consumes it.

The single external citation is `monomial_rlct` (S2), reached via
`monomialIntegrand_lintegral_box_eq_top` exactly as in the `(3,3,4)` assembly.
-/

open MeasureTheory
open scoped ENNReal BigOperators

namespace DLNFibre.DLN.RLCT

variable {L : ℕ}

/-! ## The binding-axis loss-base exponent vector (M-agnostic)

The achiever leaf's loss-base exponents `k` are `δ_p` — `1` on the binding pivot axis `p` (the loss
base `|u_p|²`), `0` on the spectator axes. The single-pivot form the cert's `(k,h) = (1, minAdm−1)`
binding axis encodes. -/

/-- The achiever leaf loss-base exponents on `Fin N`: `1` on the binding pivot `p`, `0` elsewhere
(the M-agnostic generalization of `leafK334`). -/
def nodeLeafK (N : ℕ) (p : Fin N) : Fin N → ℕ := fun j => if j = p then 1 else 0

/-- The binding pivot `p` has `nodeLeafK N p p = 1 ≠ 0` — the singular-axis witness for
`monomialIntegrand_lintegral_box_eq_top`. -/
theorem nodeLeafK_binding (N : ℕ) (p : Fin N) : nodeLeafK N p p ≠ 0 := by
  simp [nodeLeafK]

/-! ## The `NodeAchieverChart M` bundle (the `L2AchieverChart` fields, generalized to `M`)

A per-node achiever chart for `M`, with binding pivot axis `p` and genuine Jacobian exponents
`leafH` (`leafH p = minAdm M − 1`, the radial blow-up of the codim-`minAdm` achiever center; the
spectator monomial on `k = 0` axes does not lower the threshold). Carrying the bundle as an explicit
hypothesis set isolates the divergence ASSEMBLY (proven M-agnostically from the bundle) from the chart
CONSTRUCTION (the case-specific Schur-frame ∘ radial blow-up). `Ufun` is the `u_p`-free unit factor of
`F ∘ phi = (u_p)² · U`; `B` its compact-box upper bound. -/
structure NodeAchieverChart (M : Fin (L + 1) → ℕ) where
  /-- Non-degeneracy: the achiever center has positive codimension `minAdm M ≥ 1`. -/
  hpos : 1 ≤ minAdm M
  /-- The chart map (the case-specific Schur-frame ∘ radial blow-up, in flat coordinates). -/
  phi : (Fin (routeMAmbient M) → ℝ) → (Fin (routeMAmbient M) → ℝ)
  /-- The binding pivot axis (the radial exceptional divisor `u_p`). -/
  p : Fin (routeMAmbient M)
  /-- The genuine Jacobian exponents `h` of the chart (`|det Dφ| = ∏_j |u_j|^{leafH j}`). -/
  leafH : Fin (routeMAmbient M) → ℕ
  /-- The binding axis carries the radial blow-up exponent `minAdm M − 1` (`(k,h) = (1, minAdm−1)`). -/
  leafH_pivot : leafH p = minAdm M - 1
  /-- The unit factor `U` of `F ∘ phi = (u_p)² · U`. -/
  Ufun : (Fin (routeMAmbient M) → ℝ) → ℝ
  /-- On each source box `[0,δ]^N`, `U` admits a `δ`-dependent compact upper bound `B > 0`, and `U` is
  positive a.e. on the box (the SOUNDNESS-critical pair: `U ≤ B` gives `U^{−c'} ≥ B^{−c'} > 0` where
  `U > 0`; the vanishing locus `{U = 0}` is null, dropped a.e.). -/
  Ubound : ∀ δ : ℝ, ∃ B : ℝ, 0 < B ∧
    (∀ u ∈ Set.univ.pi (fun _ : Fin (routeMAmbient M) => Set.Icc (0 : ℝ) δ), Ufun u ≤ B) ∧
    ∀ᵐ u ∂(volume.restrict
        (Set.univ.pi (fun _ : Fin (routeMAmbient M) => Set.Icc (0 : ℝ) δ))), 0 < Ufun u
  /-- `U` is measurable (a polynomial in the chart coordinates). -/
  Umeas : Measurable Ufun
  /-- The leaf-integrand identity, holding **a.e.** (`∀ᵐ u ∂volume`): `(∏_j |u_j|^{leafH j}) ·
  |F ∘ phi|^{−c} = monomialIntegrand · U^{−c}` (the genuine Jacobian × the loss power, on the chart
  orthant). The box-divergence atom is intrinsically an a.e./lintegral property, so the a.e. form is the
  faithful one: a POLYNOMIAL chart supplies it ∀u via `Filter.Eventually.of_forall`; a RATIONAL chart
  (the smeared `φ_sm`) supplies it off its null pole, where the rate `F∘φ = u_p²·U` genuinely holds.
  The M-agnostic `leaf_integrand334`. -/
  leaf_integrand : ∀ (c : ℝ), ∀ᵐ u ∂(volume : Measure (Fin (routeMAmbient M) → ℝ)),
    (∏ j, |u j| ^ (leafH j)) * |routeMCore M (phi u)| ^ (-c)
      = monomialIntegrand (routeMAmbient M) (nodeLeafK (routeMAmbient M) p) leafH c u
        * (Ufun u) ^ (-c)
  /-- The composite change-of-variables (the genuine chart Jacobian `|det Dφ| = ∏_j |u_j|^{leafH j}`,
  off the pivot-zero locus `{u_p = 0}`): `∫⁻_{phi '' (V \ {u_p=0})} g = ∫⁻_{V \ {u_p=0}}
  ofReal(∏_j |u_j|^{leafH j}) · g (phi u)`. The M-agnostic `phi334_cov`. -/
  cov : ∀ (V : Set (Fin (routeMAmbient M) → ℝ)), MeasurableSet V →
      ∀ (g : (Fin (routeMAmbient M) → ℝ) → ℝ≥0∞),
    ∫⁻ x in phi '' (V \ {x | x p = 0}), g x
      = ∫⁻ u in V \ {x | x p = 0}, ENNReal.ofReal (∏ j, |u j| ^ (leafH j)) * g (phi u)
  /-- Image containment: a small source box `[0,δ]^N` maps into `cubeBox N ε`. -/
  image_subset : ∀ ε : ℝ, 0 < ε →
    ∃ δ > 0, phi '' (Set.univ.pi (fun _ : Fin (routeMAmbient M) => Set.Icc (0 : ℝ) δ))
      ⊆ cubeBox (routeMAmbient M) ε

/-! ## The leaf monomial threshold from the bundle (the M-specific input, discharged) -/

/-- **The bundle's leaf monomial threshold is `≤ ½·minAdm M`** (the binding axis `p` has
`(k,h) = (1, minAdm M − 1)`, realising `minAdm/2` via `monomialThreshold_le_regularSeq`; the spectator
monomial on `k = 0` axes has ratio `⊤`, so it does not lower the threshold). The M-agnostic
`leafMonomialThreshold334_le`, discharged from `leafH_pivot` + `hpos`. -/
theorem nodeChart_thresholdLe (M : Fin (L + 1) → ℕ) (W : NodeAchieverChart M) :
    monomialThreshold (routeMAmbient M) (nodeLeafK (routeMAmbient M) W.p) W.leafH
      ≤ (minAdm M : ℝ≥0∞) / 2 := by
  exact monomialThreshold_le_regularSeq (routeMAmbient M)
    (nodeLeafK (routeMAmbient M) W.p) W.leafH (minAdm M) W.hpos W.p
    (by simp [nodeLeafK]) W.leafH_pivot

/-! ## The unit-stripped achiever leaf-box divergence (M-agnostic, from the bundle)

The `(3,3,4)` `leaf334_box_div`, generalized to `M`: for `c'` at-or-above `½·minAdm M` (`0 < c'`),
`∫⁻_{[0,ε]^N} monomialIntegrand · U^{−c'} = ⊤`. Lower-bound `U^{−c'} ≥ B^{−c'} > 0` (`U ≤ B`,
`−c' < 0`), pull the constant out, apply the bare-monomial box divergence
(`monomialIntegrand_lintegral_box_eq_top`). -/
theorem nodeLeaf_box_div (M : Fin (L + 1) → ℕ) (W : NodeAchieverChart M) (c' : ℝ) (hc'0 : 0 < c')
    (hc' : monomialThreshold (routeMAmbient M) (nodeLeafK (routeMAmbient M) W.p) W.leafH
      ≤ ENNReal.ofReal c')
    (ε : ℝ) (hε : 0 < ε) :
    ∫⁻ u in Set.univ.pi (fun _ : Fin (routeMAmbient M) => Set.Icc (0 : ℝ) ε),
      ENNReal.ofReal (monomialIntegrand (routeMAmbient M) (nodeLeafK (routeMAmbient M) W.p) W.leafH c' u
        * (W.Ufun u) ^ (-c')) = ⊤ := by
  set N := routeMAmbient M with hN
  set k := nodeLeafK N W.p with hk
  obtain ⟨B, hB0, hBle, hUpos_ae⟩ := W.Ubound ε
  set box := Set.univ.pi (fun _ : Fin N => Set.Icc (0 : ℝ) ε) with hbox
  have hmonomeas : Measurable
      (fun u : Fin N → ℝ => monomialIntegrand N k W.leafH c' u) := by
    unfold monomialIntegrand; fun_prop
  have hmonomeas' : Measurable
      (fun u : Fin N → ℝ => ENNReal.ofReal (|monomialIntegrand N k W.leafH c' u|)) :=
    ENNReal.measurable_ofReal.comp (continuous_abs.measurable.comp hmonomeas)
  have hlb : ∫⁻ u in box, ENNReal.ofReal (B ^ (-c'))
        * ENNReal.ofReal (|monomialIntegrand N k W.leafH c' u|)
      ≤ ∫⁻ u in box, ENNReal.ofReal (monomialIntegrand N k W.leafH c' u
          * (W.Ufun u) ^ (-c')) := by
    apply setLIntegral_mono_ae
      (ENNReal.measurable_ofReal.comp (hmonomeas.mul (W.Umeas.pow_const _))).aemeasurable
    rw [ae_restrict_iff' (MeasurableSet.univ_pi (fun _ => measurableSet_Icc))] at hUpos_ae
    filter_upwards [hUpos_ae] with u hUposimp hu
    have hUpos := hUposimp hu
    rw [← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    have hmono : 0 ≤ monomialIntegrand N k W.leafH c' u := by
      unfold monomialIntegrand; positivity
    rw [abs_of_nonneg hmono, mul_comm]
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_nonpos hUpos (hBle u hu) (by linarith)) hmono
  have hBne : ENNReal.ofReal (B ^ (-c')) ≠ 0 := by
    simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact Real.rpow_pos_of_pos hB0 _
  rw [lintegral_const_mul _ hmonomeas',
    monomialIntegrand_lintegral_box_eq_top N k W.leafH
      ⟨W.p, nodeLeafK_binding N W.p⟩ c' hc' hc'0 hε,
    ENNReal.mul_top hBne] at hlb
  exact top_le_iff.1 hlb

/-! ## The achiever box-divergence atom, from the bundle (the REUSABLE M-agnostic core)

The `(3,3,4)` `routeM334_box_diverges_of_chart`, generalized to `M`: given a `NodeAchieverChart M`,
the achiever-path box integral `∫⁻_{cubeBox N ε} |routeMCore M|^{−c'} = ⊤` for `c'` at-or-above
`½·minAdm M`, every `ε > 0`. This is precisely the conclusion of the atom
`routeMCore_box_diverges_achiever M hpos c' hc' ε hε`. The assembly is M-agnostic; the only
case-specific content is the chart bundle (the per-node construction). -/
theorem routeMCore_box_diverges_of_nodeChart (M : Fin (L + 1) → ℕ) (W : NodeAchieverChart M)
    (c' : NNReal) (hc' : (minAdm M : ℝ≥0∞) / 2 ≤ (c' : ℝ≥0∞)) (ε : ℝ) (hε : 0 < ε) :
    ∫⁻ x in cubeBox (routeMAmbient M) ε,
      ENNReal.ofReal (|routeMCore M x| ^ (-(c' : ℝ))) = ⊤ := by
  set N := routeMAmbient M with hN
  set k := nodeLeafK N W.p with hk
  -- `½·minAdm ≤ c'` ⟹ `0 < c'` (since `minAdm ≥ 1`)
  have hmpos : (0 : ℝ≥0∞) < (minAdm M : ℝ≥0∞) / 2 := by
    rw [ENNReal.div_pos_iff]
    refine ⟨?_, by norm_num⟩
    have : (0 : ℝ≥0∞) < (minAdm M : ℝ≥0∞) := by
      exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one W.hpos)
    exact this.ne'
  have hc'0 : (0 : ℝ) < (c' : ℝ) := by
    by_contra hle
    have hc'00 : (c' : ℝ) = 0 := le_antisymm (not_lt.mp hle) (by positivity)
    have hc'z : (c' : ℝ≥0∞) = 0 := by
      rw [show (c' : ℝ≥0∞) = ENNReal.ofReal (c' : ℝ) from (ENNReal.ofReal_coe_nnreal).symm, hc'00,
        ENNReal.ofReal_zero]
    rw [hc'z] at hc'
    exact absurd (le_antisymm hc' (zero_le _)) hmpos.ne'
  have hthr : monomialThreshold N k W.leafH ≤ ENNReal.ofReal (c' : ℝ) := by
    rw [ENNReal.ofReal_coe_nnreal]
    exact le_trans (nodeChart_thresholdLe M W) hc'
  obtain ⟨δ, hδ, hsub⟩ := W.image_subset ε hε
  set P := Set.univ.pi (fun _ : Fin N => Set.Icc (0 : ℝ) δ) with hP
  have hPmeas : MeasurableSet P := MeasurableSet.univ_pi (fun _ => measurableSet_Icc)
  -- the pivot-zero locus `{u_p = 0}` is null, so the `\ {x p = 0}` restriction is a no-op
  have hdiffnull : ∫⁻ x in P \ {x | x W.p = 0},
        ENNReal.ofReal (∏ j, |x j| ^ (W.leafH j))
          * ENNReal.ofReal (|routeMCore M (W.phi x)| ^ (-(c' : ℝ)))
      = ∫⁻ x in P, ENNReal.ofReal (∏ j, |x j| ^ (W.leafH j))
          * ENNReal.ofReal (|routeMCore M (W.phi x)| ^ (-(c' : ℝ))) := by
    apply setLIntegral_congr
    exact MeasureTheory.diff_ae_eq_self.2 (measure_mono_null Set.inter_subset_right
      (coordZero_null W.p))
  apply top_le_iff.1
  calc (⊤ : ℝ≥0∞)
      = ∫⁻ u in P,
          ENNReal.ofReal (monomialIntegrand N k W.leafH (c' : ℝ) u
            * (W.Ufun u) ^ (-(c' : ℝ))) :=
        (nodeLeaf_box_div M W (c' : ℝ) hc'0 hthr δ hδ).symm
    _ = ∫⁻ u in P, ENNReal.ofReal (∏ j, |u j| ^ (W.leafH j))
          * ENNReal.ofReal (|routeMCore M (W.phi u)| ^ (-(c' : ℝ))) := by
        -- the leaf-integrand identity now holds a.e. (off the chart's null pole); the box-divergence
        -- integral is a.e.-insensitive, so the a.e. congruence suffices (`setLIntegral_congr_fun_ae`).
        refine setLIntegral_congr_fun_ae hPmeas ?_
        filter_upwards [W.leaf_integrand (c' : ℝ)] with u hu _
        rw [← ENNReal.ofReal_mul (by positivity), hu]
    _ = ∫⁻ x in P \ {x | x W.p = 0}, ENNReal.ofReal (∏ j, |x j| ^ (W.leafH j))
          * ENNReal.ofReal (|routeMCore M (W.phi x)| ^ (-(c' : ℝ))) :=
        hdiffnull.symm
    _ = ∫⁻ x in W.phi '' (P \ {x | x W.p = 0}),
          ENNReal.ofReal (|routeMCore M x| ^ (-(c' : ℝ))) :=
        (W.cov P hPmeas
          (fun x => ENNReal.ofReal (|routeMCore M x| ^ (-(c' : ℝ))))).symm
    _ ≤ ∫⁻ x in cubeBox N ε,
          ENNReal.ofReal (|routeMCore M x| ^ (-(c' : ℝ))) :=
        lintegral_mono_set (subset_trans (Set.image_mono Set.diff_subset) hsub)

end DLNFibre.DLN.RLCT
