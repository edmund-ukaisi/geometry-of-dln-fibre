import DLNFibre.DLN.RLCT.Validate.RouteMSmearedHeadlineL2Inst

/-!
# `RouteMSmearedAchieverGeneral` — the ∀M BOUNDARY-SMEARED achiever chart bundle + assembly

The BOUNDARY-SMEARED branch of the R1-LOWER generic achiever leg: the achiever box-divergence
`∫⁻_{cubeBox N ε} |routeMCore M|^{−c'} = ⊤` (`c' ≥ ½·minAdm M`, every `ε > 0`) for `M` in the
smeared class (`deepRank M < deepRows M`). The dispatch spine
(`routeMCore_box_diverges_achiever_spine`, `RouteMAchieverDispatch`) consumes this as the open
hypothesis

    hSmeared : ∀ _ : 2 ≤ L, BoundarySmeared M → BoxDiverges M c' ε.

This file does for the SMEARED branch what `NodeAchieverChart` did for the achiever-path atom: it
**isolates the divergence ASSEMBLY (proven M-agnostically) from the chart CONSTRUCTION** (the
case-specific rational-shear ∘ radial blow-up, the part the worked `(2,3,1)`/`(1,3,2)` instances
each spend ~1000 lines building, and which at OPAQUE widths is a separate multi-module build).

The chart factors as `φ = ψ ∘ R` (the ε-INDEPENDENT maps): `ψ` is the measure-preserving rational
shear ∘ linear reshape (total via Lean's `a⁻¹ = 0` totalization — NO pole obstruction), `R` is the
radial blow-up (polynomial, the SOLE Jacobian carrier `|det D u| = |u p|^h`). The source box radius
`δ` adapts to the caller's `ε` (the `(2,3,1)` precedent takes `δ = min(ε/2, 1)`), so the δ-DEPENDENT
data — the conditioned box, the unit `Uy`, and the analytic fields (field-A containment, the peeled
rate, `Uy > 0`) — are supplied PER-ε via `SmearedChartData`.

* **`SmearedChartData M n hN ψ R D p h`** — the δ-dependent inputs at one `ε`: the box radius `δ`,
  the conditioned per-axis `box`, the `z`-free unit `Uy`, and exactly the analytic fields the
  conditioned-box L=2 assembly `routeMCore_box_diverges_smearedL2` consumes (the field-A containment
  into `(ψ∘R)⁻¹(cubeBox ε)`, the radial fderiv/injectivity/det on the box, the decode-derived PEELED
  RATE `routeMCore M (ψ (R (insertNth p z y))) = z²·Uy y`, and `Uy > 0` — rank-block nondegeneracy
  `det P₁ ≠ 0` made an EXPLICIT box hypothesis, not a hidden full-box assumption).

* **`SmearedAchieverChart M`** — bundles the ε-INDEPENDENT inputs (the peel `n`/`hN`, the maps
  `ψ`/`R`/`D`, the pivot `p`, the radial exponent `h`, `ψ` measure-preserving + a measurable
  embedding, the binding-axis exponent `h − 2·minAdm M ≤ −1`) + the ε-indexed `data`.

* **`routeMCore_box_diverges_of_smearedChart`** — the REUSABLE M-agnostic core: the achiever
  box-divergence for `M` proven FROM a `SmearedAchieverChart M`, any `c' ≥ ½·minAdm M`, every
  `ε > 0`. A thin repackaging of `routeMCore_box_diverges_smearedL2` (the exponent specialised from
  the chart's `½·minAdm` field to the caller's `c'`).

* **`hSmeared_of_smearedChart`** — the spine wiring: given a chart-BUILDER `∀ M, BoundarySmeared M →
  SmearedAchieverChart M`, produces the spine's `hSmeared` hypothesis (`L = 2`). This is the shape
  `routeMCore_box_diverges_achiever_spine` consumes; it reduces the SMEARED branch ∀M to "construct
  one `SmearedAchieverChart M`".

This CLOSES the M-agnostic SMEARED assembly. The single remaining content is the chart CONSTRUCTION
at opaque widths — a separate build (the (1,1)/(2,1)/(1,2)-per-layer family the `phiL2` rate already
covers). Non-vacuity is WITNESSED in-file: the worked `(2,3,1)` chart assembles into a
`SmearedAchieverChart M231` (`smearedChart231`), and the assembly fires end-to-end to reproduce
`routeM231sm_box_diverges`.

Axiom-clean `[propext, Classical.choice, Quot.sound]` (measure theory; NO S2, NO `monomial_rlct` —
the cited monomial atom enters only inside each family's `hSdiv`, which the chart's `hRate`/`hUpos`
fields supply, not the assembly).
-/

open MeasureTheory
open scoped ENNReal BigOperators

namespace DLNFibre.DLN.RLCT

variable {L : ℕ}

/-! ## The δ-dependent chart data at one `ε` (the `routeMCore_box_diverges_smearedL2` δ-inputs) -/

/-- **The δ-dependent BOUNDARY-SMEARED chart data at one `ε`.** Given the ε-independent chart maps
`ψ`/`R`/`D`, pivot `p`, peel `n`/`hN`, and radial exponent `h`, this bundles the box radius `δ` and
the analytic inputs `routeMCore_box_diverges_smearedL2` consumes at that `ε`: the conditioned
`box`, the `z`-free unit `Uy`, and the proofs (field-A containment, radial fderiv/injectivity/det on
the box, the peeled rate, `Uy > 0`). The box radius adapts to `ε` (the `(2,3,1)` precedent's
`δ = min(ε/2, 1)`), so this is supplied per-ε. -/
structure SmearedChartData (M : Fin (L + 1) → ℕ) (n : ℕ) (hN : routeMAmbient M = n + 1)
    (ψ R : (Fin (routeMAmbient M) → ℝ) → (Fin (routeMAmbient M) → ℝ))
    (D : (Fin (routeMAmbient M) → ℝ) → (Fin (routeMAmbient M) → ℝ) →L[ℝ]
      (Fin (routeMAmbient M) → ℝ))
    (p : Fin (n + 1)) (h : ℕ) (ε : ℝ) where
  /-- The box radius (adapts to `ε`). -/
  δ : ℝ
  /-- The conditioned per-axis box (pivot in `Ioo 0 δ`, every other coord `k` in `box k`). -/
  box : Fin (n + 1) → Set ℝ
  /-- The `z`-free unit factor `Uy` (`= ‖P₁·H̄‖²`, the rate's polynomial part, reads only non-pivot
  coords). -/
  Uy : (Fin n → ℝ) → ℝ
  /-- Positive box radius. -/
  hδ : 0 < δ
  /-- **Field A** — the conditioned box maps into `(ψ∘R)⁻¹(cubeBox ε)`. -/
  hSpre : condBox (hN ▸ p) (fun k => box (hN ▸ k)) δ
    ⊆ (fun u => ψ (R u)) ⁻¹' (cubeBox (routeMAmbient M) ε)
  /-- `R` has fderiv `D` on the conditioned box. -/
  hRderiv : ∀ u ∈ condBox (hN ▸ p) (fun k => box (hN ▸ k)) δ,
    HasFDerivWithinAt R (D u) (condBox (hN ▸ p) (fun k => box (hN ▸ k)) δ) u
  /-- `R` is injective on the conditioned box (pivot `≠ 0` there). -/
  hRinj : Set.InjOn R (condBox (hN ▸ p) (fun k => box (hN ▸ k)) δ)
  /-- `|det (D u)| = |u p|^h` on the conditioned box (the sole radial Jacobian). -/
  hRdet : ∀ u ∈ condBox (hN ▸ p) (fun k => box (hN ▸ k)) δ,
    |(D u).det| = |u (hN ▸ p)| ^ h
  /-- Each non-pivot conditioned interval is measurable. -/
  hboxmeas : ∀ k, MeasurableSet (box (p.succAbove k))
  /-- Every conditioned coordinate interval is measurable (full `Fin (routeMAmbient M)` index). -/
  hboxmeasAll : ∀ k : Fin (routeMAmbient M), MeasurableSet ((fun k => box (hN ▸ k)) k)
  /-- The conditioned rest box has positive measure (non-vacuous). -/
  hboxpos : 0 < (volume : Measure (Fin n → ℝ))
    (Set.univ.pi (fun k : Fin n => box (p.succAbove k)))
  /-- `Uy` is measurable (a polynomial in the non-pivot coords). -/
  hUmeas : Measurable Uy
  /-- **The PEELED RATE on the conditioned box** — `routeMCore M (ψ (R (insertNth p z y)))
  = z²·Uy y` for `z` positive-small and `y` in the conditioned rest box (the off-pole quadratic
  rate; the chart collapses the deepest product to the pure radial `z·(P₁·H̄)`, `Uy = ‖P₁·H̄‖²`). -/
  hRate : ∀ z ∈ Set.Ioo (0:ℝ) δ,
    ∀ y ∈ Set.univ.pi (fun k : Fin n => box (p.succAbove k)),
      routeMCore M (ψ (R (hN ▸ (Fin.insertNth p z y)))) = z ^ 2 * Uy y
  /-- **`Uy > 0` on the conditioned box** — the rank-block nondegeneracy (`det P₁ ≠ 0`), an
  EXPLICIT box hypothesis (the conditioned `box` pins the rank-block diagonal away from the pole),
  not a hidden full-box assumption (the all-small corner of the full box has `P₁ = 0`). -/
  hUpos : ∀ y ∈ Set.univ.pi (fun k : Fin n => box (p.succAbove k)), 0 < Uy y

/-! ## The `SmearedAchieverChart M` bundle (ε-independent maps + ε-indexed data) -/

/-- **A per-family BOUNDARY-SMEARED achiever chart for `M`** (the M-agnostic generalization of the
worked `(2,3,1)`/`(1,3,2)` chart bundles). Carries the conditioned-box L=2 smeared-divergence inputs
as an explicit hypothesis set, isolating the divergence ASSEMBLY (proven M-agnostically below) from
the chart CONSTRUCTION (the case-specific rational-shear ∘ radial blow-up at opaque widths).

The chart factors as `φ = ψ ∘ R` (the ε-independent maps): `ψ` the measure-preserving part (rational
shear ∘ linear reshape, NO pole obstruction), `R` the radial blow-up (the sole Jacobian carrier,
`|det D u| = |u p|^h`). The δ-dependent geometry (box, unit, containment, rate, positivity) is
supplied per-ε via `data`. -/
structure SmearedAchieverChart (M : Fin (L + 1) → ℕ) where
  /-- The peel dimension: `routeMAmbient M = n + 1` (the chart peels the pivot off the ambient). -/
  n : ℕ
  /-- The ambient-dimension peel equation. -/
  hN : routeMAmbient M = n + 1
  /-- The chart's measure-preserving part `ψ` (rational shear ∘ linear reshape). -/
  ψ : (Fin (routeMAmbient M) → ℝ) → (Fin (routeMAmbient M) → ℝ)
  /-- The radial blow-up `R` (the sole Jacobian carrier). -/
  R : (Fin (routeMAmbient M) → ℝ) → (Fin (routeMAmbient M) → ℝ)
  /-- The fderiv of `R`. -/
  D : (Fin (routeMAmbient M) → ℝ) → (Fin (routeMAmbient M) → ℝ) →L[ℝ] (Fin (routeMAmbient M) → ℝ)
  /-- The binding pivot axis (in the peeled `Fin (n+1)` coordinates). -/
  p : Fin (n + 1)
  /-- The radial Jacobian exponent (`= minAdm M − 1`, realised on the pivot axis). -/
  h : ℕ
  /-- `ψ` is measure-preserving (the rational shear is MP for any widths — no pole obstruction). -/
  hmp : MeasurePreserving ψ (volume : Measure (Fin (routeMAmbient M) → ℝ)) volume
  /-- `ψ` is a measurable embedding (total via the `a⁻¹ = 0` totalization). -/
  hemb : MeasurableEmbedding ψ
  /-- **The binding-axis exponent** `h − 2·(½·minAdm M) ≤ −1` (`h = minAdm M − 1`, `minAdm M ≥ 1`).
  At the achiever threshold `c' = ½·minAdm M` this is `h − minAdm = −1`; the assembly weakens it to
  any `c' ≥ ½·minAdm M`. -/
  hexp : (h : ℝ) - 2 * ((minAdm M : ℝ) / 2) ≤ -1
  /-- **The ε-indexed δ-dependent data** — for every `ε > 0`, the box radius + analytic inputs at
  that `ε` (the box radius adapts to `ε`). -/
  data : ∀ ε : ℝ, 0 < ε → SmearedChartData M n hN ψ R D p h ε

/-! ## The achiever box-divergence from the bundle (the REUSABLE M-agnostic core) -/

/-- **The BOUNDARY-SMEARED achiever box-divergence, from a chart bundle.** Given a
`SmearedAchieverChart M`, the achiever box integral `∫⁻_{cubeBox N ε} |routeMCore M|^{−c'} = ⊤` for
every `c' ≥ ½·minAdm M`, every `ε > 0`. A thin repackaging of `routeMCore_box_diverges_smearedL2`:
the chart's ε-indexed `data` supplies every per-family input, the exponent specialising from the
chart's `½·minAdm` field `hexp` to the caller's `c'` (since `c' ≥ ½·minAdm` only WEAKENS
`h − 2c' ≤ −1`). The assembly is M-agnostic; the only case-specific content is the chart bundle. -/
theorem routeMCore_box_diverges_of_smearedChart (M : Fin (L + 1) → ℕ)
    (W : SmearedAchieverChart M) (c' : NNReal) (hc' : (minAdm M : ℝ≥0∞) / 2 ≤ (c' : ℝ≥0∞))
    (ε : ℝ) (hε : 0 < ε) :
    ∫⁻ x in cubeBox (routeMAmbient M) ε,
      ENNReal.ofReal (|routeMCore M x| ^ (-(c' : ℝ))) = ⊤ := by
  -- `½·minAdm M ≤ (c' : ℝ)` (push the `ℝ≥0∞` bound down to `ℝ`)
  have hchalf : (minAdm M : ℝ) / 2 ≤ (c' : ℝ) := by
    have hcoe : ((minAdm M : ℝ) / 2 : ℝ) = (((minAdm M : ℝ≥0∞) / 2).toReal) := by
      rw [ENNReal.toReal_div]; simp
    rw [hcoe, show ((c' : ℝ)) = ((c' : ℝ≥0∞).toReal) from (ENNReal.coe_toReal c').symm]
    exact ENNReal.toReal_mono (by simp) hc'
  -- the chart's `hexp` (at `½·minAdm`) weakens to the caller's `c'`
  have hexp' : (W.h : ℝ) - 2 * (c' : ℝ) ≤ -1 := by
    have hmono : 2 * ((minAdm M : ℝ) / 2) ≤ 2 * (c' : ℝ) :=
      mul_le_mul_of_nonneg_left hchalf (by norm_num)
    have := W.hexp; linarith
  -- pull the δ-dependent data at this `ε`
  set d := W.data ε hε with hd
  exact routeMCore_box_diverges_smearedL2 (M := M) (n := W.n) W.hN W.ψ W.R W.D W.p d.box W.h
    (c' : ℝ) ε d.δ d.Uy d.hδ W.hmp W.hemb d.hSpre d.hRderiv d.hRinj d.hRdet d.hboxmeas
    d.hboxmeasAll d.hboxpos d.hUmeas hexp' d.hRate d.hUpos

/-! ## The spine wiring (`hSmeared` from a chart-builder) -/

/-- **The spine's `hSmeared`, from a chart BUILDER.** Given a builder producing a
`SmearedAchieverChart M` for every smeared `M`, the spine's `hSmeared` hypothesis holds: for `2 ≤ L`
and `BoundarySmeared M`, the achiever box integral diverges (`c' ≥ ½·minAdm M`, `ε > 0`). This is
exact shape `routeMCore_box_diverges_achiever_spine` consumes for its `hSmeared` slot — reducing the
SMEARED branch ∀M to "construct one `SmearedAchieverChart M`" per smeared family.

The `2 ≤ L` and `BoundarySmeared M` hypotheses are exactly the branch gate; the chart bundle absorbs
all the geometry. -/
theorem hSmeared_of_smearedChart (M : Fin (L + 1) → ℕ)
    (build : BoundarySmeared M → SmearedAchieverChart M)
    (c' : NNReal) (hc' : (minAdm M : ℝ≥0∞) / 2 ≤ (c' : ℝ≥0∞)) (ε : ℝ) (hε : 0 < ε) :
    (2 ≤ L) → BoundarySmeared M →
      ∫⁻ x in cubeBox (routeMAmbient M) ε,
        ENNReal.ofReal (|routeMCore M x| ^ (-(c' : ℝ))) = ⊤ :=
  fun _ hsm => routeMCore_box_diverges_of_smearedChart M (build hsm) c' hc' ε hε

/-! ## Non-vacuity: the `(2,3,1)` chart assembles into a `SmearedAchieverChart M231`

The bedrock companion: the structure's hypothesis bundle is jointly SATISFIABLE — by the worked
`(2,3,1)` chart (`RouteM231Smeared`: `psi231`/`R231`/`D231`, the conditioned `box231` shape). This
witnesses the abstraction is not vacuous and confirms the rational-pole transport closes end-to-end
through it: assembling the chart + firing `routeMCore_box_diverges_of_smearedChart` reproduces
`routeM231sm_box_diverges`. -/

/-- **The `(2,3,1)` δ-dependent chart data at `ε`** (`δ = min(ε/2, 1)`). Mirrors
`routeM231sm_box_diverges_via_condBox`: the conditioned `box231 δ` shape (rank-block diagonal pinned
in `[δ/2,δ]`, the rest in `[−δ/8,δ/8]`), the `z`-free unit `Uy231`, fed the banked `subBox231_*`
bounds via `condBox231_subset_subBox231` / `insertNth6_mem_subBox231`. -/
noncomputable def smearedChartData231 (ε : ℝ) (hε : 0 < ε) :
    SmearedChartData M231 8 (rfl : routeMAmbient M231 = 8 + 1) psi231 R231 D231
      (⟨6, by decide⟩ : Fin 9) 1 ε where
  δ := min (ε / 2) 1
  box := box231 (min (ε / 2) 1)
  Uy := Uy231
  hδ := lt_min (by linarith) (by norm_num)
  hSpre := by
    have hδ : 0 < min (ε / 2) 1 := lt_min (by linarith) (by norm_num)
    have hδ1 : min (ε / 2) 1 ≤ 1 := min_le_right _ _
    have h2δε : 2 * min (ε / 2) 1 ≤ ε := by
      have : min (ε / 2) 1 ≤ ε / 2 := min_le_left _ _; linarith
    intro u hu
    rw [Set.mem_preimage, ← phi231sm_eq_psi_R]
    exact cubeBox_mono h2δε (subBox231_subset_preimage hδ hδ1 (condBox231_subset_subBox231 _ hu))
  hRderiv := fun u _ => R231_hasFDerivWithinAt _ u
  hRinj := by
    have hsub : condBox (⟨6, by decide⟩ : Fin 9) (box231 (min (ε / 2) 1)) (min (ε / 2) 1)
        ⊆ subBox231 (min (ε / 2) 1) \ {x | x 6 = 0} := by
      intro u hu
      refine ⟨condBox231_subset_subBox231 _ hu, ?_⟩
      obtain ⟨hpiv, _⟩ := hu
      simp only [Set.mem_setOf_eq]; exact ne_of_gt (Set.mem_Ioo.mp hpiv).1
    exact (R231_injOn _).mono hsub
  hRdet := fun u _ => D231_abs_det u
  hboxmeas := fun k => measurableSet_box231 _ _
  hboxmeasAll := fun k => measurableSet_box231 _ _
  hboxpos := by
    rw [volume_pi_pi]
    refine CanonicallyOrderedAdd.prod_pos.mpr (fun k _ => ?_)
    have hδ : 0 < min (ε / 2) 1 := lt_min (by linarith) (by norm_num)
    simp only [box231]
    split <;> · rw [Real.volume_Icc, ENNReal.ofReal_pos]; linarith
  hUmeas := Uy231_measurable
  hRate := by
    have hδ : 0 < min (ε / 2) 1 := lt_min (by linarith) (by norm_num)
    intro z hz y hy
    have hmem := insertNth6_mem_subBox231 hz hy
    have hdet := subBox231_det_ne hδ hmem
    have h6eq : (⟨6, by decide⟩ : Fin 9) = (6 : Fin 9) := rfl
    change routeMCore M231 (psi231 (R231 (Fin.insertNth (6 : Fin 9) z y))) = z ^ 2 * Uy231 y
    rw [← phi231sm_eq_psi_R, routeMCore_phi231sm_offpole _ (by rwa [h6eq] at hdet)]
    rw [Uy231, h6eq, Uval231_insertNth_6 z y, Uval231_insertNth_6 0 y]
    simp only [Fin.insertNth_apply_same]
  hUpos := by
    have hδ : 0 < min (ε / 2) 1 := lt_min (by linarith) (by norm_num)
    have hδ1 : min (ε / 2) 1 ≤ 1 := min_le_right _ _
    intro y hy
    set δ : ℝ := min (ε / 2) 1
    rw [Uy231]
    have hmem : Fin.insertNth (⟨6, by decide⟩ : Fin 9) (δ / 2) y ∈ subBox231 δ :=
      insertNth6_mem_subBox231 (Set.mem_Ioo.mpr ⟨by linarith, by linarith⟩) hy
    rw [show Uval231 (Fin.insertNth (⟨6, by decide⟩ : Fin 9) (0:ℝ) y)
        = Uval231 (Fin.insertNth (⟨6, by decide⟩ : Fin 9) (δ / 2) y) from
      (Uval231_insertNth_6 0 y).trans (Uval231_insertNth_6 (δ / 2) y).symm]
    exact subBox231_U_pos hδ hδ1 hmem

/-- **The `(2,3,1)` chart bundle** (`SmearedAchieverChart M231`): the worked `(2,3,1)` chart
packaged into the M-agnostic structure. The ε-independent maps `psi231`/`R231`/`D231` (MP +
embedding + radial det `|u 6|¹`), the pivot `⟨6⟩`, radial exponent `1` (`= minAdm M231 − 1`), and
the per-ε `smearedChartData231`. Witnesses the bundle is jointly satisfiable. -/
noncomputable def smearedChart231 : SmearedAchieverChart M231 where
  n := 8
  hN := rfl
  ψ := psi231
  R := R231
  D := D231
  p := ⟨6, by decide⟩
  h := 1
  hmp := measurePreserving_psi231
  hemb := measurableEmbedding_psi231
  hexp := by
    rw [minAdm_M231]; push_cast; norm_num
  data := smearedChartData231

/-- **Non-vacuity end-to-end**: the M-agnostic `routeMCore_box_diverges_of_smearedChart` FIRES on
the worked `(2,3,1)` chart bundle `smearedChart231`, reproducing the achiever box-divergence
`∫⁻_{cubeBox 9 ε} |routeMCore M231|^{−c'} = ⊤` for `c' ≥ ½·minAdm M231 = 1`. The SMEARED assembly +
the rational-pole transport (the `(2,3,1)` Gram-minor pole in `ψ = Q ∘ shear`) close through the new
abstraction, axiom-clean. -/
theorem routeM231sm_box_diverges_via_smearedChart (c' : NNReal)
    (hc' : (minAdm M231 : ℝ≥0∞) / 2 ≤ (c' : ℝ≥0∞)) (ε : ℝ) (hε : 0 < ε) :
    ∫⁻ x in cubeBox (routeMAmbient M231) ε,
      ENNReal.ofReal (|routeMCore M231 x| ^ (-(c' : ℝ))) = ⊤ :=
  routeMCore_box_diverges_of_smearedChart M231 smearedChart231 c' hc' ε hε

end DLNFibre.DLN.RLCT
