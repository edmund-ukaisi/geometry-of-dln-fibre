import DLNFibre.DLN.RLCT.Validate.RouteMLayerValue
import DLNFibre.DLN.RLCT.Validate.RouteMCoverLemmas

/-!
# `DLNFibre.DLN.RLCT.Validate.RouteMLayerCover` — the general-M layer-family cover (R1.6, the LOWER bound)

The genuine resolution-of-singularities geometry for the R1 gate: the general-M `IsRouteMCover` over
the layer-collapsing chart family `routeLayerAtlas M`. The R1 gate (`resolution_charts`) is reduced —
by `resolution_charts_of_layerCover` (`RouteMLayerValue.lean`) — to EXACTLY this cover; closing it here
closes the gate.

`IsRouteMCover` has five fields. This file banks the THREE structural fields for general `M` (proven,
reusable) and the ONE genuinely-general analytic atom of the finiteness leg (`cover_le`'s RHS positivity),
then reduces the full cover to the two remaining analytic atoms via a sorry-free `IsRouteMCover` ASSEMBLY
(`routeMLayerCover_of_atoms`). The two residual atoms are pinned to the precise layer family.

## What this banks (sorry-free)

- `layerCover_Fmeas` / `layerCover_Uopen` / `layerCover_Umem` — the three structural fields for general
  `M`, from `measurable_routeMCore` / `isOpen_routeMBaseNbhd` / `mem_routeMBaseNbhd_zero`
  (`RouteMExtraction.lean`). No geometry — banked for any `M`.
- `monomialIntegrand_pos_on_interior` — the leaf integrand is `> 0` on the open interior `(0,1)^d` of the
  unit box, for ANY `(d, k, h, c')`. The per-leaf positivity the `cover_le` RHS-positivity rides
  (generalizes the `(2,2,2)`-specific `routeM222_rhs_ne_zero`).
- `layerCover_rhs_ne_zero` — the leaf-sum RHS `≠ 0` for the layer family, for general `M` (the easy half
  of `cover_le`, fully discharged here). Via `monomialIntegrand_pos_on_interior` on ANY leaf's
  positive-measure interior box (the family is `Nonempty`; one positive term suffices).
- `routeMLayerCover_of_atoms` — the `IsRouteMCover` ASSEMBLY: given the two residual analytic atoms
  (`hfin` below-threshold finiteness, `hdiv` ε-uniform box divergence) for `routeMCore M` over the layer
  family, the full `IsRouteMCover` holds. The three structural fields + the RHS positivity are supplied
  here; only the two genuine resolution atoms remain. This pins the residual to the EXACT obligation a
  general-M resolution-of-singularities argument must discharge (no interface drift).

## The residual (NOT closed — the genuine R1.6 mountain; honest blocker)

The two analytic atoms `hfin` / `hdiv` are the LOWER-bound resolution geometry. They are NOT discharged
here — and the `(2,2,2)` template does NOT generalize directly (validated assessment + decorrelated
Codex, 2026-06-24):

- `hdiv` (box divergence, the lower bound): the `(2,2,2)` proof used ONE explicit composite blow-up
  chart `phiUnit` whose pulled-back loss factored as `monomial · unit`. That factorization is a depth-2
  miracle: for `L > 1` the loss is a product of many matrices and the Jacobian tower ceases to be
  triangular after the first pivot, so the pulled-back loss does NOT factor cleanly as `monomial · unit`.
  The PROVEN general machinery is instead the per-node SQUEEZE `rlctAtOn = nReg/2 + rlctAtOn(reduced)`
  (`schur_recursion_step_squeeze` + `rlctAtOn_layerReduced_transport`) — but that computes `rlctAtOn`
  DIRECTLY (an additive recursion), NOT the box-integral `= ⊤` fact `IsRouteMCover.cover_ge_div` demands.
  The squeeze is the wrong SHAPE for this field: lifting `rlctAtOn`-divergence to box-integral divergence
  along the achiever path is the open transcription, and the single-path squeeze alone does NOT give the
  lower bound (the MIN over branches — no branch gives a smaller value — is the missing content).

- `hfin` (below-threshold finiteness, the upper bound): the `(2,2,2)` proof iterated `recStep`
  (pivot-blow-up split) into explicit per-summand finiteness. The general obstruction is COMPLETENESS —
  proving the recursively-generated pivot charts COVER the box `(−1,1)^N` up to a null set (the "no
  missing strata" combinatorial cover). Iterating `recStep` does not package this automatically.

So the genuine open content is the SQUEEZE-to-box-integral bridge (lower bound) + the measurable-cover
completeness (upper bound). Both are stated precisely as the hypotheses of `routeMLayerCover_of_atoms`.
-/

open MeasureTheory
open scoped ENNReal BigOperators

namespace DLNFibre.DLN.RLCT

variable {L : ℕ}

/-! ## The three structural fields for general `M` (banked, no geometry) -/

/-- **`Fmeas` for general `M`.** `routeMCore M` is measurable (the DLN loss in flat coordinates is
continuous ⟹ measurable). The `IsRouteMCover.Fmeas` field. -/
theorem layerCover_Fmeas (M : Fin (L + 1) → ℕ) : Measurable (routeMCore M) :=
  measurable_routeMCore M

/-- **`Uopen` for general `M`.** `routeMBaseNbhd M = (−1,1)^N` is open. The `IsRouteMCover.Uopen` field. -/
theorem layerCover_Uopen (M : Fin (L + 1) → ℕ) : IsOpen (routeMBaseNbhd M) :=
  isOpen_routeMBaseNbhd M

/-- **`Umem` for general `M`.** `0 ∈ routeMBaseNbhd M` (the deepest flat point is in the box). The
`IsRouteMCover.Umem` field. -/
theorem layerCover_Umem (M : Fin (L + 1) → ℕ) :
    (0 : Fin (routeMAmbient M) → ℝ) ∈ routeMBaseNbhd M :=
  mem_routeMBaseNbhd_zero M

/-! ## The general leaf-integrand interior positivity (the `cover_le` RHS-positivity atom) -/

/-- **The leaf integrand is positive on the open interior `(0,1)^d`** (for ANY `d, k, h, c'`). On the
interior every `|uⱼ| > 0`, so the Jacobian monomial `∏|uⱼ|^{hⱼ} > 0` and the loss-base `rpow` factor
`(∏|uⱼ|^{2kⱼ})^{−c'} > 0`, so their product is `> 0`. The general per-leaf positivity behind the
`cover_le` RHS `≠ 0` (generalizes the `(2,2,2)`-specific `routeM222_rhs_ne_zero` interior argument). -/
theorem monomialIntegrand_pos_on_interior (d : ℕ) (k h : Fin d → ℕ) (c' : ℝ)
    {u : Fin d → ℝ} (hu : ∀ j, 0 < |u j|) :
    0 < monomialIntegrand d k h c' u := by
  unfold monomialIntegrand
  exact mul_pos (Finset.prod_pos (fun j _ => pow_pos (hu j) _))
    (Real.rpow_pos_of_pos (Finset.prod_pos (fun j _ => pow_pos (hu j) _)) _)

/-- **The leaf-sum RHS is `≠ 0` for the layer family** (general `M`, the easy half of `cover_le`). The
`∑` over leaves of the per-leaf `unitBox` integral of `ofReal (monomialIntegrand …)` is nonzero: pick any
leaf `i₀` (the family is `Nonempty`), and on the positive-measure interior box `(1/2,1)^d` the integrand
is `> 0` (`monomialIntegrand_pos_on_interior`), so that leaf's integral is `> 0`, hence the sum is.
(Generalizes `routeM222_rhs_ne_zero` off the single-leaf `Fin 1` collapse to the general `Fintype` sum.) -/
theorem layerCover_rhs_ne_zero (M : Fin (L + 1) → ℕ) (c' : NNReal) :
    (∑ i : (routeLayerAtlas M).ι, ∫⁻ y in unitBox (layerD M i),
        ENNReal.ofReal (monomialIntegrand (layerD M i) (layerK M i) (layerH M i) (c' : ℝ) y)) ≠ 0 := by
  -- pick a leaf i₀ and show its integral is > 0; the sum then is ≠ 0.
  obtain ⟨i₀⟩ := (routeLayerAtlas M).nonempty
  set d := layerD M i₀ with hd
  set f := fun y => ENNReal.ofReal (monomialIntegrand d (layerK M i₀) (layerH M i₀) (c' : ℝ) y) with hf
  have hmeas : Measurable f := by
    rw [hf]; exact ENNReal.measurable_ofReal.comp (by unfold monomialIntegrand; fun_prop)
  -- the interior box `S = (1/2,1)^d ⊆ unitBox d`, positive measure, integrand > 0 on it.
  set S : Set (Fin d → ℝ) := Set.univ.pi (fun _ => Set.Ioo (1/2 : ℝ) 1) with hS
  have hSsub : S ⊆ unitBox d := fun x hx i _ => by
    have := hx i (Set.mem_univ i); simp only [Set.mem_Ioo] at this
    simp only [Set.mem_Icc]; exact ⟨by linarith [this.1], by linarith [this.2]⟩
  have hSpos : 0 < volume S := by
    rw [hS, Real.volume_pi_Ioo]
    refine CanonicallyOrderedAdd.prod_pos.2 (fun _ _ => ?_)
    rw [ENNReal.ofReal_pos]; norm_num
  have hsupp : S ⊆ Function.support f := by
    intro x hx
    rw [Function.mem_support, hf]
    simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    have hxpos : ∀ j, (0 : ℝ) < |x j| := by
      intro j
      have := hx j (Set.mem_univ j); simp only [Set.mem_Ioo] at this
      rw [abs_of_pos (by linarith [this.1])]; linarith [this.1]
    exact monomialIntegrand_pos_on_interior d (layerK M i₀) (layerH M i₀) (c' : ℝ) hxpos
  have hi₀pos : (0 : ℝ≥0∞) < ∫⁻ y in unitBox d, f y := by
    rw [setLIntegral_pos_iff hmeas]
    exact lt_of_lt_of_le hSpos (measure_mono (fun x hx => ⟨hsupp hx, hSsub hx⟩))
  -- the i₀ term is positive, so the sum is positive, hence ≠ 0.
  refine pos_iff_ne_zero.1 ?_
  refine lt_of_lt_of_le hi₀pos ?_
  exact Finset.single_le_sum (f := fun i => ∫⁻ y in unitBox (layerD M i),
      ENNReal.ofReal (monomialIntegrand (layerD M i) (layerK M i) (layerH M i) (c' : ℝ) y))
    (fun i _ => zero_le _) (Finset.mem_univ i₀)

/-! ## The `IsRouteMCover` assembly from the two residual analytic atoms (sorry-free reduction)

The full cover, reduced to EXACTLY the two genuine resolution-of-singularities atoms — the three
structural fields + the `cover_le` RHS positivity are discharged above; the residual is the finiteness
atom (`hfin`, the upper bound) and the box-divergence atom (`hdiv`, the lower bound), each pinned to the
precise `routeMCore M` / layer-family `(d, k, h)`. This is the SAME shape `routeM_coverLe_of_finiteness`
/ `routeM_coverGeDiv_of_boxDiverges` consume; this theorem assembles them into the `Prop` the bridge needs.
-/

/-- **The general-M `IsRouteMCover` from the two analytic atoms.** Given (a) below-threshold finiteness
`hfin` — whenever the layer leaf-sum is finite, `∫⁻_{routeMBaseNbhd} |routeMCore|^{−c'} < ⊤` — and (b) the
ε-uniform box divergence `hdiv` — for `c'` at-or-above some leaf threshold, `∫⁻_{cubeBox N ε}
|routeMCore|^{−c'} = ⊤` for all `ε > 0` — the general-M `IsRouteMCover` over the layer family holds.
The three structural fields (`Fmeas`/`Uopen`/`Umem`) and the `cover_le` RHS positivity are supplied here;
`hfin` rides `routeM_coverLe_of_finiteness`, `hdiv` rides `routeM_coverGeDiv_of_boxDiverges`. The two atoms
are the genuine R1.6 resolution geometry (NOT discharged — the honest residual; see the file header). -/
theorem routeMLayerCover_of_atoms (M : Fin (L + 1) → ℕ)
    (hfin : ∀ c' : NNReal,
      (∑ i : (routeLayerAtlas M).ι, ∫⁻ y in unitBox (layerD M i),
          ENNReal.ofReal (monomialIntegrand (layerD M i) (layerK M i) (layerH M i) (c' : ℝ) y)) < ⊤ →
      ∫⁻ x in routeMBaseNbhd M, ENNReal.ofReal (|routeMCore M x| ^ (-(c' : ℝ))) < ⊤)
    (hdiv : ∀ c' : NNReal,
      (∃ i : (routeLayerAtlas M).ι,
        monomialThreshold (layerD M i) (layerK M i) (layerH M i) ≤ (c' : ℝ≥0∞)) →
      ∀ ε > 0, ∫⁻ x in cubeBox (routeMAmbient M) ε,
        ENNReal.ofReal (|routeMCore M x| ^ (-(c' : ℝ))) = ⊤) :
    IsRouteMCover (routeMCore M) (routeMBaseNbhd M) (routeLayerAtlas M).ι
      (layerD M) (layerK M) (layerH M) where
  Fmeas := layerCover_Fmeas M
  Uopen := layerCover_Uopen M
  Umem := layerCover_Umem M
  cover_le :=
    routeM_coverLe_of_finiteness (routeMCore M) (routeMBaseNbhd M) (layerD M) (layerK M) (layerH M)
      (layerCover_rhs_ne_zero M) hfin
  cover_ge_div :=
    routeM_coverGeDiv_of_boxDiverges (routeMCore M) (layerD M) (layerK M) (layerH M) hdiv

end DLNFibre.DLN.RLCT
