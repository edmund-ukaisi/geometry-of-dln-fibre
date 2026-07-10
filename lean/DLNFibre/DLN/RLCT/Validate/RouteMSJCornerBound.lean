import DLNFibre.DLN.RLCT.Validate.RouteMSJRadialPolar

/-!
# `DLNFibre.DLN.RLCT.Validate.RouteMSJCornerBound` — the uniform-in-parameters corner endpoint bound

**Thread `genm-covmount`, Stage 2 (S,J) CoV mountain.** The banked corner endpoint
`corner_block_lintegral_lt_top` (`RouteMSJRadialPolar`) gives only `∫ < ⊤`. But the `(S,J)` descent
integrates the endpoint's value over the bounded ENVIRONMENT (the pivots + deep factor, which enter
the resolved loss as bounded parameters), and a bare `< ⊤` does not integrate. This module extracts
the EXPLICIT bound the polar blow-up already produces:

    ∫⁻ z in closedBall 0 R, (g z)^{−c'}  ≤  a^{−c'} · cornerRadialConst N R c',

with `a` the uniform sphere lower bound. The constant `cornerRadialConst N R c'` (the radial power
integral × the sphere surface measure) is `< ⊤` below the threshold `c' < N/2` and is INDEPENDENT
of the loss `g` — so on a good sub-cover where `a ≥ a₀ > 0` and the block sits in a FIXED ball
`R ≤ R₀`, the inner endpoint value is uniformly `≤ a₀^{−c'} · cornerRadialConst N R₀ c'`, a constant
integrable over the finite-measure environment box. This is the step the assembly certificate
underspecifies (the `domain control` gloss) and the concrete blocker for the environment integral.

Same proof as `corner_block_lintegral_lt_top` up to the `key` monomial domination; the divergence is
only the final step: `le_trans (lintegral_mono key)` + `lintegral_const` land the explicit product
instead of discarding it into `< ⊤`.

Axiom-clean `[propext, Classical.choice, Quot.sound]` (pure real analysis; no `monomial_rlct`).
-/

namespace DLNFibre.DLN.RLCT

open MeasureTheory Set Metric
open scoped ENNReal

/-- **The corner endpoint radial constant** `(∫₀^R r^{N-1-2c'} dr) · μ_sphere(univ)` — the loss-free
factor of the polar blow-up bound. Finite below the threshold `c' < N/2`
(`cornerRadialConst_lt_top`);
the sphere surface measure `(volume).toSphere` is finite. -/
noncomputable def cornerRadialConst (N : ℕ) (R c' : ℝ) : ℝ≥0∞ :=
  (∫⁻ r in Set.Ioc (0 : ℝ) R, ENNReal.ofReal (r ^ ((N : ℝ) - 1 - 2 * c')))
    * ((volume : Measure (EuclideanSpace ℝ (Fin N))).toSphere Set.univ)

/-- The corner endpoint radial constant is finite below the pole `c' < N/2`. -/
theorem cornerRadialConst_lt_top (N : ℕ) [NeZero N] (R c' : ℝ) (hc' : c' < (N : ℝ) / 2) :
    cornerRadialConst N R c' < ⊤ := by
  have hp : -1 < (N : ℝ) - 1 - 2 * c' := by linarith
  exact ENNReal.mul_lt_top (lintegral_Ioc_rpow_lt_top hp) (measure_lt_top _ _)

/-- **The corner-block endpoint, with the EXPLICIT uniform bound.** For a measurable
degree-2-homogeneous loss `g` with `a ≤ g` on the unit sphere (`a > 0`) and `c' < N/2`, the ball
integral of the loss power is bounded by `a^{−c'} · cornerRadialConst N R c'` — the polar blow-up
bound made explicit (the banked `corner_block_lintegral_lt_top` discards this into `< ⊤`). The
bound's dependence on the loss is ONLY through the sphere lower bound `a`; the constant is
loss-free, so uniform across a family of losses sharing an `a`-lower-bound and a radius. Proof:
mirror `corner_block_lintegral_lt_top` to the monomial domination `key`, then `lintegral_mono` +
`lintegral_const` land the product (no `< ⊤` discard). -/
theorem corner_block_lintegral_le {N : ℕ} [NeZero N] {R : ℝ}
    (g : EuclideanSpace ℝ (Fin N) → ℝ) (hg : Measurable g)
    (hom : ∀ (r : ℝ) (x : EuclideanSpace ℝ (Fin N)), g (r • x) = r ^ 2 * g x)
    (c' : ℝ) (hc0 : 0 ≤ c') (hc' : c' < (N : ℝ) / 2) (a : ℝ) (ha : 0 < a)
    (hlb : ∀ ω : sphere (0 : EuclideanSpace ℝ (Fin N)) 1, a ≤ g (ω : EuclideanSpace ℝ (Fin N))) :
    ∫⁻ z in Metric.closedBall (0 : EuclideanSpace ℝ (Fin N)) R,
        ENNReal.ofReal ((g z) ^ (-c'))
      ≤ ENNReal.ofReal (a ^ (-c')) * cornerRadialConst N R c' := by
  have hNpos : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  have hcast : ((N - 1 : ℕ) : ℝ) = (N : ℝ) - 1 := by
    rw [Nat.cast_sub hNpos, Nat.cast_one]
  set p : ℝ := ((N : ℝ) - 1) - 2 * c' with hp_def
  have hp : -1 < p := by rw [hp_def]; linarith [hc']
  have hφmeas : Measurable (fun t : ℝ => t ^ (-c')) := by fun_prop
  rw [lintegral_ball_radial_polar_factor g hg hom (fun t => t ^ (-c')) hφmeas]
  -- inner bound: for each sphere direction, dominate by the separated monomial (verbatim `key`)
  have key : ∀ ω : sphere (0 : EuclideanSpace ℝ (Fin N)) 1,
      (∫⁻ r in Ioc (0 : ℝ) R,
          ENNReal.ofReal (r ^ (N - 1))
            * ENNReal.ofReal ((r ^ 2 * g (ω : EuclideanSpace ℝ (Fin N))) ^ (-c')))
        ≤ ENNReal.ofReal (a ^ (-c')) * ∫⁻ r in Ioc (0 : ℝ) R, ENNReal.ofReal (r ^ p) := by
    intro ω
    rw [← lintegral_const_mul' (ENNReal.ofReal (a ^ (-c'))) _ ENNReal.ofReal_ne_top]
    refine setLIntegral_mono' measurableSet_Ioc (fun r hr => ?_)
    have hr0 : 0 < r := hr.1
    have hgω : a ≤ g (ω : EuclideanSpace ℝ (Fin N)) := hlb ω
    have hr2a : 0 < r ^ 2 * a := by positivity
    have hr2ge : r ^ 2 * a ≤ r ^ 2 * g (ω : EuclideanSpace ℝ (Fin N)) :=
      mul_le_mul_of_nonneg_left hgω (by positivity)
    have hanti : (r ^ 2 * g (ω : EuclideanSpace ℝ (Fin N))) ^ (-c') ≤ (r ^ 2 * a) ^ (-c') :=
      Real.rpow_le_rpow_of_nonpos hr2a hr2ge (neg_nonpos.mpr hc0)
    have hsplit : (r ^ 2 * a) ^ (-c') = (r ^ 2 : ℝ) ^ (-c') * a ^ (-c') :=
      Real.mul_rpow (by positivity) ha.le
    have hpow : r ^ (N - 1) * (r ^ 2 : ℝ) ^ (-c') = r ^ p := by
      rw [show (r : ℝ) ^ (N - 1) = r ^ (((N - 1 : ℕ) : ℝ)) from (Real.rpow_natCast r (N - 1)).symm,
        show (r ^ 2 : ℝ) = r ^ ((2 : ℕ) : ℝ) from (Real.rpow_natCast r 2).symm,
        ← Real.rpow_mul hr0.le, ← Real.rpow_add hr0]
      congr 1
      rw [hcast, hp_def]; push_cast; ring
    have hreal : r ^ (N - 1) * (r ^ 2 * g (ω : EuclideanSpace ℝ (Fin N))) ^ (-c')
        ≤ a ^ (-c') * r ^ p := by
      calc r ^ (N - 1) * (r ^ 2 * g (ω : EuclideanSpace ℝ (Fin N))) ^ (-c')
          ≤ r ^ (N - 1) * (r ^ 2 * a) ^ (-c') :=
            mul_le_mul_of_nonneg_left hanti (by positivity)
        _ = r ^ (N - 1) * ((r ^ 2 : ℝ) ^ (-c') * a ^ (-c')) := by rw [hsplit]
        _ = a ^ (-c') * (r ^ (N - 1) * (r ^ 2 : ℝ) ^ (-c')) := by ring
        _ = a ^ (-c') * r ^ p := by rw [hpow]
    calc ENNReal.ofReal (r ^ (N - 1))
            * ENNReal.ofReal ((r ^ 2 * g (ω : EuclideanSpace ℝ (Fin N))) ^ (-c'))
        = ENNReal.ofReal (r ^ (N - 1) * (r ^ 2 * g (ω : EuclideanSpace ℝ (Fin N))) ^ (-c')) :=
          (ENNReal.ofReal_mul (by positivity)).symm
      _ ≤ ENNReal.ofReal (a ^ (-c') * r ^ p) := ENNReal.ofReal_le_ofReal hreal
      _ = ENNReal.ofReal (a ^ (-c')) * ENNReal.ofReal (r ^ p) :=
          ENNReal.ofReal_mul (by positivity)
  refine le_trans (lintegral_mono key) ?_
  rw [lintegral_const, cornerRadialConst, ← mul_assoc, hp_def]

/-- **Consistency / non-vacuity witness.** The explicit bound re-proves the banked corner endpoint
finiteness `corner_block_lintegral_lt_top`: the bound `a^{−c'} · cornerRadialConst N R c'` is a
product of two finite factors below the threshold. Confirms the bound is neither vacuous nor weaker
than the
banked `< ⊤`. -/
theorem corner_block_lt_top_of_bound {N : ℕ} [NeZero N] {R : ℝ}
    (g : EuclideanSpace ℝ (Fin N) → ℝ) (hg : Measurable g)
    (hom : ∀ (r : ℝ) (x : EuclideanSpace ℝ (Fin N)), g (r • x) = r ^ 2 * g x)
    (c' : ℝ) (hc0 : 0 ≤ c') (hc' : c' < (N : ℝ) / 2) (a : ℝ) (ha : 0 < a)
    (hlb : ∀ ω : sphere (0 : EuclideanSpace ℝ (Fin N)) 1, a ≤ g (ω : EuclideanSpace ℝ (Fin N))) :
    ∫⁻ z in Metric.closedBall (0 : EuclideanSpace ℝ (Fin N)) R,
        ENNReal.ofReal ((g z) ^ (-c')) < ⊤ :=
  lt_of_le_of_lt (corner_block_lintegral_le g hg hom c' hc0 hc' a ha hlb)
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (cornerRadialConst_lt_top N R c' hc'))

end DLNFibre.DLN.RLCT
