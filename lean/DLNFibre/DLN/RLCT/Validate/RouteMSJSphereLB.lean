import DLNFibre.DLN.RLCT.Validate.RouteMSJCornerBound

/-!
# `DLNFibre.DLN.RLCT.Validate.RouteMSJSphereLB` — the §8 uniform sphere lower bound

**Thread `genm-covmount`, Stage 2 (S,J) CoV mountain, step 2.** The corner endpoint
`corner_block_lintegral_le` (`RouteMSJCornerBound`) needs a UNIFORM sphere lower bound `a ≤ g`
(`a > 0`), but the natural good-chart hypothesis is only POINTWISE positivity `0 < g ω` on the
sphere (`sjGoodMap`'s `sjGoodMap_loss_pos`). We bridge the two by the extreme-value theorem: a
continuous function strictly positive on the compact unit sphere has a uniform positive lower bound
(`IsCompact.exists_forall_le'`). This is the vslice §8 unit-boundedness gate in its bounded,
network-free form (the certificate calls it "genuinely-new but not a wall").

* **`exists_uniform_sphere_lb`** — the extreme-value bridge: continuous + pointwise-positive on the
  unit sphere ⟹ a uniform positive lower bound.
* **`corner_block_lintegral_le_of_pos`** — the corner endpoint with the uniform bound derived
  internally from pointwise positivity: `∃ a > 0, ∫_{ball R} g^{−c'} ≤ a^{−c'}·cornerRadialConst`.
* **`corner_block_lt_top_of_pos`** — the finiteness form taking ONLY pointwise sphere positivity (no
  supplied `a`), the convenient shape the good-chart resolution produces.

Axiom-clean `[propext, Classical.choice, Quot.sound]` (extreme-value theorem + the banked bound).
-/

namespace DLNFibre.DLN.RLCT

open MeasureTheory Metric
open scoped ENNReal

/-- **The uniform sphere lower bound (extreme-value bridge).** A continuous function strictly
positive on the unit sphere of `EuclideanSpace ℝ (Fin N)` (compact, the space being proper) has a
uniform
positive lower bound: `∃ a > 0, ∀ ω ∈ sphere, a ≤ g ω`. The extreme value theorem
`IsCompact.exists_forall_le'` at the threshold `0`. -/
theorem exists_uniform_sphere_lb {N : ℕ} (g : EuclideanSpace ℝ (Fin N) → ℝ) (hg : Continuous g)
    (hpos : ∀ ω : sphere (0 : EuclideanSpace ℝ (Fin N)) 1, 0 < g (ω : EuclideanSpace ℝ (Fin N))) :
    ∃ a : ℝ, 0 < a ∧ ∀ ω : sphere (0 : EuclideanSpace ℝ (Fin N)) 1,
      a ≤ g (ω : EuclideanSpace ℝ (Fin N)) := by
  obtain ⟨a, ha0, hle⟩ := (isCompact_sphere (0 : EuclideanSpace ℝ (Fin N)) 1).exists_forall_le'
    hg.continuousOn (a := 0) (fun b hb => hpos ⟨b, hb⟩)
  exact ⟨a, ha0, fun ω => hle (ω : EuclideanSpace ℝ (Fin N)) ω.2⟩

/-- **The corner endpoint with the uniform bound from pointwise positivity.** For a continuous
degree-2-homogeneous loss `g` strictly positive on the unit sphere and `c' < N/2`, there is a
positive `a` with `∫_{ball R} g^{−c'} ≤ a^{−c'}·cornerRadialConst N R c'`. Derives the uniform lower
bound
(`exists_uniform_sphere_lb`) and feeds it to `corner_block_lintegral_le`. -/
theorem corner_block_lintegral_le_of_pos {N : ℕ} [NeZero N] {R : ℝ}
    (g : EuclideanSpace ℝ (Fin N) → ℝ) (hg : Measurable g) (hgc : Continuous g)
    (hom : ∀ (r : ℝ) (x : EuclideanSpace ℝ (Fin N)), g (r • x) = r ^ 2 * g x)
    (c' : ℝ) (hc0 : 0 ≤ c') (hc' : c' < (N : ℝ) / 2)
    (hpos : ∀ ω : sphere (0 : EuclideanSpace ℝ (Fin N)) 1, 0 < g (ω : EuclideanSpace ℝ (Fin N))) :
    ∃ a : ℝ, 0 < a ∧
      ∫⁻ z in Metric.closedBall (0 : EuclideanSpace ℝ (Fin N)) R,
          ENNReal.ofReal ((g z) ^ (-c'))
        ≤ ENNReal.ofReal (a ^ (-c')) * cornerRadialConst N R c' := by
  obtain ⟨a, ha, hlb⟩ := exists_uniform_sphere_lb g hgc hpos
  exact ⟨a, ha, corner_block_lintegral_le g hg hom c' hc0 hc' a ha hlb⟩

/-- **The corner endpoint finiteness from pointwise positivity only.** A continuous
degree-2-homogeneous loss strictly positive on the unit sphere has finite ball integral below the
threshold `c' < N/2` — no supplied uniform lower bound `a` (it is derived by the extreme-value
theorem). The convenient shape the good-chart resolution produces. -/
theorem corner_block_lt_top_of_pos {N : ℕ} [NeZero N] {R : ℝ}
    (g : EuclideanSpace ℝ (Fin N) → ℝ) (hg : Measurable g) (hgc : Continuous g)
    (hom : ∀ (r : ℝ) (x : EuclideanSpace ℝ (Fin N)), g (r • x) = r ^ 2 * g x)
    (c' : ℝ) (hc0 : 0 ≤ c') (hc' : c' < (N : ℝ) / 2)
    (hpos : ∀ ω : sphere (0 : EuclideanSpace ℝ (Fin N)) 1, 0 < g (ω : EuclideanSpace ℝ (Fin N))) :
    ∫⁻ z in Metric.closedBall (0 : EuclideanSpace ℝ (Fin N)) R,
        ENNReal.ofReal ((g z) ^ (-c')) < ⊤ := by
  obtain ⟨a, ha, hle⟩ := corner_block_lintegral_le_of_pos g hg hgc hom c' hc0 hc' hpos
  exact lt_of_le_of_lt hle
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (cornerRadialConst_lt_top N R c' hc'))

end DLNFibre.DLN.RLCT
