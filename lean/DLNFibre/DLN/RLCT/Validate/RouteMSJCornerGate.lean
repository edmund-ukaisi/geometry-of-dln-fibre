import DLNFibre.DLN.RLCT.Validate.RouteMSJCornerLoss

/-!
# `DLNFibre.DLN.RLCT.Validate.RouteMSJCornerGate` — the §8 unit-boundedness gate (compactness form)

**Thread `genm-l2prod`, Stage 2 (S,J) production.** The banked corner-block finiteness
`corner_block_cube_lintegral_lt_top` (`RouteMSJRadialPolar`) consumes a PRE-EXTRACTED lower-bound
triple `(a, ha, hlb)` — a value `a > 0` with `a ≤ g (ofLp ω)` at every unit-sphere direction. In the
`(S,J)` resolution (vslice cert §8; jbassembly cert §3a) that lower bound is produced by
**continuity + compactness**: the resolved corner loss `g` is continuous and strictly positive on
the (compact) unit sphere on the good chart, so it attains a positive minimum there.

This module isolates that gate, network-free:

* **`exists_pos_lower_bound_on_sphere`** — a continuous `g : (Fin n → ℝ) → ℝ` strictly positive at
  every unit-sphere direction `ofLp ω` has a uniform `a > 0` with `a ≤ g (ofLp ω)` for all `ω`. The
  extreme value theorem on the compact sphere (`IsCompact.exists_forall_le'`, `isCompact_sphere`).
* **`corner_block_cube_lintegral_lt_top_of_pos`** — the corner-block finiteness with the §8 gate
  discharged by the natural hypothesis `0 < g (ofLp ω)` on the sphere (continuity supplied), rather
  than the pre-extracted `(a, ha, hlb)`. The endpoint the good-chart resolution calls.

S2-FREE (no `monomial_rlct`, no `cited_aoyagi_dln`); axiom-clean `[propext, Classical.choice,
Quot.sound]`.
-/

namespace DLNFibre.DLN.RLCT

open MeasureTheory Set Metric
open scoped ENNReal

/-- **§8 gate — a continuous loss positive on the unit sphere has a positive lower bound there.**
For `g : (Fin n → ℝ) → ℝ` continuous and strictly positive at every unit-sphere direction `ofLp ω`
(`ω` in the Euclidean unit sphere), the extreme value theorem on the compact sphere produces a
uniform `a > 0` with `a ≤ g (ofLp ω)` for all `ω`. This is the continuity+compactness
positive-minimum (vslice §8 / jbassembly §3a) that turns the `g > 0`-on-sphere locus into the
`corner_block_cube_lintegral_lt_top` endpoint's pre-extracted lower-bound triple `(a, ha, hlb)`.
`IsCompact.exists_forall_le'` also handles `n = 0` (empty sphere) uniformly. -/
theorem exists_pos_lower_bound_on_sphere {n : ℕ} (g : (Fin n → ℝ) → ℝ) (hg : Continuous g)
    (hpos : ∀ ω : sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
        0 < g (WithLp.ofLp (ω : EuclideanSpace ℝ (Fin n)))) :
    ∃ a : ℝ, 0 < a ∧ ∀ ω : sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
        a ≤ g (WithLp.ofLp (ω : EuclideanSpace ℝ (Fin n))) := by
  have hcompact : IsCompact (sphere (0 : EuclideanSpace ℝ (Fin n)) 1) := isCompact_sphere _ _
  have hof : Continuous (WithLp.ofLp : EuclideanSpace ℝ (Fin n) → (Fin n → ℝ)) := by fun_prop
  have hcont : Continuous (fun ω : EuclideanSpace ℝ (Fin n) => g (WithLp.ofLp ω)) := hg.comp hof
  have hpos' : ∀ b ∈ sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
      (0 : ℝ) < g (WithLp.ofLp b) := fun b hb => hpos ⟨b, hb⟩
  obtain ⟨a, ha, hforall⟩ := hcompact.exists_forall_le' hcont.continuousOn hpos'
  exact ⟨a, ha, fun ω => hforall (ω : EuclideanSpace ℝ (Fin n)) ω.2⟩

/-- **The corner-block finiteness with the §8 gate discharged by positivity + continuity.** A
cleaner caller interface for `corner_block_cube_lintegral_lt_top`: instead of the pre-extracted
lower-bound triple `(a, ha, hlb)`, it consumes the natural hypothesis that the (continuous,
degree-2-homogeneous) loss `g` is strictly positive at every unit-sphere direction `ofLp ω`. The
uniform positive lower
bound is supplied internally by `exists_pos_lower_bound_on_sphere` (extreme value theorem on the
compact sphere). This is the endpoint the good-chart `(S,J)` resolution calls: `c' < n/2` (the SUM
threshold `Mval/2`), `g` the resolved cross-coupled corner loss, positive on the good chart. -/
theorem corner_block_cube_lintegral_lt_top_of_pos {n : ℕ} [NeZero n]
    (g : (Fin n → ℝ) → ℝ) (hgc : Continuous g)
    (hom : ∀ (r : ℝ) (x : Fin n → ℝ), g (r • x) = r ^ 2 * g x)
    (c' : ℝ) (hc0 : 0 ≤ c') (hc' : c' < (n : ℝ) / 2)
    (hpos : ∀ ω : sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
        0 < g (WithLp.ofLp (ω : EuclideanSpace ℝ (Fin n)))) :
    ∫⁻ z in Set.univ.pi (fun _ : Fin n => Set.Icc (-1 : ℝ) 1),
        ENNReal.ofReal ((g z) ^ (-c')) < ⊤ := by
  obtain ⟨a, ha, hlb⟩ := exists_pos_lower_bound_on_sphere g hgc hpos
  exact corner_block_cube_lintegral_lt_top g hgc.measurable hom c' hc0 hc' a ha hlb

end DLNFibre.DLN.RLCT
