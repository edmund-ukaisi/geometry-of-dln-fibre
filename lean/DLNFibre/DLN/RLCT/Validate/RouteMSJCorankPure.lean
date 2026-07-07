import DLNFibre.DLN.RLCT.Validate.RouteMSJCorankResidual
import DLNFibre.DLN.RLCT.Validate.RouteMSchurDepth2

/-!
# `DLNFibre.DLN.RLCT.Validate.RouteMSJCorankPure` — the PURE joint corank-block Morse peel

The **isotropic joint** corank-block finiteness for the R-BLOWUP PURE route
(`expeditions/2026-06-20-aoyagi-full/threads/genm-sjjoint-design/pure-vs-atom-adj.md`, verdict A).
The matrix (`p × q`, ANY outer domain) generalisation of the banked flat/`Fin 4` corank-2 terminal
`radial_morse_dominates_absZ_lt_top` (`RouteMSchurDepth2`): the freed corank block
`Δ : Fin p → Fin q → ℝ` over the box, coupled to an arbitrary outer parameter `z ∈ Z` through a
NON-NEGATIVE core `W z`, integrates finitely BELOW the block Morse threshold `pq/2`, JOINTLY:

    ∫_{z∈Z} ∫_{Δ∈matBox p q T} (frobSq Δ + W z)^{−c'} dΔ dz < ∞   (c' < pq/2, μ Z < ∞, W ≥ 0).

This is the **finite** isotropic counterpart of the DEAD anisotropic pointwise bound
(`RouteMSJCorankResidual` header, finding `genm-sjpeel-blow`): the naive pointwise-in-`z` bound on
`frobSq(Δ · Q_b)^{−c'}` DIVERGES on the rank-deficient-`Q_b` locus, so the peel is NOT a
`lintegral_mono_ae` on a pointwise estimate. Once the anisotropy `Δ ↦ Δ · Q_b` has been removed (the
`(S,J)` change-of-variables content), the block enters through its OWN Frobenius energy `frobSq Δ`
on a non-negative additive core `W z`, and THIS joint integral is finite — the pure route keeps `Δ`
a chart coordinate, blows up its radial (charge `= pq`, the block codim `(M₀−t)(M₁−t)`), and
integrates over the box, NEVER integrating `Δ` out against `Q_b` (which would manufacture the
divergent Gram determinant).

The `pq`-charge lands at the block Morse threshold `pq/2`: the inner block-box bound
`Kbound (pq) c' T` is `z`-INDEPENDENT (adding `W z ≥ 0` only shrinks the sub-threshold integral),
and Tonelli pulls it out against `μ Z < ∞`.

S2-FREE: the `p × q → Fin (p·q)` measure-preserving flatten (`eMatFlat`, `frobSq_eq_flatSum`,
`matBox_eq_eMatFlat_preimage`, all banked in `RouteMSJCorankResidual`) transports the inner integral
to the flat Morse box, then rides the banked `radial_morse_dominates_absZ_lt_top` (itself S2-free).
No `monomial_rlct`; the axiom footprint is the clean three
`[propext, Classical.choice, Quot.sound]`.

## What this brick is, and is NOT (fidelity)

This is the **terminal** isotropic joint block finiteness — the shape the pure `(S,J)` recursion
reaches once a corank block is fully resolved (anisotropy removed) and the deeper loss is folded
into the additive core `W z`. It does NOT: (i) remove the anisotropy `Δ ↦ Δ · Q_b` (the Gram change
of variables, `(S,J)` content); (ii) accumulate the per-layer radial monomial `∏ uⱼ²` across layers
(the recursion carrier, deferred); (iii) discharge `sjJointResolution` (which needs the full
recursion to this terminal). It is the reusable joint-finiteness endpoint, generalising the corank-2
`radial_morse_dominates_absZ_lt_top` to arbitrary block width `p × q` and an arbitrary outer
measurable domain.
-/

namespace DLNFibre.DLN.RLCT

open MeasureTheory Set
open scoped ENNReal BigOperators

/-- **The matrix-block ↔ flat-Morse-box integrand transport (S2-FREE).** For any core `w` and
exponent `c'`, the corank-block box integral of `(frobSq D + w)^{−c'}` over `matBox p q T` equals
the flat Morse-box integral of `(∑ᵢ xᵢ² + w)^{−c'}` over `morseBox (p·q) T`. The `p × q → Fin (p·q)`
measure-preserving flatten `eMatFlat` (banked: `matBox_eq_eMatFlat_preimage`, `frobSq_eq_flatSum`,
`measurePreserving_eMatFlat`) — the shared first step of `matBox_corank_residual_le`, factored here
so the joint peel reuses it per outer parameter. -/
theorem matBox_frobSq_add_lintegral_eq (p q : ℕ) (c' w T : ℝ) :
    ∫⁻ D in matBox p q T, ENNReal.ofReal ((frobSq D + w) ^ (-c'))
      = ∫⁻ x in morseBox (p * q) T, ENNReal.ofReal ((∑ i, (x i) ^ 2 + w) ^ (-c')) := by
  have hmp := measurePreserving_eMatFlat p q
  have hpremeas : MeasurableSet (eMatFlat p q ⁻¹' morseBox (p * q) T) :=
    (morseBox_measurableSet (p * q) T).preimage (eMatFlat p q).measurable
  have hrwfrob : ∀ D : Fin p → Fin q → ℝ, ENNReal.ofReal ((frobSq D + w) ^ (-c'))
      = (fun x : Fin (p * q) → ℝ =>
          ENNReal.ofReal ((∑ i, (x i) ^ 2 + w) ^ (-c'))) (eMatFlat p q D) :=
    fun D => by rw [frobSq_eq_flatSum p q D]
  rw [matBox_eq_eMatFlat_preimage p q T,
    setLIntegral_congr_fun hpremeas (fun D _ => hrwfrob D),
    hmp.setLIntegral_comp_preimage_emb (eMatFlat p q).measurableEmbedding
      (fun x => ENNReal.ofReal ((∑ i, (x i) ^ 2 + w) ^ (-c'))) (morseBox (p * q) T)]

/-- **The PURE joint corank-block Morse peel (S2-FREE).** For a `p × q` corank block `Δ`
(`p, q ≥ 1`) coupled to an arbitrary outer parameter `z ∈ Z` (finite outer volume `μ Z < ∞`) through
a NON-NEGATIVE additive core `W z ≥ 0`, BELOW the block Morse threshold `pq/2`, the JOINT integral
is finite:

    ∫_{z ∈ Z} ∫_{Δ ∈ matBox p q T} (frobSq Δ + W z)^{−c'} dΔ dz  <  ∞      (0 ≤ c' < pq/2).

The matrix / arbitrary-outer-domain generalisation of the banked corank-2 terminal
`radial_morse_dominates_absZ_lt_top`. The `eMatFlat` transport (`matBox_frobSq_add_lintegral_eq`)
rewrites each inner block integral to the flat Morse-box integral; the flat abstract-`Z` dominance
then finishes (the inner block-box bound `Kbound (pq) c' T` is `z`-independent, pulled out against
`μ Z`). This is the isotropic joint terminal of the pure `(S,J)` recursion; the charge
`pq = (M₀−t)(M₁−t)` lands at the block threshold `pq/2`. -/
theorem matBox_corank_dominates_absZ_lt_top {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (c' : ℝ) (hc' : c' < (p * q : ℝ) / 2) (hc0 : 0 ≤ c') (T : ℝ) (hT : 0 < T)
    (W : Ω → ℝ) (hWnn : ∀ z, 0 ≤ W z) (Z : Set Ω) (hZ : μ Z < ⊤) :
    ∫⁻ z in Z, (∫⁻ D in matBox p q T,
        ENNReal.ofReal ((frobSq D + W z) ^ (-c')) ∂volume) ∂μ < ⊤ := by
  obtain ⟨m, hm⟩ : ∃ m, p * q = m + 1 := ⟨p * q - 1, by have := Nat.mul_pos hp hq; omega⟩
  have hbridge : ((m : ℝ) + 1) = (p : ℝ) * (q : ℝ) := by
    rw [show ((m : ℝ) + 1) = ((m + 1 : ℕ) : ℝ) by push_cast; ring, ← hm]; push_cast; ring
  have hinnereq : ∀ z, (∫⁻ D in matBox p q T,
        ENNReal.ofReal ((frobSq D + W z) ^ (-c')) ∂volume)
      = ∫⁻ P in morseBox (m + 1) T, ENNReal.ofReal ((∑ j, (P j) ^ 2 + W z) ^ (-c')) ∂volume := by
    intro z; rw [matBox_frobSq_add_lintegral_eq p q c' (W z) T, hm]
  calc ∫⁻ z in Z, (∫⁻ D in matBox p q T,
          ENNReal.ofReal ((frobSq D + W z) ^ (-c')) ∂volume) ∂μ
      = ∫⁻ z in Z, (∫⁻ P in morseBox (m + 1) T,
          ENNReal.ofReal ((∑ j, (P j) ^ 2 + W z) ^ (-c')) ∂volume) ∂μ :=
        lintegral_congr hinnereq
    _ < ⊤ := radial_morse_dominates_absZ_lt_top μ c' (by rw [hbridge]; exact hc') hc0 T hT
        W hWnn Z hZ

/-- **The PURE intermediate-layer corank peel — the per-step exponent shift (S2-FREE).** For a
`p × q` corank block `Δ` (`p, q ≥ 1`) coupled to an outer parameter `z ∈ Z` through a
STRICTLY-POSITIVE additive core `W z > 0`, ABOVE the block Morse threshold `pq/2`, the joint
integral is bounded by the shifted-core integral:

    ∫_{z∈Z} ∫_{Δ∈matBox p q T} (frobSq Δ + W z)^{−c'} dΔ dz
        ≤ Cresid(pq) c' · ∫_{z∈Z} (W z)^{−(c' − pq/2)} dz      (pq/2 < c').

This is Aoyagi's per-layer exponent shift `c' ↦ c' − ½·pq` at block dimension `pq = (M₀−t)(M₁−t)`
(`peelExp`): the corank block peels (charge `pq`), leaving the deeper core `W z` at the SHIFTED
exponent `c' − pq/2` — the outer integral `∫_z (W z)^{−(c'−pq/2)}` the `(S,J)` recursion hands to
the strong IH (box finiteness of the STRICTLY-shorter chain at the shifted exponent). The banked
isotropic corank atom `matBox_corank_residual_le` per `z` (needs `W z > 0` — its
`w^{−(c'−pq/2)}` residual power), then `lintegral_mono` + the finite constant `Cresid` pulled out
(`lintegral_const_mul'`,
`ENNReal.ofReal_ne_top`).

The strict `W z > 0` is the honest hypothesis here: at an INTERMEDIATE layer the deeper loss is
strictly positive on the chart; the LAST layer, where the core can VANISH (`W z ≥ 0`), is instead
closed by `matBox_corank_dominates_absZ_lt_top` (Morse dominance, `c' < pq/2`). Together the two
bricks cover the two regimes of the pure peel — intermediate exponent-shift (`c' > pq/2`, `W > 0`)
and terminal Morse dominance (`c' < pq/2`, `W ≥ 0`). -/
theorem matBox_corank_residual_absZ_le {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (c' : ℝ) (hc' : (p * q : ℝ) / 2 < c') (T : ℝ) (hT : 0 < T)
    (W : Ω → ℝ) (hWpos : ∀ z, 0 < W z) (Z : Set Ω) :
    ∫⁻ z in Z, (∫⁻ D in matBox p q T,
        ENNReal.ofReal ((frobSq D + W z) ^ (-c')) ∂volume) ∂μ
      ≤ ENNReal.ofReal (Cresid (p * q) c')
          * ∫⁻ z in Z, ENNReal.ofReal ((W z) ^ (-(c' - (p * q : ℝ) / 2))) ∂μ := by
  calc ∫⁻ z in Z, (∫⁻ D in matBox p q T,
          ENNReal.ofReal ((frobSq D + W z) ^ (-c')) ∂volume) ∂μ
      ≤ ∫⁻ z in Z, ENNReal.ofReal (Cresid (p * q) c'
          * (W z) ^ (-(c' - (p * q : ℝ) / 2))) ∂μ :=
        lintegral_mono (fun z => matBox_corank_residual_le p q hp hq c' hc' T hT (W z) (hWpos z))
    _ = ∫⁻ z in Z, ENNReal.ofReal (Cresid (p * q) c')
          * ENNReal.ofReal ((W z) ^ (-(c' - (p * q : ℝ) / 2))) ∂μ :=
        lintegral_congr (fun z => by rw [ENNReal.ofReal_mul (Cresid_nonneg _ _)])
    _ = ENNReal.ofReal (Cresid (p * q) c')
          * ∫⁻ z in Z, ENNReal.ofReal ((W z) ^ (-(c' - (p * q : ℝ) / 2))) ∂μ :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

end DLNFibre.DLN.RLCT
