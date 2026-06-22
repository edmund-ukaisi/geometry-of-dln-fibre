import DLNFibre.DLN.RLCT.Skeleton
import DLNFibre.DLN.RLCT.Foundations.S1Cover

/-!
# `DLNFibre.DLN.RLCT.Validate.RouteMBridge` — the Route-M rlct-cover BRIDGE (crux2, §5(5), SPECIFY)

The general per-node mechanism's value step (g138 §5(5)): `rlctAtOn (core) 0 = ⨅ᵢ monomialThreshold`,
over fm3's chart cover. MECHANISM-INDEPENDENT — consumes the chart family `(ι, d, k, h)` + the cover
datum + the per-leaf monomial pullback ABSTRACTLY (as an `IsRouteMCover` hypothesis), so it is unaffected
by how the charts are PRODUCED (fm3's geometry; the C1 squeeze→monomial correction). Generalizes
`Case222CoverGE`/`Case222CoverGETail` (the bespoke (2,2,2) `≥`-cover) to an abstract cover.

SPECIFY stage (this file): the abstract cover interface `IsRouteMCover` (a stub fm3's geometry fills)
+ the bridge `routeM_rlctAtOn_eq_iInf` consuming it. Bodies `sorry`; the signature is the contract.

- `IsRouteMCover F U ι d k h φ` — the abstract input: a finite chart family with per-leaf monomial
  pullback + Jacobian + a.e. cover, the generalized `Case222CoverGE` input set.
- `routeM_rlctAtOn_eq_iInf` — the BRIDGE: `rlctAtOn F 0 = ⨅ᵢ monomialThreshold (d i)(k i)(h i)`.

Cover #21 (`resolution_value_of_atlas`) then closes `⨅ = ofReal(lambdaCore M)`; the headline assembles
`rlctAtOn(core) = lambdaCore`. This file is core-only (no `nReg` regular shift; that is L2/Fubini).
-/

open MeasureTheory
open scoped ENNReal BigOperators
namespace DLNFibre.DLN.RLCT

/-- **The abstract Route-M chart cover** (the stubbed interface fm3's chart geometry fills, §5(1,2)).
A finite family of charts `φ i` covering a neighbourhood of `0` a.e., each pulling the core `F` back to a
monomial `monomialIntegrand (d i)(k i)(h i)` times a positive unit, with the disjoint-cover integral
split. This is the generalized `Case222CoverGE` input — `crux2`'s bridge consumes it ABSTRACTLY; the C1
squeeze→monomial correction changes how fm3 PRODUCES it, not this consumed shape. -/
structure IsRouteMCover {N : ℕ} (F : (Fin N → ℝ) → ℝ) (U : Set (Fin N → ℝ))
    (ι : Type) [Fintype ι] (d : ι → ℕ) (k h : (i : ι) → Fin (d i) → ℕ) : Prop where
  /-- `F` is measurable (polynomial core). -/
  Fmeas : Measurable F
  /-- The base nbhd `U` is open and contains the deepest point `0`. -/
  Uopen : IsOpen U
  Umem : (0 : Fin N → ℝ) ∈ U
  /-- (COVER ≥) Per `c'`, the threshold integral over `U` is bounded by the SUM over leaves of the
  per-leaf monomial integrals (the `g5_pivotNode`/`recStep` cover split + per-chart CoV); so finiteness
  of every leaf integral (below its threshold) gives finiteness over `U`. The exact split fm3's cover
  datum supplies; here the consequence the bridge needs. -/
  cover_le : ∀ c' : NNReal,
      ∫⁻ x in U, ENNReal.ofReal (|F x| ^ (-(c' : ℝ)))
        ≤ ∑ i : ι, ∫⁻ y in unitBox (d i),
            ENNReal.ofReal (monomialIntegrand (d i) (k i) (h i) (c' : ℝ) y)
  /-- (COVER ≤) Conversely, for `c'` at-or-above some leaf's threshold, the `U`-integral diverges
  (the leaf's monomial singularity, ε-uniform, survives localisation to any sub-box of any `Ω ∋ 0`). -/
  cover_ge_div : ∀ c' : NNReal, (∃ i : ι, monomialThreshold (d i) (k i) (h i) ≤ (c' : ℝ≥0∞)) →
      ∀ Ω : Set (Fin N → ℝ), IsOpen Ω → (0 : Fin N → ℝ) ∈ Ω →
        ¬ IntegrableOn (fun x => |F x| ^ (-(c' : ℝ)) * (fun _ => (1 : ℝ)) x) Ω volume

/-- **The Route-M rlct-cover BRIDGE (crux2, §5(5)) — SPECIFY, body `sorry`.** Given the abstract chart
cover, the core's RLCT at the deepest point is the infimum of the per-leaf monomial thresholds:
`rlctAtOn F 0 = ⨅ᵢ monomialThreshold (d i)(k i)(h i)`. The two directions: `≥` from `cover_le` +
`monomialIntegrand_integrable_of_lt` (below-threshold ⟹ leaf finite ⟹ `U`-finite ⟹ `rlctAtOn ≥ ⨅`,
S2-free); `≤` from `cover_ge_div` (at-or-above some leaf threshold ⟹ `U`-divergence ⟹ that `c'` not
admissible on any `Ω` ⟹ `rlctAtOn ≤ ⨅`). Mechanism-independent: consumes `IsRouteMCover` abstractly.
The value `⨅ = ofReal(lambdaCore M)` is cover #21's `resolution_value_of_atlas`, NOT here. -/
theorem routeM_rlctAtOn_eq_iInf {N : ℕ} (F : (Fin N → ℝ) → ℝ) (U : Set (Fin N → ℝ))
    (ι : Type) [Fintype ι] [Nonempty ι] (d : ι → ℕ) (k h : (i : ι) → Fin (d i) → ℕ)
    (hcover : IsRouteMCover F U ι d k h) :
    rlctAtOn F (0 : Fin N → ℝ) = ⨅ i : ι, monomialThreshold (d i) (k i) (h i) := by
  sorry

end DLNFibre.DLN.RLCT
