import DLNFibre.DLN.RLCT.Foundations.S1BoxProductMin
import DLNFibre.DLN.RLCT.Foundations.S1Cover
import DLNFibre.DLN.RLCT.Foundations.S1G5Charts

/-!
# `DLNFibre.DLN.RLCT.Foundations.S1NodeCoverGE` — the per-node cover GE (`≥`) leg (R1 item 2a)

The `≥`-direction of the per-node blow-up cover, assembled from the box-form weighted product-min
(`S1BoxProductMin`), the `g5` cover machinery (`g5_flat_cover` + `cover_integral_lt_top_iff`), and the
`argmaxCell` cover/disjointness (`S1G5Charts`). Concretises the RECURSION SHAPE of the per-node atom.

## What the GE leg establishes
For the true loss `F = dlnLoss M 0` (flat), the `mk` pivot charts cover `{A ≠ 0}` a.e.-disjointly; on
each chart `F∘φ_p = y₀²·core_p` with Jacobian `|y₀|^{mk−1}`. By `g5_flat_cover`,
`∫_U |F|^{−c'} = Σ_p ∫_{chart_p} |y₀|^{mk−1}·|core_p|^{−c'}`, and each summand is finite (for
`c' < mk/2`) **provided `|core_p|^{−c'}` is integrable over the chart's full ratio box** — the
`boxpm_integrableOn_of_lt` hypothesis. Hence `∫_U |F|^{−c'} < ⊤`, so (via `rlctAtOn_ge_of_integral_lt`)
`min{mk/2, (the c' admitted by the core boxes)} ≤ rlctAtOn F 0`.

## THE RECURSION SHAPE (the reported crux — answered concretely)
The per-chart hypothesis `boxpm_integrableOn_of_lt` requires `|core_p|^{−c'}` integrable over the
**full ratio box** `Vz` — NOT a point-RLCT of `core`. So the node's box-integrability reduces to the
CORE's box-integrability, not its point threshold. With the uniform Schur squeeze `core ≍ Φ = ∑Erow² +
‖child‖²` over the box (`schur_node_squeeze_unif`, `T = √(m−1)` bounded on the ratio box) and disjoint-
block additivity, `core`'s box-integrability reduces to the CHILD-loss box-integrability — the SAME
recursion one dimension down. **The atom is NOT a clean point-min `rlctAtOn node = min{mk/2, n/2 +
rlctAtOn child}`; it threads the child's FULL-BOX integrability** (the (2,2,2) `resolved_residual_lt_top`
`recStep` precedent). This file states the GE leg with the per-chart box-integrability as the explicit
threaded hypothesis, making the recursion shape the interface — for a617's spine to consume.

Axiom-free target (only `propext`/`Classical.choice`/`Quot.sound`).
-/

open MeasureTheory Set
open scoped ENNReal BigOperators
namespace DLNFibre.DLN.RLCT

/-! ## The abstract cover-finiteness GE leg (the recursion-shape interface) -/

/-- **The per-node cover GE leg (abstract, recursion-shape interface).** Given a flat loss `F` on
`Fin N → ℝ`, a finite pivot-chart family `φ` covering an open box `U` a.e.-disjointly off the pivot-zero
null sets (the `g5_flat_cover` contract), and — the load-bearing input — that EACH chart's pulled-back
threshold integrand is integrable over its chart domain `V p \ N p` (`hchart`), the threshold integral
over `U` is finite. The per-chart `hchart` is exactly what `boxpm_integrableOn_of_lt` discharges from
`c' < mk/2` + the chart CORE's FULL-BOX integrability — so this lemma's hypothesis IS the recursion's
threaded box-integrability (the reported shape: child full-box, not child point-RLCT). -/
theorem node_cover_threshold_lt_top {N : ℕ} {ι : Type*} (s : Finset ι)
    (F : (Fin N → ℝ) → ℝ) (φ : ι → (Fin N → ℝ) → (Fin N → ℝ))
    (φ' : ι → (Fin N → ℝ) → ((Fin N → ℝ) →L[ℝ] (Fin N → ℝ)))
    (V Npiv : ι → Set (Fin N → ℝ)) (U : Set (Fin N → ℝ)) (c' : NNReal)
    (hV : ∀ i ∈ s, MeasurableSet (V i)) (hN : ∀ i ∈ s, MeasurableSet (Npiv i))
    (hφ' : ∀ i ∈ s, ∀ x ∈ V i \ Npiv i, HasFDerivWithinAt (φ i) (φ' i x) (V i \ Npiv i) x)
    (hinj : ∀ i ∈ s, InjOn (φ i) (V i \ Npiv i))
    (hNnull : ∀ i ∈ s, volume ((φ i) '' (Npiv i)) = 0)
    (hcover : U =ᵐ[volume] ⋃ i ∈ s, (φ i) '' (V i))
    (hdisj : Set.Pairwise (↑s) (Function.onFun (AEDisjoint volume)
      (fun i : ι => (φ i) '' (V i))))
    (hmeas : ∀ i ∈ s, NullMeasurableSet ((φ i) '' (V i)) volume)
    (hchart : ∀ i ∈ s, ∫⁻ x in V i \ Npiv i,
        ENNReal.ofReal (|(φ' i x).det| * |F (φ i x)| ^ (-(c' : ℝ))) < ⊤) :
    ∫⁻ x in U, ENNReal.ofReal (|F x| ^ (-(c' : ℝ))) < ⊤ := by
  -- the `g5_flat_cover` identity for `g = ofReal(|F|^{−c'})`
  have hcov := g5_flat_cover (volume : Measure (Fin N → ℝ)) s φ φ' V Npiv U
    hV hN hφ' hinj hNnull hcover hdisj hmeas
    (fun x => ENNReal.ofReal (|F x| ^ (-(c' : ℝ))))
  -- the cover sum is finite iff each leaf is (`cover_integral_lt_top_iff`)
  rw [(cover_integral_lt_top_iff s volume U (fun i => V i \ Npiv i)
        (fun x => ENNReal.ofReal (|F x| ^ (-(c' : ℝ))))
        (fun i x => ENNReal.ofReal |(φ' i x).det| * ENNReal.ofReal (|F (φ i x)| ^ (-(c' : ℝ))))
        hcov)]
  intro i hi
  -- the leaf integrand `ofReal|det|·ofReal(|F∘φ|^{−c'}) = ofReal(|det|·|F∘φ|^{−c'})`, finite by `hchart`
  have heq : ∀ x, ENNReal.ofReal |(φ' i x).det| * ENNReal.ofReal (|F (φ i x)| ^ (-(c' : ℝ)))
      = ENNReal.ofReal (|(φ' i x).det| * |F (φ i x)| ^ (-(c' : ℝ))) := fun x => by
    rw [← ENNReal.ofReal_mul (abs_nonneg _)]
  rw [setLIntegral_congr_fun (hV i hi |>.diff (hN i hi)) (fun x _ => heq x)]
  exact hchart i hi

/-! ## The per-chart `hchart` from the box-product-min (the recursion-shape bridge)

The abstract `hchart` (per-chart pullback integrable) is discharged, per chart, from the box-form
weighted product-min: when the chart pullback presents as `|det| = |y₀|^{mk−1}` and `F∘φ = y₀²·core`
on a rectangle `Iy ×ˢ Vz` (the chart box), `boxpm_integrableOn_of_lt` gives the integrability from
`c' < mk/2` AND `|core|^{−c'}` integrable over `Vz` (the core's FULL-BOX integrability). This lemma
makes that bridge explicit, exposing the recursion's threaded input: the CORE box-integrability `hKint`,
NOT a point-RLCT of the core. The actual chart presentation (`F∘φ = y₀²·core` via
`dlnLoss_nodeBlowup_factor`, `|det| = |y₀|^{mk−1}` via `pivotBlowupOnDeriv_det`/`flatIdx_layer0_card`)
is the assembly's plumbing; here `e = mk−1`, `Iy` the bounded pivot interval, `Vz` the core box. -/
theorem chart_pullback_lt_top_of_boxpm {Z : Type*}
    [MeasureSpace Z] [TopologicalSpace Z] [Zero Z] [SFinite (volume : Measure Z)]
    [BorelSpace Z] [SecondCountableTopology Z]
    (e : ℕ) (c' : ℝ) (hc' : 0 ≤ c') (hc'lt : c' < ((e : ℝ) + 1) / 2)
    (K : Z → ℝ) (hKm : Measurable K)
    (Iy : Set ℝ) (hIy : MeasurableSet Iy) (hIybdd : Bornology.IsBounded Iy)
    (Vz : Set Z) (hKint : IntegrableOn (fun z => |K z| ^ (-c')) Vz volume) :
    ∫⁻ p in Iy ×ˢ Vz,
        ENNReal.ofReal (|p.1| ^ e * |p.1 ^ 2 * K p.2| ^ (-c')) < ⊤ := by
  -- `boxpm_integrableOn_of_lt` gives the integrand integrable on the rectangle; reduce to lintegral < ⊤.
  have hbox := boxpm_integrableOn_of_lt K hKm e c' hc' Iy hIy hIybdd hc'lt Vz hKint
  have hnn : ∀ p : ℝ × Z, 0 ≤ |p.1| ^ e * |p.1 ^ 2 * K p.2| ^ (-c') :=
    fun p => mul_nonneg (by positivity) (Real.rpow_nonneg (abs_nonneg _) _)
  -- the box integrand `|p.1|^e · |p.1²·K|^{−c'}` is the `boxpm` integrand commuted (`mul_comm`)
  have hcomm : (fun p : ℝ × Z => |p.1 ^ 2 * K p.2| ^ (-c') * |p.1| ^ e)
      = (fun p : ℝ × Z => |p.1| ^ e * |p.1 ^ 2 * K p.2| ^ (-c')) := by
    funext p; rw [mul_comm]
  rw [hcomm] at hbox
  rw [IntegrableOn, Integrable, hasFiniteIntegral_iff_ofReal (ae_of_all _ (fun p => hnn p))] at hbox
  exact hbox.2

end DLNFibre.DLN.RLCT
