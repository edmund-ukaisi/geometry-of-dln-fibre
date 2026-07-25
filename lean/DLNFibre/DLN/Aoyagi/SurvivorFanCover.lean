import Meta.Cordon
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# R2 (cover-side) — the SURVIVOR-ENTRY fan: the per-node UP-TO-NULL cover atom

The reroute R2 cover atom, in the form the tube-cover probe (`#169`,
`threads/reroute-R2-tubecover/tube-cover-probe.md`, exact + decorrelated Codex) forces. That
probe established at `(3,3,3,2,2)` that the **radial-pivot** fan (vary the input radial, keep one
fixed survivor entry) covers **0 %** of the `{unit≈0}` tube — every such chart carries the SAME
numerator (the fixed survivor generator) and so all vanish together on its zero locus. The
**survivor-entry** fan — one sibling per residual-ideal generator (each entry that can be the
rank-surviving pivot) — covers the node box **up-to-null**, the only uncovered set being
`{X=0} = {all generators vanish}` (codim ≥ 2, Lebesgue-null).

This module formalises exactly that correction, abstractly over a finite family of generators
`gen : ι → E → ℝ` (the residual-ideal generators / entries that can survive) and the per-entry
charts. It is the correction to `CoverFold.bornSiblings_union_covers`, whose fan is indexed by the
input RADIAL pivot (`p ∈ Z`, via the block-blow-up argmax) — a FULL cover of the input box, but
silent about the OUTPUT `{X=0}` hole. Here the routing is the argmax over the GENERATORS, and the
hole is named honestly as `commonZero gen = {X=0}`.

## The mechanism (probe2/probe3, exact)
Each survivor-entry chart is regular exactly where its generator SURVIVES (`gen a ≠ 0`) and
dominates the others up to the box ratio `R` — that is `survivorRegion R gen a`. The argmax
generator is always dominant with ratio `1 ≤ R`, so:

* `iUnion_survivorRegion` — the survivor regions cover **exactly** the complement of the hole:
  `⋃ a, survivorRegion R gen a = (commonZero gen)ᶜ` (a set EQUALITY, `1 ≤ R`). This is the tight
  form: the uncovered set is precisely `{X=0}`, no bigger, no smaller.
* `volume_box_diff_survivorRegion_eq_zero` / `volume_box_diff_charts_eq_zero` — the UP-TO-NULL
  cover: `volume (box \ ⋃ charts) = 0`, given the hole is null (`volume (commonZero gen) = 0`).

## Indexing — matched pairings (loss-isometry orbit), permutation-closed
The atom is abstract over the index `ι`: the caller chooses the generators. For the DLN application
`gen` is the LOSS-ISOMETRY ORBIT = the MATCHED inner-permutation pairings — each `gen a` a PRODUCT
TERM of a survivor entry (e.g. `C3[0,1]·C4[1,0]`), NOT arbitrary independent pivots. Being abstract
over `ι`, the atom is PERMUTATION-CLOSED: it extends unchanged to the shear-outermost reordering
(the escape cone B1, `#170`) — one fan, no separate construction.

Two obligations, kept DISTINCT: (i) `hchart` — the SET-COVER hypothesis of THIS atom (chart images
cover their survivor regions), which ANY covering chart meets, even identity charts (cf.
`witness_chart_cover`); (ii) the downstream `R > 0` SANDWICH (loss-normal-form, `sumSq_residual`) a
REAL geometric chart must satisfy to be loss-regular — an R3 / caller obligation, NOT enforced
here and NOT the same as (i). A MISMATCHED pivot gives `R(0) = 0` and fails (ii), so it is not a
valid fan member — but that exclusion lives in (ii)'s downstream discharge, never in `hchart`.
With `gen` the matched-pairing monomials the hole `commonZero gen ⊆ {R=0}`
(`commonZero_subset_residualZero`); `{R=0}` is codim ≥ 2, so the hole is measure-zero (cheap — see
below).

## The null input (`volume (commonZero gen) = 0`) — CHEAP codim-nullity
The measure conclusions take the hole's nullity as an explicit hypothesis, and it is ELEMENTARY: the
hole `{X=0}` is the zero-set of the generators, so if even ONE generator is a non-vanishing
polynomial its zero-set is null (codim ≥ 1) and the hole `⊆` it is null —
`volume_commonZero_eq_zero_of_single`. Probe1 computed the hole to be `{X=0}`, codim ≥ 2 (generic
`δ`: codim 4) at `(3,3,3,2,2)`; codim ≥ 1 already suffices for nullity. The witnesses discharge it
concretely (`Measure.pi_hyperplane`).

This is NOT the `#172` obligation. `#172` is a DIFFERENT question on the SAME set — the
integrability / divisor-ratio behaviour as points APPROACH `{R=0}` — owned by the VALUE rung (the
RLCT lower bound), not this measure-bookkeeping atom. Nullity here is a set-measure fact; the
recursion there is an analysis fact.

## Scope (honest) — this is the MEASURE-BOOKKEEPING layer, NOT the RLCT lower bound
This atom is the up-to-null COVER: the box is covered by the fan except for a measure-zero hole. It
says NOTHING about blow-up behaviour as `R → 0`; the RLCT lower bound `rlct ≥ ½·minAdm` still needs
the per-chart integrability + the recursion (the VALUE rung, `#172`) built ON TOP of this cover.
- IN: the survivor-entry-fan per-node up-to-null cover atom (this file) + the sum-of-squares
  residual normal-form structural lemma (`sumSq_residual`).
- OUT (do NOT block on): the per-chart cover certificate `hchart` (each atlas chart covers its
  survivor region — discharged at the fold/wire from the block-blow-up atoms + the clearing, R3, an
  explicit hypothesis here); the RLCT-value obligations (per-chart integrability + the `#172`
  approach-recursion); the sector-count escape cone (B1, `#170`).

## Main results
- `commonZero`, `survivorRegion` — the hole `{X=0}` and the per-entry survivor region.
- `iUnion_survivorRegion` — the tight characterization: the fan covers exactly `(commonZero)ᶜ`.
- `box_diff_charts_subset_commonZero` — the uncovered set (chart images) is contained in `{X=0}`.
- `volume_box_diff_survivorRegion_eq_zero` / `volume_box_diff_charts_eq_zero` — up-to-null cover.
- `volume_commonZero_eq_zero_of_single` — nullity from one generator's null zero-set.
- `commonZero_subset_residualZero` / `volume_commonZero_eq_zero_of_residualNull` — hole ⊆ `{R=0}`
  bridge (matched-pairing entries), wiring `hnull` to the recursion locus `#172`.
- `sumSq_residual` — the kept-survivor `loss = monomial² · R` structural input (`R` a sum of
  squares, `R(0) = 1`, `R ≥ (kept pivot)²`).
- `witness_commonZero_null`, `witness_survivorRegion_cover`, `witness_chart_cover` — non-vacuity.
-/

open MeasureTheory Set

namespace DLNFibre.DLN.Aoyagi.SurvivorFanCover

variable {E : Type*} {ι : Type*}

/-- The **hole** `{X=0}`: the common-zero set of the survivor-entry generators (all residual-ideal
generators vanish). This is the only set the survivor-entry fan cannot cover. -/
def commonZero (gen : ι → E → ℝ) : Set E := {x | ∀ a, gen a x = 0}

/-- The region survivor entry `a` covers: it **survives** (`gen a ≠ 0`) and **dominates** every
other generator up to the box ratio `R`. The sibling pivoting on generator `a` is regular exactly
here — the blow-up making `a` the rank-survivor needs `gen a ≠ 0` (probe2: a fan on a FIXED
survivor's numerator vanishes wholesale on that survivor's zero locus). -/
def survivorRegion (R : ℝ) (gen : ι → E → ℝ) (a : ι) : Set E :=
  {x | gen a x ≠ 0 ∧ ∀ b, |gen b x| ≤ R * |gen a x|}

/-- **The tight characterization (the survivor-entry correction).** For `1 ≤ R` the survivor
regions cover **exactly** the complement of the hole:
`⋃ a, survivorRegion R gen a = (commonZero gen)ᶜ`. The `⊇` direction is the argmax routing (pick the
dominant generator; it survives since some generator is nonzero); the `⊆` direction is that every
chart requires its generator nonzero. The uncovered set is therefore precisely `{X=0}` — no smaller
(the fan reaches everything off the hole), no bigger (no chart reaches the hole). -/
theorem iUnion_survivorRegion [Finite ι] [Nonempty ι] {R : ℝ} (hR : 1 ≤ R)
    (gen : ι → E → ℝ) :
    ⋃ a, survivorRegion R gen a = (commonZero gen)ᶜ := by
  letI := Fintype.ofFinite ι
  apply subset_antisymm
  · intro x hx
    obtain ⟨a, ha⟩ := Set.mem_iUnion.mp hx
    simp only [survivorRegion, Set.mem_setOf_eq] at ha
    simp only [commonZero, Set.mem_compl_iff, Set.mem_setOf_eq, not_forall]
    exact ⟨a, ha.1⟩
  · intro x hx
    simp only [commonZero, Set.mem_compl_iff, Set.mem_setOf_eq, not_forall] at hx
    obtain ⟨a0, ha0⟩ := hx
    obtain ⟨a, -, hmax⟩ :=
      Finset.exists_max_image Finset.univ (fun b => |gen b x|) Finset.univ_nonempty
    have hpos : 0 < |gen a x| := lt_of_lt_of_le (abs_pos.mpr ha0) (hmax a0 (Finset.mem_univ a0))
    refine Set.mem_iUnion.mpr ⟨a, abs_pos.mp hpos, fun b => ?_⟩
    exact (hmax b (Finset.mem_univ b)).trans (le_mul_of_one_le_left (abs_nonneg _) hR)

/-- **The uncovered set is contained in `{X=0}`.** Given each chart covers its survivor region
within the box (`hchart`), the box minus the union of chart images is contained in the hole
`commonZero gen`. Pure set theory over `iUnion_survivorRegion`: a box point outside the hole lands
in some survivor region, hence in that chart's image. -/
theorem box_diff_charts_subset_commonZero [Finite ι] [Nonempty ι] {R : ℝ} (hR : 1 ≤ R)
    (gen : ι → E → ℝ) (box : Set E) (chart : ι → E → E) (dom : ι → Set E)
    (hchart : ∀ a, survivorRegion R gen a ∩ box ⊆ chart a '' dom a) :
    box \ (⋃ a, chart a '' dom a) ⊆ commonZero gen := by
  intro x hx
  by_contra hxc
  have hxne : x ∈ (commonZero gen)ᶜ := hxc
  rw [← iUnion_survivorRegion hR gen] at hxne
  obtain ⟨a, ha⟩ := Set.mem_iUnion.mp hxne
  exact hx.2 (Set.mem_iUnion.mpr ⟨a, hchart a ⟨ha, hx.1⟩⟩)

/-! ## Measure conclusions (`volume` on `Fin N → ℝ`) -/

variable {N : ℕ}

/-- Nullity of the hole from ONE generator's null zero-set: `commonZero gen ⊆ {gen a0 = 0}`, so if
`{gen a0 = 0}` is null the hole is null. Exposes the weakest input — codim ≥ 1 (a single nonzero
generator) already gives nullity, weaker than the source's codim ≥ 2. -/
theorem volume_commonZero_eq_zero_of_single (gen : ι → (Fin N → ℝ) → ℝ) (a0 : ι)
    (h : volume {x : Fin N → ℝ | gen a0 x = 0} = 0) :
    volume (commonZero gen) = 0 :=
  measure_mono_null (fun _ hx => hx a0) h

/-- **The hole is contained in the residual's zero-set `{R=0}`.** When each residual entry `entry e`
vanishes wherever ALL generators vanish (`hentry` — automatic when the entries are sums of the
generator monomials, the matched-pairing structure), the hole is contained in
`{x | ∑ e, (entry e x)² = 0} = {R=0}`. Since `{R=0}` is codim ≥ 2, this is an alternative CHEAP
route to the hole's nullity (`volume_commonZero_eq_zero_of_residualNull`) — a set-measure fact,
distinct from the `#172` approach-integrability the VALUE rung owns. -/
theorem commonZero_subset_residualZero {κ : Type*} [Fintype κ]
    (gen : ι → E → ℝ) (entry : κ → E → ℝ)
    (hentry : ∀ e x, (∀ a, gen a x = 0) → entry e x = 0) :
    commonZero gen ⊆ {x | ∑ e, (entry e x) ^ 2 = 0} := by
  intro x hx
  simp only [Set.mem_setOf_eq]
  refine Finset.sum_eq_zero (fun e _ => ?_)
  rw [hentry e x hx]; ring

/-- Nullity of the hole from the residual's `{R=0}` nullity: if the matched-pairing entries vanish
on the common-zero (`hentry`) and `{R=0}` is null, the hole is null. An alternative to
`volume_commonZero_eq_zero_of_single` phrased via the residual `R`; both are CHEAP codim-nullity —
NOT the `#172` approach-integrability obligation (the value rung's, a different fact on the same
set). -/
theorem volume_commonZero_eq_zero_of_residualNull {κ : Type*} [Fintype κ]
    (gen : ι → (Fin N → ℝ) → ℝ) (entry : κ → (Fin N → ℝ) → ℝ)
    (hentry : ∀ e x, (∀ a, gen a x = 0) → entry e x = 0)
    (hres : volume {x : Fin N → ℝ | ∑ e, (entry e x) ^ 2 = 0} = 0) :
    volume (commonZero gen) = 0 :=
  measure_mono_null (commonZero_subset_residualZero gen entry hentry) hres

/-- **UP-TO-NULL cover (raw survivor regions).** Given the hole is null, the box minus the union of
the survivor regions is null: `volume (box \ ⋃ a, survivorRegion R gen a) = 0`. The tightest form —
no chart hypothesis, straight from `iUnion_survivorRegion` (`box \ (commonZero)ᶜ = box ∩
commonZero`). -/
theorem volume_box_diff_survivorRegion_eq_zero [Finite ι] [Nonempty ι] {R : ℝ} (hR : 1 ≤ R)
    (gen : ι → (Fin N → ℝ) → ℝ) (box : Set (Fin N → ℝ))
    (hnull : volume (commonZero gen) = 0) :
    volume (box \ ⋃ a, survivorRegion R gen a) = 0 := by
  refine measure_mono_null ?_ hnull
  rw [iUnion_survivorRegion hR gen]
  intro x hx
  simpa using hx.2

/-- **UP-TO-NULL cover (chart images) — the per-node R2 atom.** Given each chart covers its survivor
region within the box (`hchart`) and the hole is null (`hnull`), the box minus the union of chart
images is null: `volume (box \ ⋃ a, chart a '' dom a) = 0`. This is the survivor-entry-fan per-node
up-to-null cover the brief asked for, with the uncovered set contained in `{X=0}`
(`box_diff_charts_subset_commonZero`). -/
theorem volume_box_diff_charts_eq_zero [Finite ι] [Nonempty ι] {R : ℝ} (hR : 1 ≤ R)
    (gen : ι → (Fin N → ℝ) → ℝ) (box : Set (Fin N → ℝ))
    (chart : ι → (Fin N → ℝ) → (Fin N → ℝ)) (dom : ι → Set (Fin N → ℝ))
    (hchart : ∀ a, survivorRegion R gen a ∩ box ⊆ chart a '' dom a)
    (hnull : volume (commonZero gen) = 0) :
    volume (box \ ⋃ a, chart a '' dom a) = 0 :=
  measure_mono_null (box_diff_charts_subset_commonZero hR gen box chart dom hchart) hnull

/-! ## The kept-survivor normal-form structural input (`loss = monomial² · R`) -/

/-- **The residual `R = ∑ (f i)²` structural input** (probe: `loss = (wy)² · R`, `R(0) = 1`). With a
distinguished kept "1"-pivot `f i0` (value `1` at the origin `o`) and every other summand vanishing
at `o`: `R ≥ 0` everywhere, `R(o) = 1`, and `R ≥ (kept pivot)²` everywhere. These are the
sum-of-squares facts the lower-bound sandwich builds on. NOTE this lemma proves only the POINTWISE
bounds + the value at `o`; turning `R(o) = 1` into a NEIGHBOURHOOD lower bound (`R` a unit near `o`)
needs continuity of `f i0`, which is NOT established here. -/
theorem sumSq_residual {ι' : Type*} [Fintype ι'] (f : ι' → E → ℝ) (i0 : ι') (o : E)
    (h1 : f i0 o = 1) (h0 : ∀ i, i ≠ i0 → f i o = 0) :
    (∀ x, 0 ≤ ∑ i, (f i x) ^ 2) ∧
      (∑ i, (f i o) ^ 2 = 1) ∧
      (∀ x, (f i0 x) ^ 2 ≤ ∑ i, (f i x) ^ 2) := by
  refine ⟨fun x => Finset.sum_nonneg (fun i _ => sq_nonneg _), ?_,
    fun x => Finset.single_le_sum (fun i _ => sq_nonneg (f i x)) (Finset.mem_univ i0)⟩
  rw [Finset.sum_eq_single i0]
  · rw [h1]; norm_num
  · intro i _ hi; rw [h0 i hi]; norm_num
  · intro h; exact absurd (Finset.mem_univ i0) h

/-! ## Non-vacuity witnesses (`ι = Fin 2`, coordinate generators, hole `= {0}`, codim 2) -/

/-- Non-vacuity: with the coordinate generators on `Fin 2 → ℝ`, the hole `commonZero` is `{0}` —
codim 2, matching the source's codim ≥ 2 — and it is Lebesgue-null (via `Measure.pi_hyperplane`). -/
theorem witness_commonZero_null :
    volume (commonZero (fun (a : Fin 2) (x : Fin 2 → ℝ) => x a)) = 0 := by
  refine volume_commonZero_eq_zero_of_single _ 0 ?_
  rw [volume_pi]
  exact Measure.pi_hyperplane _ 0 0

/-- Non-vacuity (raw regions): the survivor-entry fan for the coordinate generators covers ALL of
space up-to-null — `volume (univ \ ⋃ a, survivorRegion 1 gen a) = 0` — the uncovered part being
exactly the codim-2 hole `{0}`. Fires `volume_box_diff_survivorRegion_eq_zero` non-trivially. -/
theorem witness_survivorRegion_cover :
    volume (Set.univ \
      ⋃ a, survivorRegion 1 (fun (a : Fin 2) (x : Fin 2 → ℝ) => x a) a) = 0 :=
  volume_box_diff_survivorRegion_eq_zero le_rfl _ _ witness_commonZero_null

/-- Non-vacuity (chart images): the identity charts with per-entry domain `= survivorRegion ∩ box`
satisfy the per-chart cover hypothesis, so `volume_box_diff_charts_eq_zero` fires — all of space
minus the union of chart images is null. Exercises the full chart-level atom end to end. -/
theorem witness_chart_cover :
    volume (Set.univ \
      ⋃ a, (id : (Fin 2 → ℝ) → (Fin 2 → ℝ)) ''
        (survivorRegion 1 (fun (a : Fin 2) (x : Fin 2 → ℝ) => x a) a ∩ Set.univ)) = 0 :=
  volume_box_diff_charts_eq_zero le_rfl _ _ (fun _ => id) _
    (fun _ => by rw [Set.image_id]) witness_commonZero_null

-- Forced axiom gate: the cover atoms + witnesses rest only on `[propext, Classical.choice,
-- Quot.sound]`. A future edit making any depend on `sorryAx` FAILS this red (not masked by a
-- stale-olean `exit 0` — lean/CLAUDE.md caveat).
#assert_banked_clean_batch [iUnion_survivorRegion, box_diff_charts_subset_commonZero,
  volume_box_diff_survivorRegion_eq_zero, volume_box_diff_charts_eq_zero,
  volume_commonZero_eq_zero_of_single, commonZero_subset_residualZero,
  volume_commonZero_eq_zero_of_residualNull, sumSq_residual, witness_commonZero_null,
  witness_survivorRegion_cover, witness_chart_cover]

end DLNFibre.DLN.Aoyagi.SurvivorFanCover
