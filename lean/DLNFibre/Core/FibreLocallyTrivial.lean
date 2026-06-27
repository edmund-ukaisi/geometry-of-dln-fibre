/-
Copyright (c) 2026. Released under Apache 2.0; see LICENSE.
-/
import DLNFibre.Core.FibreRankBridge

/-!
# `DLNFibre.Core.FibreLocallyTrivial` — honest local-product structure over the rank-`= r` open (S4)

The headline rung of the fibration-geometry spine: promote the per-pivot local-product atlas
(`reducedFibre_pivotLocalProductAtlasOnRankOpen`, thread 22) to a clean, honestly-named
**local-product-over-an-open-cover** statement over the rank-`= r` open
`rankROpen ⊆ Spec (sweepSigmaRing k d r)`, now that the S1 keystone
(`mem_rankROpen_iff_rank_universalMatrixResidue_eq`) certifies that `rankROpen` genuinely **is** the
locus where the universal product matrix has rank exactly `r` over each residue field — not merely
the definitional cover-complement.

## What this DOES claim (the honest local-product content)

`RankROpenPerPivotLocalProduct d r hp hq` bundles three genuinely-established facts:

1. **`isRankLocus`** (the S1 keystone, folded in): for every prime `P`,
   `P ∈ rankROpen d r ↔ (universalMatrixResidue d r P).rank = r`. This is the name=content bridge —
   it upgrades `rankROpen` from "the union of pivot-minor basic opens" (its definition) to
   "the residue-field rank-`= r` locus of the universal product matrix". WITHOUT this the open is a
   formal cover-complement; WITH it the cover is genuinely a cover *of the rank-`= r` open*.
2. **`cover`** (the scheme open-cover): the per-pivot charts
   `PrimeSpectrum.basicOpen (chartDsigAt s t)`, over all pivots `(s, t)`, cover `rankROpen`.
3. **`triv` / `triv_chartElt`** (the per-chart product trivialization): over each pivot chart there
   is a `k`-algebra isomorphism of the localized chart total ring with the product
   `SchurLoc ⊗_k sweepFibreRing` of the local matrix-direction with the (fixed) standard fibre ring,
   and the chart's localizing element is exactly `chartDsigAt s t`.

The reader-facing headline is the **pointwise** theorem `reducedFibre_existsProductChartAt_rankEq`:
for every prime `P` at which the universal matrix has rank `r`, there is a pivot chart containing
`P` carrying a product trivialization. This reads as genuine local triviality at each point of the
rank-`= r` open, composed directly from (1)+(2)+(3).

## What this does NOT claim (the honest residual — read before reusing)

- **NOT `locallyTrivial` / `FiberBundle`.** Those names imply a coherent *target-side* transition
  cocycle (the per-chart trivializations glued on overlaps, `targetOverlapTransition`, roadmap R1),
  which is **not** assembled. This statement is **per-chart / uncocycled**: each chart is a product,
  but the products are NOT identified on overlaps here. (The banked atlas carries the *base-side*
  overlap cocycle `chartOverlapTransition` with its laws, and an overlap-local restriction; those
  are available but are base-side, not the fixed-target gluing a fibre bundle needs.)
- The product iso is a bare `k`-algebra equivalence `Total ≃ₐ[k] SchurLoc ⊗_k Fibre`; **no
  projection-compatibility field is asserted**. A genuine "respects the base projection" condition
  would compare the iso against a named base map `SchurLoc →ₐ[k] Total` (giving an `AlgEquiv` over
  `SchurLoc`), which is not packaged here — stating projection-compatibility without that named map
  would be vacuous, so it is deliberately omitted (decorrelated Codex consult, design round).

**Dependency rule:** `Core` only — never import `DLNFibre.DLN`.
-/

namespace DLNFibre.Core

open MvPolynomial Matrix
open scoped TensorProduct

variable {k : Type} [Field k] [Infinite k] {N : ℕ}

/-! ## The honest local-product structure over the rank-`= r` open -/

/-- **An honest per-chart local-product structure over the rank-`= r` open.** For a fixed `(d, r)`,
bundles: (1) the S1 rank-locus identity `isRankLocus` — `rankROpen` is exactly the residue-field
rank-`= r` locus of the universal product matrix (the name=content bridge); (2) the scheme
open-cover `cover` of `rankROpen` by the per-pivot charts; (3) a per-pivot product trivialization
`triv` (a `k`-algebra iso of the localized chart total ring with `SchurLoc ⊗_k sweepFibreRing`)
whose localizing element is the chart minor `chartDsigAt s t` (`triv_chartElt`). This is the honest
"locally a product over an open cover of the rank-`= r` open" — **per-chart, uncocycled**: it does
NOT carry a coherent target-side overlap cocycle (roadmap R1), so it is deliberately not a
`locallyTrivial`/`FiberBundle` object. -/
structure RankROpenPerPivotLocalProduct (d : Fin (N + 2) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last (N + 1))) (hq : r ≤ d 0) where
  /-- **The rank-locus identity (S1 keystone, folded in).** A prime lies in `rankROpen` iff the
  universal product matrix over its residue field has rank exactly `r`. This certifies that the open
  the charts cover genuinely IS the rank-`= r` locus, not merely the definitional
  common-vanishing-locus complement. -/
  isRankLocus : ∀ P : PrimeSpectrum (sweepSigmaRing k d r),
    P ∈ rankROpen (k := k) d r ↔ (universalMatrixResidue d r P).rank = r
  /-- **The scheme open-cover.** The per-pivot charts `basicOpen (chartDsigAt s t)`, over all
  pivots, cover the rank-`= r` open `rankROpen` of `Spec (sweepSigmaRing)`. -/
  cover : (⋃ st : (Fin r → Fin (d (Fin.last (N + 1)))) × (Fin r → Fin (d 0)),
        (PrimeSpectrum.basicOpen (chartDsigAt (k := k) d r st.1 st.2) :
          Set (PrimeSpectrum (sweepSigmaRing k d r))))
      = rankROpen (k := k) d r
  /-- **The per-chart product trivialization.** A genuine local-trivialization datum at every pivot:
  the localized chart total ring `Away (chartDsigAt s t)` is, as a `k`-algebra, the product
  `SchurLoc ⊗_k sweepFibreRing` of the local matrix direction with the fixed standard fibre ring. -/
  triv : ∀ I : PivotDatum d r hp hq,
    LocalTrivializationDatum k (sweepSigmaRing k d r)
      (Localization.Away (chartDsigAt (k := k) d r I.s I.t))
      (SchurLoc (k := k) (d 0) (d (Fin.last (N + 1))) r) (sweepFibreRing k d r hp hq)
  /-- **The chart's localizing element is its pivot minor.** The `triv I` datum localizes at exactly
  the pivot minor `chartDsigAt I.s I.t` (`= pivotElt I`) — so the chart `basicOpen (chartDsigAt s
  t)` of `cover` connects to its product trivialization `triv`. -/
  triv_chartElt : ∀ I : PivotDatum d r hp hq,
    (triv I).chartElt = chartDsigAt (k := k) d r I.s I.t

/-- **The reduced fibre family is an honest local product over the rank-`= r` open.** Assembled from
the banked per-pivot atlas (`reducedFibre_pivotLocalProductAtlasOnRankOpen`, thread 22) + the S1
rank-bridge keystone (`mem_rankROpen_iff_rank_universalMatrixResidue_eq`). Every field is a banked,
machine-checked fact — the rank-locus identity, the scheme open-cover, the per-pivot product
trivializations. **Per-chart / uncocycled**: NOT a `locallyTrivial`/`FiberBundle` (the target-side
overlap cocycle R1 is unbuilt); see the module docstring. -/
noncomputable def reducedFibre_rankROpenPerPivotLocalProduct (d : Fin (N + 2) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last (N + 1))) (hq : r ≤ d 0) :
    RankROpenPerPivotLocalProduct (k := k) d r hp hq where
  isRankLocus P := mem_rankROpen_iff_rank_universalMatrixResidue_eq d r P
  cover := iSup_pivot_basicOpen_eq_rankROpen d r
  triv I := (reducedFibre_pivotLocalProductAtlasOnRankOpen d r hp hq).triv I
  triv_chartElt _ := rfl

/-! ## The reader-facing headline: pointwise local product at each rank-`= r` prime -/

/-- **The honest local-triviality headline (pointwise).** For every prime `P` of the chart-closure
ring `sweepSigmaRing k d r` at which the universal product matrix over the residue field `κ(P)` has
rank exactly `r`, there is a pivot `(s, t)` whose chart `basicOpen (chartDsigAt s t)` contains `P`
and over which the localized total ring is, as a `k`-algebra, the product
`SchurLoc ⊗_k sweepFibreRing` of the local matrix direction with the standard fibre ring. This is
genuine **local triviality at each point of the rank-`= r` open**: every rank-`= r` prime sits in a
product-trivialized chart. Composed directly from the S1 rank-bridge (rank `= r` ⟹ `P ∈ rankROpen`),
the scheme open-cover (`P ∈ rankROpen` ⟹ some chart contains `P`), and the per-pivot product
trivialization. **Per-chart / uncocycled**: it does NOT assert the charts' products agree on
overlaps (the target-side overlap cocycle R1 is unbuilt) — hence not named `locallyTrivial`. -/
theorem reducedFibre_existsProductChartAt_rankEq (d : Fin (N + 2) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last (N + 1))) (hq : r ≤ d 0)
    (P : PrimeSpectrum (sweepSigmaRing k d r))
    (hP : (universalMatrixResidue d r P).rank = r) :
    ∃ (s : Fin r → Fin (d (Fin.last (N + 1)))) (t : Fin r → Fin (d 0)),
      P ∈ PrimeSpectrum.basicOpen (chartDsigAt (k := k) d r s t) ∧
      Nonempty (Localization.Away (chartDsigAt (k := k) d r s t)
        ≃ₐ[k] SchurLoc (k := k) (d 0) (d (Fin.last (N + 1))) r
          ⊗[k] sweepFibreRing k d r hp hq) := by
  -- S1: rank `= r` puts `P` in `rankROpen`, the union of the pivot charts.
  have hmem : P ∈ rankROpen (k := k) d r :=
    (mem_rankROpen_iff_rank_universalMatrixResidue_eq d r P).mpr hP
  rw [← iSup_pivot_basicOpen_eq_rankROpen, Set.mem_iUnion] at hmem
  obtain ⟨st, hst⟩ := hmem
  -- the chart datum at `(s, t)` (chart membership forces injectivity) IS the product.
  refine ⟨st.1, st.2, hst, ?_⟩
  obtain ⟨I, hI⟩ := pivotDatumOfMemBasicOpen d r hp hq st.1 st.2 hst
  refine ⟨?_⟩
  -- the per-pivot trivialization at `I` lands in `Away (chartDsigAt I.s I.t)`; rewrite to `(s, t)`.
  have hrw : chartDsigAt (k := k) d r I.s I.t = chartDsigAt (k := k) d r st.1 st.2 := hI
  exact hrw ▸ (perPivotLocalTrivializationDatum d r hp hq I.s I.t I.σ I.τ I.hσ I.hτ).trivialization

/-! ## Non-vacuity witnesses -/

section Witness

/-- **Rank-locus witness.** The folded-in S1 identity fires: a prime lies in `rankROpen` iff the
universal product matrix has rank `r` over its residue field — the geometric characterization of the
open the charts cover. -/
example {k : Type} [Field k] [Infinite k] {N : ℕ} (d : Fin (N + 2) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last (N + 1))) (hq : r ≤ d 0)
    (P : PrimeSpectrum (sweepSigmaRing k d r)) :
    P ∈ rankROpen (k := k) d r ↔ (universalMatrixResidue d r P).rank = r :=
  (reducedFibre_rankROpenPerPivotLocalProduct (k := k) d r hp hq).isRankLocus P

/-- **Open-cover witness.** The per-pivot charts genuinely cover the rank-`= r` open. -/
example {k : Type} [Field k] [Infinite k] {N : ℕ} (d : Fin (N + 2) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last (N + 1))) (hq : r ≤ d 0) :
    (⋃ st : (Fin r → Fin (d (Fin.last (N + 1)))) × (Fin r → Fin (d 0)),
        (PrimeSpectrum.basicOpen (chartDsigAt (k := k) d r st.1 st.2) :
          Set (PrimeSpectrum (sweepSigmaRing k d r))))
      = rankROpen (k := k) d r :=
  (reducedFibre_rankROpenPerPivotLocalProduct (k := k) d r hp hq).cover

/-- **Per-chart product witness.** The trivialization at a pivot is a genuine `k`-algebra iso of the
localized chart total ring with the product `SchurLoc ⊗ sweepFibreRing`, localizing at the chart
minor `chartDsigAt s t`. -/
example {k : Type} [Field k] [Infinite k] {N : ℕ} (d : Fin (N + 2) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last (N + 1))) (hq : r ≤ d 0) (I : PivotDatum d r hp hq) :
    ((reducedFibre_rankROpenPerPivotLocalProduct (k := k) d r hp hq).triv I).chartElt
      = chartDsigAt (k := k) d r I.s I.t :=
  (reducedFibre_rankROpenPerPivotLocalProduct (k := k) d r hp hq).triv_chartElt I

/-- **Pointwise local-product witness.** The reader-facing headline fires at any rank-`= r` prime:
it sits in a pivot chart carrying a product trivialization. -/
example {k : Type} [Field k] [Infinite k] {N : ℕ} (d : Fin (N + 2) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last (N + 1))) (hq : r ≤ d 0)
    (P : PrimeSpectrum (sweepSigmaRing k d r))
    (hP : (universalMatrixResidue d r P).rank = r) :
    ∃ (s : Fin r → Fin (d (Fin.last (N + 1)))) (t : Fin r → Fin (d 0)),
      P ∈ PrimeSpectrum.basicOpen (chartDsigAt (k := k) d r s t) ∧
      Nonempty (Localization.Away (chartDsigAt (k := k) d r s t)
        ≃ₐ[k] SchurLoc (k := k) (d 0) (d (Fin.last (N + 1))) r
          ⊗[k] sweepFibreRing k d r hp hq) :=
  reducedFibre_existsProductChartAt_rankEq d r hp hq P hP

end Witness

end DLNFibre.Core
