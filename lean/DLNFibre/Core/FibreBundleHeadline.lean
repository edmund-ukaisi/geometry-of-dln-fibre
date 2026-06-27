/-
Copyright (c) 2026. Released under Apache 2.0; see LICENSE.
-/
import DLNFibre.Core.FibreLocallyTrivial
import DLNFibre.Core.FibreOverBaseTriv

/-!
# `DLNFibre.Core.FibreBundleHeadline` — the over-base local-product-with-flatness capstone (S5)

The expedition capstone for the DLN reduced fibre family over the rank-`= r` open. It **upgrades**
the S4 headline `reducedFibre_existsProductChartAt_rankEq` (which carried only a *bare `k`-algebra*
product per chart) to the genuine **over-base** version, using the S4b convergent keystone: each
chart's localized total ring is, OVER its in-chart Schur/base ring `SchurLoc` (via an HONEST
structure map), the standard fibre model `SchurLoc ⊗_k sweepFibreRing`, AND is flat over `SchurLoc`.

## What this DOES claim

`RankROpenOverBaseLocalProduct d r hp hq` bundles, for a fixed `(d, r)`:

1. **`isRankLocus`** (the S1 keystone, folded in): for every prime `P`,
   `P ∈ rankROpen d r ↔ (universalMatrixResidue d r P).rank = r`. The name=content bridge:
   `rankROpen` genuinely IS the residue-field rank-`= r` locus.
2. **`cover`** (the scheme open-cover): the per-pivot charts `basicOpen (chartDsigAt s t)` cover
   `rankROpen`.
3. **`structMap`** (the per-pivot HONEST structure map): a `k`-algebra map
   `SchurLoc →ₐ[k] Away (chartDsigAt s t)` exhibiting each chart total ring as a `SchurLoc`-algebra,
   where `SchurLoc` is the in-chart Schur-direction coordinate ring (`= Away (detSchurS …)`, NOT the
   base-restriction `Away (chartDsigAt s t)` of `sweepSigmaRing`; see the open items below). The map
   is `schurToDsigAt` (the gauge-transported `schurToDsig`).
4. **`triv`** (the per-pivot OVER-BASE trivialization): with the `structMap`-induced
   `SchurLoc`-algebra structure, a `SchurLoc`-algebra iso
   `Away (chartDsigAt s t) ≃ₐ[SchurLoc] SchurLoc ⊗_k sweepFibreRing`
   (the `chartDsigAt_schurLocTensorEquiv` of S4b).
5. **`flat`** (the per-pivot FLATNESS over the base): with the same structure, the chart total ring
   is `Module.Flat SchurLoc (Away (chartDsigAt s t))` (`chartDsigAt_flat_over_schurLoc` of S4b).

The reader-facing headline is the **pointwise** theorem
`reducedFibre_existsOverBaseProductChartAt_rankEq`: for every prime `P` at which the universal
matrix has rank `r`, there is a pivot chart containing `P` AND an honest structure map
`φ : SchurLoc →ₐ[k] Away (chartDsigAt s t)` such that, OVER the `φ`-induced base algebra, the chart
total ring is the product `SchurLoc ⊗_k sweepFibreRing` (a `≃ₐ[SchurLoc]`) and is flat over the
base. This is the S4 headline's `Nonempty (… ≃ₐ[k] …)` upgraded to over-base `≃ₐ[SchurLoc]` + flat.

## What this does NOT claim (the honest residual — read before reusing)

The base of the over-base trivialization + flatness is **`SchurLoc`**, the in-chart Schur-direction
coordinate ring (`= Localization.Away (detSchurS …)`), acting via the named structure map
`structMap`. `SchurLoc` is a DIFFERENT ring from the actual bundle base — the
restriction of `sweepSigmaRing` to `basicOpen (chartDsigAt s t)` (i.e. `Away (chartDsigAt s t)` is a
localization OF `sweepSigmaRing`, whereas `SchurLoc` is the Schur block-localization). The wording
throughout is "over `SchurLoc`", never "flat over `rankROpen`" or "flat over `sweepSigmaRing`".

- **OPEN ITEM — the chart-base bridge (a real build, AHEAD of R1).** There is NO proven
  identification `SchurLoc ≅ (sweepSigmaRing restricted to basicOpen (chartDsigAt s t))` with
  structure-map compatibility. That bridge is unbuilt; it is the prerequisite for reading the
  chartwise `SchurLoc`-flatness as flatness over the genuine base
  `rankROpen ⊆ Spec(sweepSigmaRing)`.
  Until it is built, the flatness/triviality is honestly only over `SchurLoc`.
- **OPEN ITEM — NOT `Flat π` / `FiberBundle` over all of `rankROpen` (NOT a GLOBAL morphism, R1).**
  This is the CHARTWISE over-base local product + chartwise flatness, at every pivot / every
  rank-`= r` point. A single GLOBAL flatness-of-`π` or fibre-bundle statement over the whole
  `rankROpen` additionally needs the target-side overlap-gluing cocycle (roadmap R1
  `targetOverlapTransition`) to assemble the per-chart data; that stays roadmapped and is **not**
  claimed here. (Whether global flatness as a property globalizes from the chartwise data without R1
  is a separate question assessed elsewhere.)
- The structure map `structMap` is the in-chart *ring* map `SchurLoc →ₐ[k] Total`; no scheme
  morphism / continuity / sheaf statement is asserted. The over-base content is exactly: the
  trivialization respects this named base map (it is a `≃ₐ[SchurLoc]`, not a bare `≃ₐ[k]`), and the
  total ring is flat as a module over `SchurLoc` via this map.

**Dependency rule:** `Core` only — never import `DLNFibre.DLN`.
-/

namespace DLNFibre.Core

open MvPolynomial Matrix
open scoped TensorProduct

variable {k : Type} [Field k] [Infinite k] {N : ℕ}

/-! ## The per-pivot over-base trivialization datum -/

/-- **The over-base trivialization datum at one pivot.** For a pivot datum `I`, bundles: the HONEST
structure map `structMap : SchurLoc →ₐ[k] Away (chartDsigAt I.s I.t)` (exhibiting the chart total
ring as a `SchurLoc`-algebra, `SchurLoc` the in-chart Schur-direction ring), the
trivialization `triv`
(a `SchurLoc`-algebra iso of the chart total ring with `SchurLoc ⊗_k sweepFibreRing`, over the
`structMap`-induced algebra), and the FLATNESS `flat` (the chart total ring is flat over the base
via `structMap`). This is the S4b per-pivot data (`schurToDsigAt`,
`chartDsigAt_schurLocTensorEquiv`,
`chartDsigAt_flat_over_schurLoc`) packaged with the `SchurLoc`-algebra structure carried explicitly
as the structure map, so the data is independent of any ambient `letI`. -/
structure OverBaseChartDatum (d : Fin (N + 2) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last (N + 1))) (hq : r ≤ d 0) (I : PivotDatum d r hp hq) where
  /-- The HONEST structure map (`schurToDsigAt`): `SchurLoc →ₐ[k] Away (chartDsigAt I.s I.t)`, the
  in-chart Schur-direction coordinate ring `Away (detSchurS …)`, exhibiting the chart total ring
  as a `SchurLoc`-algebra. NOT the base-restriction of `sweepSigmaRing` (chart-base bridge,
  open). -/
  structMap : SchurLoc (k := k) (d 0) (d (Fin.last (N + 1))) r →ₐ[k]
    Localization.Away (chartDsigAt (k := k) d r I.s I.t)
  /-- The OVER-BASE trivialization: with the `structMap`-induced `SchurLoc`-algebra structure on the
  chart total ring, a `SchurLoc`-algebra iso with the standard fibre model
  `SchurLoc ⊗_k sweepFibreRing`. -/
  triv :
    letI := structMap.toRingHom.toAlgebra
    Localization.Away (chartDsigAt (k := k) d r I.s I.t)
      ≃ₐ[SchurLoc (k := k) (d 0) (d (Fin.last (N + 1))) r]
        SchurLoc (k := k) (d 0) (d (Fin.last (N + 1))) r ⊗[k] sweepFibreRing k d r hp hq
  /-- FLATNESS over the base: with the `structMap`-induced structure, the chart total ring is flat
  over `SchurLoc`. -/
  flat :
    letI := structMap.toRingHom.toAlgebra
    Module.Flat (SchurLoc (k := k) (d 0) (d (Fin.last (N + 1))) r)
      (Localization.Away (chartDsigAt (k := k) d r I.s I.t))

/-- **The over-base trivialization datum at a pivot, genuinely instantiated.** The structure map is
the S4b honest structure map `schurToDsigAt` (gauge ∘ deep-chart ∘ connecting map); the over-base
iso is `chartDsigAt_schurLocTensorEquiv`; the flatness is `chartDsigAt_flat_over_schurLoc`. Every
field is a banked, machine-checked S4b fact. -/
noncomputable def overBaseChartDatum (d : Fin (N + 2) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last (N + 1))) (hq : r ≤ d 0) (I : PivotDatum d r hp hq) :
    OverBaseChartDatum (k := k) d r hp hq I where
  structMap := schurToDsigAt d r hp hq I.s I.t I.σ I.τ I.hσ I.hτ
  triv := chartDsigAt_schurLocTensorEquiv d r hp hq I.s I.t I.σ I.τ I.hσ I.hτ
  flat := chartDsigAt_flat_over_schurLoc d r hp hq I.s I.t I.σ I.τ I.hσ I.hτ

/-! ## The over-base local-product structure over the rank-`= r` open -/

/-- **The genuine over-base local-product-with-flatness structure over the rank-`= r` open (S5).**
For a fixed `(d, r)`, bundles: (1) the S1 rank-locus identity `isRankLocus`; (2) the scheme
open-cover `cover` of `rankROpen`; (3) per-pivot the HONEST structure map + over-base trivialization
+ flatness over the base (`chart`, an `OverBaseChartDatum`). This UPGRADES S4's
`RankROpenPerPivotLocalProduct` (bare `k`-algebra products) to the over-base version: each chart is
a product OVER the in-chart Schur-direction ring `SchurLoc` (via an honest structure map), flat
over `SchurLoc`. (`SchurLoc` not yet identified with the base-restriction: chart-base bridge, open.)
**Chartwise / per-chart**: it does NOT carry a target-side overlap cocycle (R1), so it is NOT a
global `Flat π` / `FiberBundle`; see the module docstring. -/
structure RankROpenOverBaseLocalProduct (d : Fin (N + 2) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last (N + 1))) (hq : r ≤ d 0) where
  /-- **The rank-locus identity (S1 keystone, folded in).** A prime lies in `rankROpen` iff the
  universal product matrix over its residue field has rank exactly `r`. -/
  isRankLocus : ∀ P : PrimeSpectrum (sweepSigmaRing k d r),
    P ∈ rankROpen (k := k) d r ↔ (universalMatrixResidue d r P).rank = r
  /-- **The scheme open-cover.** The per-pivot charts cover the rank-`= r` open. -/
  cover : (⋃ st : (Fin r → Fin (d (Fin.last (N + 1)))) × (Fin r → Fin (d 0)),
        (PrimeSpectrum.basicOpen (chartDsigAt (k := k) d r st.1 st.2) :
          Set (PrimeSpectrum (sweepSigmaRing k d r))))
      = rankROpen (k := k) d r
  /-- **The per-pivot over-base datum.** At every pivot: the honest structure map, the over-base
  `≃ₐ[SchurLoc]` trivialization, and the flatness over the base. -/
  chart : ∀ I : PivotDatum d r hp hq, OverBaseChartDatum (k := k) d r hp hq I

/-- **The reduced fibre family is an honest over-base local product (with flatness) over the
rank-`= r` open (S5).** Assembled from the S1 rank-bridge keystone, the banked scheme open-cover,
and
the S4b per-pivot over-base trivialization + flatness. Every field is a banked, machine-checked
fact.
**Chartwise**: NOT a global `Flat π` / `FiberBundle` (target-side overlap cocycle R1 unbuilt);
see the module docstring. -/
noncomputable def reducedFibre_rankROpenOverBaseLocalProduct (d : Fin (N + 2) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last (N + 1))) (hq : r ≤ d 0) :
    RankROpenOverBaseLocalProduct (k := k) d r hp hq where
  isRankLocus P := mem_rankROpen_iff_rank_universalMatrixResidue_eq d r P
  cover := iSup_pivot_basicOpen_eq_rankROpen d r
  chart I := overBaseChartDatum d r hp hq I

/-! ## The reader-facing headline: pointwise over-base local product at each rank-`= r` prime -/

/-- **The over-base local-triviality + flatness headline (pointwise, S5).** For every prime `P` of
the chart-closure ring `sweepSigmaRing k d r` at which the universal product matrix over `κ(P)` has
rank exactly `r`, there is a pivot `(s, t)` whose chart `basicOpen (chartDsigAt s t)` contains `P`,
together with an HONEST structure map `φ : SchurLoc →ₐ[k] Away (chartDsigAt s t)` (`SchurLoc` = the
in-chart Schur-direction coordinate ring `Away (detSchurS …)`, NOT the base-restriction of
`sweepSigmaRing`), such that — OVER the `φ`-induced `SchurLoc`-algebra structure on the chart total
ring —

* the chart total ring is the product `SchurLoc ⊗_k sweepFibreRing` (a `SchurLoc`-algebra iso, not
  merely a `k`-algebra iso), AND
* the chart total ring is FLAT over `SchurLoc`.

This UPGRADES the S4 headline `reducedFibre_existsProductChartAt_rankEq` (bare
`Nonempty (… ≃ₐ[k] …)`)
to the genuine over-base version. Composed from the S1 rank-bridge, the scheme open-cover, and the
S4b per-pivot over-base data. **Chartwise / uncocycled, base = `SchurLoc`**: it does NOT identify
`SchurLoc` with the base-restriction (chart-base bridge, open), and does NOT assert a global
`Flat π` /
fibre bundle over all of `rankROpen` (the target-side overlap cocycle R1 is unbuilt). -/
theorem reducedFibre_existsOverBaseProductChartAt_rankEq (d : Fin (N + 2) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last (N + 1))) (hq : r ≤ d 0)
    (P : PrimeSpectrum (sweepSigmaRing k d r))
    (hP : (universalMatrixResidue d r P).rank = r) :
    ∃ (s : Fin r → Fin (d (Fin.last (N + 1)))) (t : Fin r → Fin (d 0)),
      P ∈ PrimeSpectrum.basicOpen (chartDsigAt (k := k) d r s t) ∧
      ∃ φ : SchurLoc (k := k) (d 0) (d (Fin.last (N + 1))) r →ₐ[k]
          Localization.Away (chartDsigAt (k := k) d r s t),
        (letI := φ.toRingHom.toAlgebra;
          Nonempty (Localization.Away (chartDsigAt (k := k) d r s t)
            ≃ₐ[SchurLoc (k := k) (d 0) (d (Fin.last (N + 1))) r]
              SchurLoc (k := k) (d 0) (d (Fin.last (N + 1))) r
                ⊗[k] sweepFibreRing k d r hp hq)) ∧
        (letI := φ.toRingHom.toAlgebra;
          Module.Flat (SchurLoc (k := k) (d 0) (d (Fin.last (N + 1))) r)
            (Localization.Away (chartDsigAt (k := k) d r s t))) := by
  -- S1: rank `= r` puts `P` in `rankROpen`, the union of the pivot charts.
  have hmem : P ∈ rankROpen (k := k) d r :=
    (mem_rankROpen_iff_rank_universalMatrixResidue_eq d r P).mpr hP
  rw [← iSup_pivot_basicOpen_eq_rankROpen, Set.mem_iUnion] at hmem
  obtain ⟨st, hst⟩ := hmem
  -- chart membership forces injectivity ⟹ a `PivotDatum I` with chart elt `chartDsigAt st.1 st.2`.
  obtain ⟨I, hI⟩ := pivotDatumOfMemBasicOpen d r hp hq st.1 st.2 hst
  -- present the chart at `I.s, I.t` (where the S4b over-base data lives NATIVELY): only membership
  -- Prop transports across `hI : chartDsigAt I.s I.t = chartDsigAt st.1 st.2` (cheap), never the
  -- heavy over-base data (avoids the `isDefEq` blowup of transporting the structure-map algebra).
  rw [SetLike.mem_coe] at hst
  have hmem' : P ∈ PrimeSpectrum.basicOpen (chartDsigAt (k := k) d r I.s I.t) := by
    rw [← hI] at hst; exact hst
  exact ⟨I.s, I.t, hmem', (overBaseChartDatum d r hp hq I).structMap,
    ⟨(overBaseChartDatum d r hp hq I).triv⟩, (overBaseChartDatum d r hp hq I).flat⟩

/-! ## Non-vacuity witnesses -/

section Witness

/-- **Rank-locus witness.** The folded-in S1 identity fires. -/
example {k : Type} [Field k] [Infinite k] {N : ℕ} (d : Fin (N + 2) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last (N + 1))) (hq : r ≤ d 0)
    (P : PrimeSpectrum (sweepSigmaRing k d r)) :
    P ∈ rankROpen (k := k) d r ↔ (universalMatrixResidue d r P).rank = r :=
  (reducedFibre_rankROpenOverBaseLocalProduct (k := k) d r hp hq).isRankLocus P

/-- **Open-cover witness.** The per-pivot charts cover the rank-`= r` open. -/
example {k : Type} [Field k] [Infinite k] {N : ℕ} (d : Fin (N + 2) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last (N + 1))) (hq : r ≤ d 0) :
    (⋃ st : (Fin r → Fin (d (Fin.last (N + 1)))) × (Fin r → Fin (d 0)),
        (PrimeSpectrum.basicOpen (chartDsigAt (k := k) d r st.1 st.2) :
          Set (PrimeSpectrum (sweepSigmaRing k d r))))
      = rankROpen (k := k) d r :=
  (reducedFibre_rankROpenOverBaseLocalProduct (k := k) d r hp hq).cover

/-- **Per-pivot over-base trivialization witness.** The datum at a pivot carries a genuine
`SchurLoc`-algebra iso of the chart total ring with `SchurLoc ⊗_k sweepFibreRing` (over the honest
structure map). -/
noncomputable def overBaseTrivWitness {k : Type} [Field k] [Infinite k] {N : ℕ}
    (d : Fin (N + 2) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last (N + 1))) (hq : r ≤ d 0) (I : PivotDatum d r hp hq) :
    letI := ((reducedFibre_rankROpenOverBaseLocalProduct
      (k := k) d r hp hq).chart I).structMap.toRingHom.toAlgebra;
    Localization.Away (chartDsigAt (k := k) d r I.s I.t)
      ≃ₐ[SchurLoc (k := k) (d 0) (d (Fin.last (N + 1))) r]
        SchurLoc (k := k) (d 0) (d (Fin.last (N + 1))) r
          ⊗[k] sweepFibreRing k d r hp hq :=
  ((reducedFibre_rankROpenOverBaseLocalProduct (k := k) d r hp hq).chart I).triv

/-- **Per-pivot flatness witness.** The chart total ring is flat over the base `SchurLoc` (via the
honest structure map). -/
example {k : Type} [Field k] [Infinite k] {N : ℕ} (d : Fin (N + 2) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last (N + 1))) (hq : r ≤ d 0) (I : PivotDatum d r hp hq) :
    letI := ((reducedFibre_rankROpenOverBaseLocalProduct
      (k := k) d r hp hq).chart I).structMap.toRingHom.toAlgebra;
    Module.Flat (SchurLoc (k := k) (d 0) (d (Fin.last (N + 1))) r)
      (Localization.Away (chartDsigAt (k := k) d r I.s I.t)) :=
  ((reducedFibre_rankROpenOverBaseLocalProduct (k := k) d r hp hq).chart I).flat

/-- **Pointwise over-base local-product witness.** The reader-facing headline fires at any
rank-`= r` prime: it sits in a pivot chart carrying an over-base product trivialization +
flatness. -/
example {k : Type} [Field k] [Infinite k] {N : ℕ} (d : Fin (N + 2) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last (N + 1))) (hq : r ≤ d 0)
    (P : PrimeSpectrum (sweepSigmaRing k d r))
    (hP : (universalMatrixResidue d r P).rank = r) :
    ∃ (s : Fin r → Fin (d (Fin.last (N + 1)))) (t : Fin r → Fin (d 0)),
      P ∈ PrimeSpectrum.basicOpen (chartDsigAt (k := k) d r s t) ∧
      ∃ φ : SchurLoc (k := k) (d 0) (d (Fin.last (N + 1))) r →ₐ[k]
          Localization.Away (chartDsigAt (k := k) d r s t),
        (letI := φ.toRingHom.toAlgebra;
          Nonempty (Localization.Away (chartDsigAt (k := k) d r s t)
            ≃ₐ[SchurLoc (k := k) (d 0) (d (Fin.last (N + 1))) r]
              SchurLoc (k := k) (d 0) (d (Fin.last (N + 1))) r
                ⊗[k] sweepFibreRing k d r hp hq)) ∧
        (letI := φ.toRingHom.toAlgebra;
          Module.Flat (SchurLoc (k := k) (d 0) (d (Fin.last (N + 1))) r)
            (Localization.Away (chartDsigAt (k := k) d r s t))) :=
  reducedFibre_existsOverBaseProductChartAt_rankEq d r hp hq P hP

end Witness

end DLNFibre.Core
