/-
Copyright (c) 2026. Released under Apache 2.0; see LICENSE.
-/
import DLNFibre.Core.FibreLocallyTrivial
import DLNFibre.Core.FibreOverBaseTriv
import DLNFibre.Core.RingTheory.Determinantal.Atlas

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
   where `SchurLoc` is the in-chart base direction (the Schur-direction coordinate ring
   `= Away (detSchurS …)`) — a PROPER subdirection of the total chart `Away (chartDsigAt s t)`, not
   the whole localized total ring (whose extra `sweepFibreRing` factor is the fibre; see the open
   items below). The map is `schurToDsigAt` (the gauge-transported `schurToDsig`).
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

The geometry of the chart. `Spec (sweepSigmaRing k d r) = Σ̄^r` is the **source/total** rank-`≤ r`
locus (the composable matrix tuples whose product has rank `≤ r`), NOT the target-matrix base.
`Away (chartDsigAt s t)` is the localized **total** chart, and is already the source of the product
trivialization `Away (chartDsigAt s t) ≃ SchurLoc ⊗_k sweepFibreRing`. In that product, `SchurLoc`
(the in-chart Schur-direction coordinate ring `= Localization.Away (detSchurS …)`) is the **base
direction** — it presents the target/base rank-chart — and `sweepFibreRing` is the **fibre**. The
over-base trivialization + flatness is over this base direction `SchurLoc`, via the named structure
map `structMap = schurToDsigAt`. The wording throughout is "over `SchurLoc`", never "flat over
`rankROpen`" or "flat over `sweepSigmaRing`" (those are the source/total, not the base).

- **CLOSED (R5, `Core.FibreProjectionCompat`) — projection compatibility.** The structure map
  `schurToDsigAt : SchurLoc →ₐ[k] Away (chartDsigAt s t)` **agrees with the pullback of `mult`'s
  projection** after precomposition with `localizeSchur`: `schurToDsigAt_comp_localizeSchur` /
  `chartPhiSchurAeval_eq_comp_multComap` factor the in-chart base map through `mult`'s comorphism
  `multComap` at every pivot (so the in-chart base direction agrees with the geometric projection
  `mult⁻¹(B) → Mat^{= r}` restricted to the chart). The over-base content is now that the trivialization
  respects the geometric projection, not merely the named in-chart base map.
- **OPEN ITEM — NOT `Flat π` / `FiberBundle` over all of `rankROpen` (NOT a GLOBAL morphism, R1).**
  This is the CHARTWISE over-base local product + chartwise flatness, at every pivot / every
  rank-`= r` point. A single GLOBAL flatness-of-`π` or fibre-bundle statement over the whole
  `rankROpen` additionally needs the target-side overlap-gluing cocycle (roadmap R1
  `targetOverlapTransition`) to assemble the per-chart data; that stays roadmapped and is **not**
  claimed here.
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
  in-chart base direction (Schur-direction coordinate ring `Away (detSchurS …)`), exhibiting the
  chart total ring as a `SchurLoc`-algebra. Proven to agree with the pullback of `mult`'s projection
  after precomposition with `localizeSchur` (projection compatibility, CLOSED in
  `Core.FibreProjectionCompat`, R5). -/
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

/-! ## The DLN bundle is an instance of the abstract `Algebra.StandardFibreChart` (P2.a)

The per-pivot DLN over-base datum is exactly the network-free standard fibre model datum
`Algebra.StandardFibreChart` of `DLNFibre.Core.RingTheory.Determinantal.Atlas`, at
`Total = Away (chartDsigAt I.s I.t)`, `BaseLoc = SchurLoc`, `Fibre = sweepFibreRing`, with structure
map `schurToDsigAt`. So the abstract Core datum is the honest home of the bundle's per-chart fibre
model: the DLN layer instantiates it, dropping the `s/t/σ/τ` threading into one structure. -/

/-- **The DLN per-pivot fibre model as an abstract standard fibre chart (P2.a instance).** The
per-pivot DLN over-base datum (`overBaseChartDatum`) re-packaged as the network-free
`Algebra.StandardFibreChart`: the structure map is `schurToDsigAt`, the over-base trivialization is
`chartDsigAt_schurLocTensorEquiv`, the flatness is `chartDsigAt_flat_over_schurLoc`. This exhibits
the DLN reduced-fibre bundle as an INSTANCE of the Core determinantal-atlas fibre model — the
abstract datum (`StandardFibreChart`) is the honest, reusable home; the DLN chart is an instance. -/
noncomputable def standardFibreChartOfPivot (d : Fin (N + 2) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last (N + 1))) (hq : r ≤ d 0) (I : PivotDatum d r hp hq) :
    Algebra.StandardFibreChart k
      (Localization.Away (chartDsigAt (k := k) d r I.s I.t))
      (SchurLoc (k := k) (d 0) (d (Fin.last (N + 1))) r)
      (sweepFibreRing k d r hp hq) where
  structMap := (overBaseChartDatum d r hp hq I).structMap
  triv := (overBaseChartDatum d r hp hq I).triv
  flat := (overBaseChartDatum d r hp hq I).flat

/-! ## The over-base local-product structure over the rank-`= r` open -/

/-- **The genuine over-base local-product-with-flatness structure over the rank-`= r` open (S5).**
For a fixed `(d, r)`, bundles: (1) the S1 rank-locus identity `isRankLocus`; (2) the scheme
open-cover `cover` of `rankROpen`; (3) per-pivot the HONEST structure map + over-base trivialization
+ flatness over the base (`chart`, an `OverBaseChartDatum`). This UPGRADES S4's
`RankROpenPerPivotLocalProduct` (bare `k`-algebra products) to the over-base version: each chart is
a product OVER the in-chart base direction `SchurLoc` (via a named structure map), flat
over `SchurLoc`. (`schurToDsigAt` agrees with the pullback of `mult`'s projection after precomposition
with `localizeSchur`: projection compatibility, CLOSED in `Core.FibreProjectionCompat`, R5.)
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
rank exactly `r`, there is a pivot datum `I` (carrying `s, t, σ, τ`) whose chart
`basicOpen (chartDsigAt I.s I.t)` contains `P`, such that — OVER the GEOMETRIC `SchurLoc`-algebra
structure `chartDsigAtSchurLocAlgebra` (the in-chart base presentation via the HONEST structure map
`schurToDsigAt = gauge ∘ deep-chart ∘ connecting`, `SchurLoc` = the Schur-direction coordinate ring
`Away (detSchurS …)`) —

* the chart total ring is the product `SchurLoc ⊗_k sweepFibreRing` (a `SchurLoc`-algebra iso, not
  merely a `k`-algebra iso), AND
* the chart total ring is FLAT over `SchurLoc`.

The structure map is named in the TYPE: it is the geometric `schurToDsigAt` (presented as the `letI`
algebra `chartDsigAtSchurLocAlgebra`), NOT an existentially-bound `φ` that any bare `≃ₐ[k]` could
satisfy. So this is a genuine over-base strengthening of S4's bare `≃ₐ[k]` headline, not merely its
re-packaging. (It implies the weaker existential `…_exists_someStructure` below — pick `φ :=
schurToDsigAt` — but not vice versa.) The `flat` conjunct is a corollary of `triv` (the model
`SchurLoc ⊗_k sweepFibreRing` is `SchurLoc`-free), recorded explicitly.

This UPGRADES the S4 headline `reducedFibre_existsProductChartAt_rankEq` (bare
`Nonempty (… ≃ₐ[k] …)`)
to the genuine over-base version. Composed from the S1 rank-bridge, the scheme open-cover, and the
S4b per-pivot over-base data. **Chartwise / uncocycled, base = `SchurLoc`**: it does not itself fold in
that `schurToDsigAt` agrees with the pullback of `mult`'s projection after precomposition with
`localizeSchur` (projection compatibility — proven separately in `Core.FibreProjectionCompat`, R5), and
does NOT assert a global `Flat π` / fibre bundle over all of `rankROpen` (the target-side overlap
cocycle R1 is unbuilt). -/
theorem reducedFibre_existsOverBaseProductChartAt_rankEq (d : Fin (N + 2) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last (N + 1))) (hq : r ≤ d 0)
    (P : PrimeSpectrum (sweepSigmaRing k d r))
    (hP : (universalMatrixResidue d r P).rank = r) :
    ∃ I : PivotDatum d r hp hq,
      P ∈ PrimeSpectrum.basicOpen (chartDsigAt (k := k) d r I.s I.t) ∧
      (letI := chartDsigAtSchurLocAlgebra (k := k) d r hp hq I.s I.t I.σ I.τ I.hσ I.hτ;
        Nonempty (Localization.Away (chartDsigAt (k := k) d r I.s I.t)
          ≃ₐ[SchurLoc (k := k) (d 0) (d (Fin.last (N + 1))) r]
            SchurLoc (k := k) (d 0) (d (Fin.last (N + 1))) r
              ⊗[k] sweepFibreRing k d r hp hq)) ∧
      (letI := chartDsigAtSchurLocAlgebra (k := k) d r hp hq I.s I.t I.σ I.τ I.hσ I.hτ;
        Module.Flat (SchurLoc (k := k) (d 0) (d (Fin.last (N + 1))) r)
          (Localization.Away (chartDsigAt (k := k) d r I.s I.t))) := by
  -- S1: rank `= r` puts `P` in `rankROpen`, the union of the pivot charts.
  have hmem : P ∈ rankROpen (k := k) d r :=
    (mem_rankROpen_iff_rank_universalMatrixResidue_eq d r P).mpr hP
  rw [← iSup_pivot_basicOpen_eq_rankROpen, Set.mem_iUnion] at hmem
  obtain ⟨st, hst⟩ := hmem
  -- chart membership forces injectivity ⟹ a `PivotDatum I` with chart elt `chartDsigAt st.1 st.2`.
  obtain ⟨I, hI⟩ := pivotDatumOfMemBasicOpen d r hp hq st.1 st.2 hst
  -- present the chart at `I.s, I.t` (where the S4b over-base data lives NATIVELY): only membership
  -- Prop transports across `hI : chartDsigAt I.s I.t = chartDsigAt st.1 st.2` (cheap).
  rw [SetLike.mem_coe] at hst
  have hmem' : P ∈ PrimeSpectrum.basicOpen (chartDsigAt (k := k) d r I.s I.t) := by
    rw [← hI] at hst; exact hst
  exact ⟨I, hmem',
    ⟨chartDsigAt_schurLocTensorEquiv d r hp hq I.s I.t I.σ I.τ I.hσ I.hτ⟩,
    chartDsigAt_flat_over_schurLoc d r hp hq I.s I.t I.σ I.τ I.hσ I.hτ⟩

/-- **The over-base local-triviality + flatness headline, the WEAKER `∃ φ` projection (S5).** For
every rank-`= r` prime `P` there is a pivot `(s, t)` whose chart contains `P` together with SOME
`k`-algebra structure map `φ : SchurLoc →ₐ[k] Away (chartDsigAt s t)` over which the chart total
ring is `≃ₐ[SchurLoc] SchurLoc ⊗_k sweepFibreRing` and flat over `SchurLoc`.

This is the OLD form of the headline and is logically WEAKER than
`reducedFibre_existsOverBaseProductChartAt_rankEq`: the structure map is bound existentially, so the
statement is satisfiable by a degenerate pullback `φ := e.symm ∘ includeLeft` from any bare `≃ₐ[k]`,
hence no stronger than S4's bare-`k` headline. The strong form (with the GEOMETRIC `schurToDsigAt`
named in the type) implies this one by instantiating `φ := schurToDsigAt`; retained as a convenience
projection only. -/
theorem reducedFibre_existsOverBaseProductChartAt_rankEq_exists_someStructure
    (d : Fin (N + 2) → ℕ) (r : ℕ)
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
  obtain ⟨I, hmem, htriv, hflat⟩ :=
    reducedFibre_existsOverBaseProductChartAt_rankEq d r hp hq P hP
  exact ⟨I.s, I.t, hmem, schurToDsigAt d r hp hq I.s I.t I.σ I.τ I.hσ I.hτ, htriv, hflat⟩

/-! ## API witnesses (consumer examples)

These are consumer smoke-tests of the structure + headline, **conditional on their inputs** (`P`, `hP`,
a `PivotDatum`, …); they do NOT exhibit an actual rank-`r` prime, a nonempty `rankROpen`, or a
nontrivial fibre ring — so they are API examples, not an existential non-vacuity proof. -/

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

/-- **Pointwise over-base local-product witness (strong form).** The reader-facing headline fires at
any rank-`= r` prime: it sits in a pivot chart whose total ring is, OVER the GEOMETRIC
`chartDsigAtSchurLocAlgebra` (the named `schurToDsigAt` structure), the product
`SchurLoc ⊗_k sweepFibreRing` and flat over `SchurLoc`. -/
example {k : Type} [Field k] [Infinite k] {N : ℕ} (d : Fin (N + 2) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last (N + 1))) (hq : r ≤ d 0)
    (P : PrimeSpectrum (sweepSigmaRing k d r))
    (hP : (universalMatrixResidue d r P).rank = r) :
    ∃ I : PivotDatum d r hp hq,
      P ∈ PrimeSpectrum.basicOpen (chartDsigAt (k := k) d r I.s I.t) ∧
      (letI := chartDsigAtSchurLocAlgebra (k := k) d r hp hq I.s I.t I.σ I.τ I.hσ I.hτ;
        Nonempty (Localization.Away (chartDsigAt (k := k) d r I.s I.t)
          ≃ₐ[SchurLoc (k := k) (d 0) (d (Fin.last (N + 1))) r]
            SchurLoc (k := k) (d 0) (d (Fin.last (N + 1))) r
              ⊗[k] sweepFibreRing k d r hp hq)) ∧
      (letI := chartDsigAtSchurLocAlgebra (k := k) d r hp hq I.s I.t I.σ I.τ I.hσ I.hτ;
        Module.Flat (SchurLoc (k := k) (d 0) (d (Fin.last (N + 1))) r)
          (Localization.Away (chartDsigAt (k := k) d r I.s I.t))) :=
  reducedFibre_existsOverBaseProductChartAt_rankEq d r hp hq P hP

/-- **Pointwise over-base local-product witness (weaker `∃ φ` projection).** The convenience
projection `…_exists_someStructure` fires at any rank-`= r` prime. -/
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
  reducedFibre_existsOverBaseProductChartAt_rankEq_exists_someStructure d r hp hq P hP

end Witness

end DLNFibre.Core
