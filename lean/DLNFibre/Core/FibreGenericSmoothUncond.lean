/-
Copyright (c) 2026. Released under Apache 2.0; see LICENSE.
-/
import DLNFibre.Core.FibreGenericSmooth
import DLNFibre.Core.LocalizationAtComponent
import Mathlib.RingTheory.Localization.BaseChange

/-!
# `DLNFibre.Core.FibreGenericSmoothUncond` — generic smoothness, reduced to one geometric fact
(thread 17, task #110) — ⚠ HISTORICAL / SUPERSEDED for the headline

> **⚠ The unconditional generic-smoothness headline is NOT here — it is
> `Core.FibreComponentOrbitTransport.isSmoothAt_sweepFibre_topComponent`, proved by a SIMPLER route that
> needs no C2(a) (a fibre top component is an fp domain over an alg-closed field, hence generically
> smooth). The "single remaining geometric conditional (C2(a))" described below was the thread-17 LIVE
> state; it is now SUPERSEDED — the bare-orbit C2(a) iso was found dimensionally impossible (thread 20)
> and smoothness was achieved without it. This module's LIVE contribution is the unconditional C1 bridge
> + C3 transport; `isSmoothAt_sweepFibre_of_component_orbitSmooth` below is relabeled dead scaffolding
> (its hypothesis iso does not exist in that shape).**

Thread 16 landed generic smoothness of the reduced fibre as an **honest conditional**: its one open
input is `Algebra.IsSmoothAt k q` of `sweepFibreRing` at a top-component prime `q`. This module
discharges the *commutative-algebra* sub-walls of that conditional and reduces it to a **single
named geometric fact** (C2(a)): that each top-dimensional component of the reduced fibre is, as a
quotient, an orbit-closure ring covered by `Core.OrbitSmooth`.

## What is discharged UNCONDITIONALLY here

* **C1 bridge (reducedness sub-wall (a)+(b)).** `Core.LocalizationAtComponent`:
  `isSmoothAt_minimalPrime_of_isSmoothAt_quotient` — for a reduced Noetherian `k`-algebra, the full
  reducible ring is `IsSmoothAt k I` at a minimal prime `I` (its own generic point) **iff** the
  component ring `R ⧸ I` is smooth at *its* generic point. The "meets exactly one component"
  hypothesis is free (minimal primes are incomparable). `sweepFibreRing` is a reduced (a
  `vanishingIdeal` quotient) finitely-generated `k`-algebra, so this applies.
* **C3 transport (LANDED).** `isSmoothAt_chartDsig_of_isSmoothAt_sweepFibre` — the thread-16 output
  `Smooth k (SchurLoc ⊗_k Away g)` transports to `Algebra.IsSmoothAt k p` of the source pivot chart
  `Away (chartDsig …)` (at every chart prime `p` off the smooth witness `h`). Keystones
  `awayTensorRightAlgEquiv` / `schurTensorAwayAlgEquiv` give the localization-of-base-change
  identity `S ⊗_k Away g ≃ₐ[k] Away (1 ⊗ g)` in `S ⊗_k A`
  (`IsLocalization.tensorProduct_tensorProduct`); the chart iso
  `reducedFibre_chartDsig_tensorEquiv_reducedVariety` + the abstract
  `LocalizationAtComponent.smooth_localizationAway_symm_of_smooth_localizationAway` (one heavy-ring
  instantiation, no `whnf` blowup) + the basic-open bridge `isSmoothAt_of_smooth_localizationAway`
  land the chart `IsSmoothAt`.

## The thread-17 C2(a) conditional — SUPERSEDED (see ⚠ banner above; kept as historical scaffolding)

`isSmoothAt_sweepFibre_of_component_orbitSmooth`: GIVEN that every top-dim minimal prime `I` of
`sweepFibreRing` has a `k`-algebra iso `sweepFibreRing ⧸ I ≃ₐ[k] orbitRing M` to an orbit-closure
coordinate ring — the C2(a) fact — then `Algebra.IsSmoothAt k I` of `sweepFibreRing`, via
`OrbitSmooth.isSmoothAt_normalFormIdeal` (+ a domain "smooth closed point ⟹ smooth generic point"
step, transported across the iso — no `⊥ ↦ normalFormIdeal` correspondence needed) and the C1
bridge. **C2(a) is NOT
discharged here**: it needs a fibre-component ↔ orbit-closure theory (an explicit
`sweepFibreRing ⧸ I ≃ orbitRing M`) that this harness does not build (the θ-count is established via
codimension/`ncard` chains, never labelling a component by an orbit). Codex-confirmed multi-module
wall.

**Dependency rule:** `Core` only — never import `DLNFibre.DLN`.
-/

namespace DLNFibre.Core

open MvPolynomial Matrix Algebra
open scoped TensorProduct

universe u

variable {k : Type u} [Field k]

/-! ## `sweepFibreRing` is reduced and Noetherian (feeds the C1 bridge) -/

variable {N : ℕ}

/-- `sweepFibreRing` is **reduced** (over `[IsAlgClosed k]`): it is
`MvPolynomial (RepCoord d) k ⧸ vanishingIdeal(F)`, and the vanishing ideal of any subset is radical
(strong Nullstellensatz, `MvPolynomial.vanishingIdeal_isRadical`), so the quotient is reduced
(`Ideal.isRadical_iff_quotient_reduced`). -/
instance isReduced_sweepFibreRing [IsAlgClosed k] (d : Fin (N + 2) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last (N + 1))) (hq : r ≤ d 0) :
    IsReduced (sweepFibreRing k d r hp hq) :=
  (Ideal.isRadical_iff_quotient_reduced _).mp
    (vanishingIdeal_isRadical (σ := RepCoord d) (k := k) (sweepFibre k d r hp hq))

/-- `sweepFibreRing` is **Noetherian**: a quotient of a Noetherian polynomial ring over the field
`k` (finitely many representation coordinates). -/
instance isNoetherianRing_sweepFibreRing (d : Fin (N + 2) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last (N + 1))) (hq : r ≤ d 0) :
    IsNoetherianRing (sweepFibreRing k d r hp hq) :=
  isNoetherianRing_of_surjective (MvPolynomial (RepCoord d) k) _
    (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective

/-- `sweepSigmaRing` is **finitely presented** over `k` (a quotient of the Noetherian polynomial
ring in the representation coordinates). -/
instance finitePresentation_sweepSigmaRing (d : Fin (N + 2) → ℕ) (r : ℕ) :
    Algebra.FinitePresentation k (sweepSigmaRing k d r) :=
  Algebra.FinitePresentation.quotient
    (IsNoetherian.noetherian (vanishingIdeal k (sweepSigma k d r)))

/-- `Away (chartDsig …)` is **finitely presented** over `k`: it is `Localization.Away` of the
finitely-presented `sweepSigmaRing` (`IsLocalization.Away.finitePresentation`), composed by
`FinitePresentation.trans`. -/
instance finitePresentation_away_chartDsig (d : Fin (N + 2) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last (N + 1))) (hq : r ≤ d 0) :
    Algebra.FinitePresentation k (Localization.Away (chartDsig k d r hp hq)) :=
  haveI : Algebra.FinitePresentation (sweepSigmaRing k d r)
      (Localization.Away (chartDsig k d r hp hq)) :=
    IsLocalization.Away.finitePresentation (chartDsig k d r hp hq)
  Algebra.FinitePresentation.trans k (sweepSigmaRing k d r)
    (Localization.Away (chartDsig k d r hp hq))

/-! ## The C2(a)-conditional: `IsSmoothAt` of `sweepFibreRing` at a top-component prime -/

/-- ⚠ **HISTORICAL SCAFFOLDING — do NOT use as a reduction.** The hypothesis iso
`e : sweepFibreRing ⧸ I ≃ₐ[k] orbitRing M` (a *bare* orbit-closure ring) is **globally
unsatisfiable in this shape**: by the chart dimension identity `dim Σ^r = dim F + δ`
(`δ = r·(d_last + d_0 − r) > 0` for `r ≥ 1`, `Core.ChartSweepWiring`), a fibre top component has
dimension `dim F`, while a shifted orbit closure has dimension `dim F − δ` — a Krull-dim-preserving
ring iso cannot equate them (thread-20 finding, Codex-confirmed). This theorem is **valid but
vacuous in practice** (a true implication from an unsatisfiable premise); it is leftover from the
abandoned orbit-iso route to C2(a).

**SUPERSEDED** by the direct domain argument
`Core.FibreComponentOrbitTransport.isSmoothAt_sweepFibre_topComponent` (and
`isSmoothAt_sweepFibre_component`): a fibre component `sweepFibreRing ⧸ I` is a finitely-presented
domain over the perfect field `k`, hence generically smooth, giving `Algebra.IsSmoothAt k I`
**fully unconditionally** with no orbit iso. Kept for the honest record; do not build a reduction
to this. -/
@[deprecated "superseded by isSmoothAt_sweepFibre_topComponent (direct fp-domain route); \
hypothesis iso is globally unsatisfiable — historical scaffolding, do not use"
  (since := "2026-06-26")]
theorem isSmoothAt_sweepFibre_of_component_orbitSmooth [IsAlgClosed k]
    {d' : Fin (N + 1) → ℕ} (d : Fin (N + 2) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last (N + 1))) (hq : r ≤ d 0)
    (I : Ideal (sweepFibreRing k d r hp hq)) [I.IsPrime]
    (hImin : I ∈ minimalPrimes (sweepFibreRing k d r hp hq))
    (M : Tuple (k := k) d')
    (e : (sweepFibreRing k d r hp hq ⧸ I) ≃ₐ[k] orbitRing M) :
    Algebra.IsSmoothAt k I :=
  isSmoothAt_minimalPrime_of_componentEquiv_domain k I hImin e
    (normalFormIdeal M) (isSmoothAt_normalFormIdeal M)

/-! ## C3 — transport the tensor-factor smoothness to the source chart `Away chartDsig`

The thread-16 output is `Smooth k (SchurLoc ⊗_k Localization.Away g)` for a fibre element `g ∉ q`.
We transport it to `Algebra.IsSmoothAt k p` of the source pivot chart `Away (chartDsig …)`, across
the banked product trivialization `reducedFibre_chartDsig_tensorEquiv_reducedVariety`
and the localization-of-base-change identification `SchurLoc ⊗_k Away g ≃ Away (1 ⊗ g)`. -/

section TensorAway

variable {S : Type u} [CommRing S] [Algebra k S] {A : Type u} [CommRing A] [Algebra k A]
  (g : A)

/-- The `(A ⊗_k S)`-algebra structure on `Localization.Away g ⊗_k S` induced by `A → Away g`, via
`Algebra.TensorProduct.map` (mirrors `FibreBundleReduced`'s local `tensorAlgebra`). Feeds
`IsLocalization.tensorProduct_tensorProduct`. -/
noncomputable local instance tensorAlgebraC3 :
    Algebra (A ⊗[k] S) (Localization.Away g ⊗[k] S) :=
  (Algebra.TensorProduct.map
    (IsScalarTower.toAlgHom k A (Localization.Away g)) (AlgHom.id k S)).toRingHom.toAlgebra

/-- The local `tensorAlgebraC3` structure forms a scalar tower with the base `A`. -/
local instance tensorIsScalarTowerC3 :
    IsScalarTower A (A ⊗[k] S) (Localization.Away g ⊗[k] S) := by
  refine IsScalarTower.of_algebraMap_eq (fun x ↦ ?_)
  show algebraMap A (Localization.Away g ⊗[k] S) x
      = (Algebra.TensorProduct.map (IsScalarTower.toAlgHom k A (Localization.Away g))
          (AlgHom.id k S)) (algebraMap A (A ⊗[k] S) x)
  rw [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.algebraMap_apply,
    Algebra.algebraMap_self_apply, Algebra.TensorProduct.map_tmul, map_one,
    IsScalarTower.coe_toAlgHom']

/-- **The away-localization tensor identification (abstract C3 keystone).** For a commutative
`k`-algebra `S`, a `k`-algebra `A`, and `g : A`, tensoring the away-localization `Localization.Away
g` (of `A`) by `S` on the right is the away-localization of `A ⊗_k S` at the left inclusion `g ⊗ 1`:

> `Localization.Away g ⊗_k S  ≃ₐ[k]  Localization.Away (g ⊗ₜ 1 : A ⊗_k S)`.

Built from `IsLocalization.tensorProduct_tensorProduct` (`Away g ⊗_k S` is the localization of
`A ⊗_k S` at the image of `powers g`) glued to `Localization.Away (g ⊗ 1)` by
`IsLocalization.algEquiv`; the image submonoid `algebraMapSubmonoid (A ⊗_k S) (powers g)` is
`powers (g ⊗ 1)` (`Submonoid.map_powers`). -/
noncomputable def awayTensorRightAlgEquiv :
    Localization.Away g ⊗[k] S ≃ₐ[k]
      Localization.Away (algebraMap A (A ⊗[k] S) g) := by
  haveI hloc : IsLocalization (Algebra.algebraMapSubmonoid (A ⊗[k] S) (Submonoid.powers g))
      (Localization.Away g ⊗[k] S) := by
    refine IsLocalization.tensorProduct_tensorProduct (R := k) (S := S) (A := A)
      (M := Submonoid.powers g) (B := Localization.Away g) ?_
    show ((Algebra.TensorProduct.map
        (IsScalarTower.toAlgHom k A (Localization.Away g)) (AlgHom.id k S)).toRingHom).comp
          Algebra.TensorProduct.includeRight.toRingHom
        = Algebra.TensorProduct.includeRight.toRingHom
    have hmap := Algebra.TensorProduct.map_comp_includeRight
      (IsScalarTower.toAlgHom k A (Localization.Away g)) (AlgHom.id k S)
    rw [AlgHom.comp_id] at hmap
    exact congrArg AlgHom.toRingHom hmap
  have hpow : Algebra.algebraMapSubmonoid (A ⊗[k] S) (Submonoid.powers g)
      = Submonoid.powers (algebraMap A (A ⊗[k] S) g) := by
    rw [Algebra.algebraMapSubmonoid, Submonoid.map_powers]
  rw [hpow] at hloc
  exact (IsLocalization.algEquiv (Submonoid.powers (algebraMap A (A ⊗[k] S) g))
    (Localization.Away g ⊗[k] S) (Localization.Away (algebraMap A (A ⊗[k] S) g))).restrictScalars k

/-- **`S ⊗_k Localization.Away g` is the away-localization of `S ⊗_k A` at `1 ⊗ g`.** The
left-tensor orientation (matching the thread-16 output `SchurLoc ⊗_k Away g`): flip to the right
orientation by `Algebra.TensorProduct.comm`, apply `awayTensorRightAlgEquiv`, and carry the
localized element `g ⊗ 1` back to `1 ⊗ g = includeRight g` (`comm_tmul`). -/
noncomputable def schurTensorAwayAlgEquiv :
    S ⊗[k] Localization.Away g ≃ₐ[k]
      Localization.Away (Algebra.TensorProduct.includeRight (R := k) (A := S) (B := A) g) := by
  -- `S ⊗ Away g ≃ Away g ⊗ S ≃ Away (g ⊗ₜ 1 in A ⊗ S)`.
  refine (Algebra.TensorProduct.comm k S (Localization.Away g)).trans
    ((awayTensorRightAlgEquiv (S := S) g).trans ?_)
  -- `Away (g ⊗ 1 in A ⊗ S) ≃ Away (1 ⊗ g in S ⊗ A)` via `comm` carrying `g⊗1 ↦ 1⊗g`.
  have H : Submonoid.map (Algebra.TensorProduct.comm k A S :
        (A ⊗[k] S) →+* (S ⊗[k] A)) (Submonoid.powers (algebraMap A (A ⊗[k] S) g))
      = Submonoid.powers (Algebra.TensorProduct.includeRight (R := k) (A := S) (B := A) g) := by
    rw [Submonoid.map_powers]
    congr 1
  exact IsLocalization.algEquivOfAlgEquiv
    (Localization.Away (algebraMap A (A ⊗[k] S) g))
    (Localization.Away (Algebra.TensorProduct.includeRight (R := k) (A := S) (B := A) g))
    (Algebra.TensorProduct.comm k A S) H

end TensorAway

/-! ## C3 — the source chart `Away chartDsig` is smooth on a basic open -/

/-- **C3 — the reduced fibre's source pivot chart is smooth on a basic open.** GIVEN
`IsSmoothAt k q` of `sweepFibreRing` at a top-component prime `q` (the open input, discharged
unconditionally-modulo-C2(a) by `isSmoothAt_sweepFibre_of_component_orbitSmooth`), there is a chart
element `h : Away (chartDsig …)` with `Algebra.Smooth k (Localization.Away h)` — the smooth basic
open `{h ≠ 0}` of the source pivot chart. Chain:

* thread-16 `smooth_schurLoc_tensor_away_of_isSmoothAt_sweepFibre` gives `g ∉ q` with
  `Smooth k (SchurLoc ⊗_k Away g)`;
* `schurTensorAwayAlgEquiv g` (C3 keystone) identifies `SchurLoc ⊗_k Away g ≃ₐ[k] Away (1 ⊗ g)` in
  `SchurLoc ⊗_k sweepFibreRing`, so `Smooth k (Away (1 ⊗ g))` (`Smooth.of_equiv`);
* the banked chart iso `e := FibreBundleReduced.reducedFibre_chartDsig_tensorEquiv_reducedVariety :
  Away chartDsig ≃ₐ[k] SchurLoc ⊗_k sweepFibreRing` and the abstract transport
  `LocalizationAtComponent.smooth_localizationAway_symm_of_smooth_localizationAway` carry it back to
  `Smooth k (Away (e.symm (1 ⊗ g)))` on the chart (one heavy-ring instantiation, no `whnf` blowup).

`isSmoothAt_of_smooth_localizationAway` (thread-16 bridge) then gives `Algebra.IsSmoothAt k p
(Away chartDsig)` at any chart prime `p ∌ h`. Needs `[Infinite k]` (the chart `e`) and
`[IsAlgClosed k]` (thread-16). -/
theorem exists_smooth_localizationAway_chartDsig_of_isSmoothAt_sweepFibre
    [IsAlgClosed k] [Infinite k] (d : Fin (N + 2) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last (N + 1))) (hq : r ≤ d 0)
    (q : Ideal (sweepFibreRing k d r hp hq)) [q.IsPrime]
    (hq_smooth : Algebra.IsSmoothAt k q) :
    ∃ h : Localization.Away (chartDsig k d r hp hq), Algebra.Smooth k (Localization.Away h) := by
  obtain ⟨g, _, hg_smooth⟩ :=
    smooth_schurLoc_tensor_away_of_isSmoothAt_sweepFibre d r hp hq q hq_smooth
  -- `Smooth k (Away (1 ⊗ g))` in `SchurLoc ⊗ sweepFibreRing`.
  haveI hsmT : Algebra.Smooth k (Localization.Away
      (Algebra.TensorProduct.includeRight (R := k)
        (A := SchurLoc (k := k) (d 0) (d (Fin.last (N + 1))) r)
        (B := sweepFibreRing k d r hp hq) g)) :=
    Algebra.Smooth.of_equiv
      (schurTensorAwayAlgEquiv (S := SchurLoc (k := k) (d 0) (d (Fin.last (N + 1))) r) g)
  -- pull back across the chart iso `e` via the abstract transport (one heavy-ring instantiation).
  exact ⟨_, smooth_localizationAway_symm_of_smooth_localizationAway k
    (reducedFibre_chartDsig_tensorEquiv_reducedVariety (k := k) d r hp hq) _ hsmT⟩

/-- **C3 — the smooth chart witness is NON-VACUOUS (its basic open is nonempty).** The same chart
element `h` as `exists_smooth_localizationAway_chartDsig_of_isSmoothAt_sweepFibre`, additionally
certified `¬ IsNilpotent h` — so the smooth basic open `D(h) = {h ≠ 0}` is a **nonempty** open of
the source pivot chart (`PrimeSpectrum.basicOpen h ≠ ⊥`). The smoothness conclusion is therefore not
vacuous: there genuinely are chart primes off `h` at which the chart is smooth.

`h = e.symm (1 ⊗ g)` for the singular-witness element `g ∉ q` (from
`smooth_schurLoc_tensor_away_of_isSmoothAt_sweepFibre`); since `q` is prime `g ≠ 0`, and
`sweepFibreRing` is reduced so `¬ IsNilpotent g`. Injectivity of `includeRight : sweepFibreRing →
SchurLoc ⊗_k sweepFibreRing` (from `SchurLoc` being a domain, hence `Nontrivial`, so `algebraMap k
SchurLoc` is injective) and of the chart iso `e.symm` transports non-nilpotence to `h`
(`IsNilpotent.map_iff`). This is the honest non-vacuity strengthening; it does **not** yet certify
that `D(h)` meets the chart image of the chosen component `q`'s generic point — see the note on the
chart headline `isSmoothAt_chartDsig_topComponent_nonvacuous`. -/
theorem exists_smooth_localizationAway_chartDsig_nonvacuous
    [IsAlgClosed k] [Infinite k] (d : Fin (N + 2) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last (N + 1))) (hq : r ≤ d 0)
    (q : Ideal (sweepFibreRing k d r hp hq)) [q.IsPrime]
    (hq_smooth : Algebra.IsSmoothAt k q) :
    ∃ h : Localization.Away (chartDsig k d r hp hq),
      ¬ IsNilpotent h ∧ Algebra.Smooth k (Localization.Away h) := by
  obtain ⟨g, hgq, hg_smooth⟩ :=
    smooth_schurLoc_tensor_away_of_isSmoothAt_sweepFibre d r hp hq q hq_smooth
  -- `g ≠ 0` (prime `q` contains `0`); `sweepFibreRing` reduced ⟹ `¬ IsNilpotent g`.
  have hg0 : g ≠ 0 := fun h ↦ hgq (h ▸ q.zero_mem)
  have hgnil : ¬ IsNilpotent g := fun hn ↦ hg0 (IsReduced.eq_zero g hn)
  -- `SchurLoc` is a domain (localization of a domain at `detSchurS ≠ 0`), hence `Nontrivial` — so
  -- `algebraMap k SchurLoc` is injective.
  haveI : IsDomain (SchurLoc (k := k) (d 0) (d (Fin.last (N + 1))) r) :=
    IsLocalization.isDomain_of_le_nonZeroDivisors (SchurLoc (k := k) (d 0) (d (Fin.last (N + 1))) r)
      (powers_le_nonZeroDivisors_of_noZeroDivisors
        (detSchurS_ne_zero (k := k) (d 0) (d (Fin.last (N + 1))) r))
  -- transport non-nilpotence: `includeRight` injective (`k`-flat base), then chart iso `e.symm`.
  set Tg : SchurLoc (k := k) (d 0) (d (Fin.last (N + 1))) r ⊗[k] sweepFibreRing k d r hp hq :=
    Algebra.TensorProduct.includeRight (R := k)
      (A := SchurLoc (k := k) (d 0) (d (Fin.last (N + 1))) r)
      (B := sweepFibreRing k d r hp hq) g with hTg
  have hTgnil : ¬ IsNilpotent Tg := by
    rw [hTg, IsNilpotent.map_iff
      (Algebra.TensorProduct.includeRight_injective (B := sweepFibreRing k d r hp hq)
        (algebraMap k (SchurLoc (k := k) (d 0) (d (Fin.last (N + 1))) r)).injective)]
    exact hgnil
  haveI hsmT : Algebra.Smooth k (Localization.Away Tg) :=
    Algebra.Smooth.of_equiv
      (schurTensorAwayAlgEquiv (S := SchurLoc (k := k) (d 0) (d (Fin.last (N + 1))) r) g)
  set e := reducedFibre_chartDsig_tensorEquiv_reducedVariety (k := k) d r hp hq with he
  refine ⟨e.symm Tg, ?_, smooth_localizationAway_symm_of_smooth_localizationAway k e Tg hsmT⟩
  -- `e.symm` injective ⟹ `¬ IsNilpotent (e.symm Tg)`.
  rw [IsNilpotent.map_iff e.symm.injective]
  exact hTgnil

/-- **C3 headline — `IsSmoothAt` of the source pivot chart at primes off the singular witness.**
GIVEN `IsSmoothAt k q` of `sweepFibreRing` at a top-component prime `q`, there is a chart element
`h : Away (chartDsig …)` whose smooth basic open `{h ≠ 0}` certifies `Algebra.IsSmoothAt k p` of the
source pivot chart at **every** chart prime `p` with `h ∉ p`: the existence
(`exists_smooth_localizationAway_chartDsig_of_isSmoothAt_sweepFibre`) plus the basic-open bridge
`isSmoothAt_of_smooth_localizationAway`.

So once C2(a) discharges the input `IsSmoothAt k q`
(`isSmoothAt_sweepFibre_of_component_orbitSmooth`), the source chart is smooth on the basic open
of `h`. -/
theorem isSmoothAt_chartDsig_of_isSmoothAt_sweepFibre
    [IsAlgClosed k] [Infinite k] (d : Fin (N + 2) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last (N + 1))) (hq : r ≤ d 0)
    (q : Ideal (sweepFibreRing k d r hp hq)) [q.IsPrime]
    (hq_smooth : Algebra.IsSmoothAt k q) :
    ∃ h : Localization.Away (chartDsig k d r hp hq),
      ∀ (p : Ideal (Localization.Away (chartDsig k d r hp hq))) [p.IsPrime],
        h ∉ p → Algebra.IsSmoothAt k p := by
  obtain ⟨h, hh_smooth⟩ :=
    exists_smooth_localizationAway_chartDsig_of_isSmoothAt_sweepFibre d r hp hq q hq_smooth
  exact ⟨h, fun p _ hhp ↦ isSmoothAt_of_smooth_localizationAway hhp hh_smooth⟩

end DLNFibre.Core
