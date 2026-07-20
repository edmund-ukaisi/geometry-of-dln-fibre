# Statement card — `Core.FibreComponentOrbit` (thread 20, task #119, C2(a))

**Status:** sorry-free, axiom-clean `[propext, Classical.choice, Quot.sound]`. Whole library green
(module built standalone, 3084 jobs; not yet wired into `DLNFibre.lean` — controller owns the
aggregator). Module: `lean/DLNFibre/Core/FibreComponentOrbit.lean`.

## The fidelity finding (escalated, NOT silently rewritten)

The thread-17 C2(a) interface `isSmoothAt_sweepFibre_of_component_orbitSmooth` takes
`e : sweepFibreRing ⧸ I ≃ₐ[k] orbitRing M`. **This `e` cannot exist** for the natural `M`: by the
chart identity `dim Σ^r = dim F + δ` (`ChartSweepWiring.sweep_of_localizedChartAlgEquiv`,
`δ = r·(d_last + d_0 − r)`), a fibre top component has dimension `dim F`, while a shifted orbit
closure `Ō_M` (over `d − r`) has dimension `dim F − δ`. The fibre top component is the orbit closure
**times an affine factor `A^δ`** (the C-part). Confirmed: (i) my dimension arithmetic, (ii) decorrelated
Codex consult (`codex/route-answer.md`), (iii) numeric `(2,2,2), r=1`: fibre comp dim 4, residual
orbit (over `(1,1,1)`) dim 1, δ = 3.

So the bare-`orbitRing` C2(a) target is the wrong interface. The dimension-correct target is
`sweepFibreRing ⧸ I ≃ₐ[k] MvPolynomial η (orbitRing M)` (`η` = the δ affine coords).

## Theorems delivered

### Dimension-correct C2(a) consumer (the headline)
```lean
theorem isSmoothAt_sweepFibre_of_component_orbitPolyEquiv [IsAlgClosed k]
    {d' : Fin (N + 1) → ℕ} (d : Fin (N + 2) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last (N + 1))) (hq : r ≤ d 0)
    (I : Ideal (sweepFibreRing k d r hp hq)) [I.IsPrime]
    (hImin : I ∈ minimalPrimes (sweepFibreRing k d r hp hq))
    (M : Tuple (k := k) d') (n : ℕ)
    (e : (sweepFibreRing k d r hp hq ⧸ I) ≃ₐ[k] MvPolynomial (Fin n) (orbitRing M)) :
    Algebra.IsSmoothAt k I
```
English: given the dimension-correct fibre-component iso (orbit ring × `A^n`), the reduced fibre is
smooth at the component's generic point. Discharges the C2(a) consumer up to the *true* iso `e`.

### Supporting (all unconditional, banked-reusable CA)
- `smooth_localizationAway_C_of_smooth_localizationAway` — `Smooth k (Away g) ⟹ Smooth k (Away (C g))`
  in `MvPolynomial (Fin n) A` (reuses C3 keystone `schurTensorAwayAlgEquiv` + the banked transport
  `smooth_localizationAway_symm_of_smooth_localizationAway`).
- `isSmoothAt_bot_mvPolynomial_of_isSmoothAt` — an fp domain `A` smooth at a prime ⟹
  `MvPolynomial (Fin n) A` is `IsSmoothAt k ⊥` (abstract; one heavy-ring instantiation).
- `exists_isSmoothAt_mvPolynomial_orbitRing` — `MvPolynomial (Fin n) (orbitRing M)` is `IsSmoothAt`
  at a prime (fp domain; orbit smooth at normal form `OrbitSmooth.isSmoothAt_normalFormIdeal`).
- `finitePresentation_mvPolynomial_orbitRing`, `isDomain_mvPolynomial_orbitRing` (instances).

### Sigma-side labeled component ↔ orbit iso (UNCONDITIONAL — the first "label a component by an orbit")
```lean
theorem exists_sigma_topComponent_orbitRingEquiv [IsAlgClosed k] [CharZero k]
    (d : Fin (N + 1) → ℕ) (r : ℕ) (h : (kostantPartitions d r).Nonempty)
    (q : Ideal (MvPolynomial (RepCoord d) k ⧸ sigmaIdeal (k := k) d r))
    (hq : q ∈ TopDimMinPrimes (MvPolynomial (RepCoord d) k ⧸ sigmaIdeal (k := k) d r)) :
    ∃ (m : Fin (N + 1) × Fin (N + 1) → ℕ) (hm : m ∈ kostantPartitions d r),
      Nonempty (((MvPolynomial (RepCoord d) k ⧸ sigmaIdeal (k := k) d r) ⧸ q)
        ≃ₐ[k] orbitRing (realizerD (k := k) hm))
```
English: every top-dim component of `O(Σ̄^r)` IS (as a `k`-algebra) the coordinate ring of a Kostant
orbit closure — **exactly, no affine factor** (the C-part lives only on the fibre side of the chart).
Built unconditionally from the θ-count chain's labeled sigma facts (`bijOn_comap_quotTopDimSet`,
`quotTopDimSet_sigma_eq_topComponents`, `exists_kostantPartition_partitionIdeal_eq_of` discharged by
`cCodim_zero_strict`) + the third iso theorem (`quotQuotEquivQuotOfLEₐ`) +
`partitionIdeal_eq_orbitIdeal_realizerD` (`vanishingIdeal_orbitRankLocus_eq_orbitSet`). This confirms
the dimension story and is the labeled *target* the eventual fibre→sigma transport lands in.
- `partitionIdeal_eq_orbitIdeal_realizerD` — `partitionIdeal d r m = orbitIdeal (realizerD m)`.

## What remains for FULLY-unconditional smoothness (the genuine C2(a) wall)

The remaining open input is now `e` itself: the intrinsic **block-triangular fibre theorem** — that
a fibre top component is, as a reduced variety, `Ō_M × A^δ` (`sweepFibreRing ⧸ I ≃ₐ[k]
MvPolynomial η (orbitRing M)`). The harness has the *sigma* end labeled (above) and the chart
AlgEquiv `chartLocalizedAlgEquiv : Away dsig ≃ₐ[k] Away gF` + the product trivialization
`Away chartGfib ≃ₐ[k] SchurLoc ⊗_k sweepFibreRing` (`FibreBundleReduced`), but the count chain
transports fibre↔sigma only at `ncard` level. Building `e` requires a *labeled* fibre→sigma component
transport across: W3 radical (likely free), the Schur poly extension (`map C` of minimal primes), the
`gF`/`dsig` localizations + chart `e`, and the W0 `δ`-shift. Codex line-tier: ~800–1800 LoC; hardest
rung = the intrinsic vanishing-ideal/coordinate-iso per component. NOT attempted in this tide.

## Aggregator import line (for the controller)
`import DLNFibre.Core.FibreComponentOrbit`
(after `DLNFibre.Core.FibreGenericSmoothUncond`; new imports it pulls: `TopDimMinPrimesW0`,
`CCodimCornerMono`, `Mathlib.RingTheory.TensorProduct.MvPolynomial` — all already in the library).
