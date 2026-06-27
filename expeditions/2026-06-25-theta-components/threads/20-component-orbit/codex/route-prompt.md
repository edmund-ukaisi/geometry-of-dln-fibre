# Codex consult — route for C2(a): `sweepFibreRing ⧸ I ≃ₐ[k] orbitRing M`

You are a Lean 4 + Mathlib (v4.29) commutative-algebra / algebraic-geometry design reviewer.
This is a DESIGN-REVIEW consult: I want you to pressure-test a route and pick the cleanest path
to a single target theorem, BEFORE I spend ~1000+ lines building it. Do not write Lean code;
give a route map, the load-bearing lemmas, and the failure modes.

## The target (the sole open input for unconditional generic smoothness)

```
theorem isSmoothAt_sweepFibre_of_component_orbitSmooth ... :
    (I : Ideal (sweepFibreRing k d r hp hq)) [I.IsPrime]
    (hImin : I ∈ minimalPrimes (sweepFibreRing k d r hp hq))
    (M : Tuple (k := k) d')      -- d' : Fin (N+1) → ℕ
    (e : (sweepFibreRing k d r hp hq ⧸ I) ≃ₐ[k] orbitRing M)
    → Algebra.IsSmoothAt k I
```

The consumer is ALREADY proved (it just plugs `e` into a packaged C1+C2 bridge). The OPEN task is:
**For each top-dimensional minimal prime `I` of `sweepFibreRing`, produce SOME orbit tuple `M` over
`d' : Fin (N+1) → ℕ` and a `k`-algebra iso `e : sweepFibreRing ⧸ I ≃ₐ[k] orbitRing M`.**

Equivalently I want a headline like:
```
theorem isSmoothAt_sweepFibre_topComponent (I top-dim min prime) : Algebra.IsSmoothAt k I
```
that DOES NOT take `M`/`e` as hypotheses — discharging them internally.

## The objects (all `MvPolynomial (RepCoord ·) k ⧸ vanishingIdeal(·)` quotients)

- `d : Fin (N+2) → ℕ` (the FIBRE/sweep dimension vector; has an interior vertex).
- `sweepFibreRing k d r hp hq = MvPolynomial (RepCoord d) k ⧸ vanishingIdeal(sweepFibre)`,
  `sweepFibre = canonicalCoord d '' fibre d (normalForm ...)`. Reduced + Noetherian.
- `orbitRing M = MvPolynomial (RepCoord d') k ⧸ orbitIdeal M`, `d' : Fin (N+1) → ℕ`,
  `orbitIdeal M = vanishingIdeal(orbitSet M)`. Domain (orbit irreducible).
- `partitionIdeal d' r m = orbitIdeal (realizerD m) = vanishingIdeal(canonicalCoord '' orbitRankLocus (realizerD m))`
  for a Kostant partition `m ∈ kostantPartitions d' r`. So
  `MvPolynomial (RepCoord d') k ⧸ partitionIdeal d' r m = orbitRing (realizerD m)` definitionally.

## What the harness HAS (real lemmas, all sorry-free, axiom-clean)

The θ-count is established by a chain of SEVEN rungs, but it is an **`ncard` chain** —
`(TopDimMinPrimes A).ncard = (TopDimMinPrimes B).ncard` at each rung. The rungs:
```
cTheta(d-r)
 =E0= (TopDimMinPrimes O(Σ̄^r)).ncard         -- O(Σ̄^r)=R'⧸sigmaIdeal d' r, d'=Fin(N+2)→ℕ here? NO: d'=Fin((N)+1)... see note
 =W0= (TopDimMinPrimes O(Σ^r)).ncard          -- exact-rank locus; SET equality available (quotTopDimSet)
 =W1= (TopDimMinPrimes O(Σ^r)[1/dsig]).ncard  -- localization away dsig; ncard only (avoidance)
 =chartE= (TopDimMinPrimes (O(F)[Schur])[1/gF]).ncard  -- via the chart AlgEquiv `e`; ncard only
 =W2= (TopDimMinPrimes O(F)[Schur]).ncard      -- ncard only (flat route)
 =poly= (TopDimMinPrimes O(F)).ncard           -- strip Schur poly ext; ncard only
 =W3= (TopDimMinPrimes O(fibre)).ncard         -- radical; ncard only
```

Note on dimension index: the sigma side `O(Σ̄^r)` is at `Fin ((N+1)+1) = Fin (N+2)` (SAME ambient
`RepCoord d` as the fibre), instantiated via `(N := N+1)`. The orbit/`partitionIdeal`/`topComponents`
infrastructure (`ThetaComponentCount`) is at a GENERIC `d' : Fin (M+1) → ℕ`; the sigma application
uses `d' := d : Fin (N+2) → ℕ` (so `M = N+1`). The shifted `cTheta(d - r)` index is `dminus d r`.

LABELED (set-level / comap-bijection) facts that DO exist:
1. `bijOn_comap_quotTopDimSet I : Set.BijOn (comap (Quotient.mk I)) (TopDimMinPrimes (R⧸I)) (quotTopDimSet I)`
   where `quotTopDimSet I = {minimal primes p ⊇ I of R with ringKrullDim(R⧸p)=ringKrullDim(R⧸I)}`.
2. `quotTopDimSet_sigma_eq_topComponents : quotTopDimSet (sigmaIdeal d r) = topComponents d r h`.
3. `exists_kostantPartition_partitionIdeal_eq_of` (with `cCodim_zero_strict` discharging hMonoStrict):
   **every top component `p ∈ topComponents d r h` equals `partitionIdeal d r m` for some Kostant
   `m ∈ kostantPartitions d r`** — i.e. every top component of `O(Σ̄^r)` IS an orbit-closure ideal.
   THIS IS UNCONDITIONAL AND LABELED at the sigma level.
4. The chart AlgEquiv `chartLocalizedAlgEquiv : Localization.Away dsig ≃ₐ[k] Localization.Away gF`
   (dsig in O(Σ^r); gF in O(F)[Schur]). This is a genuine ring iso of the LOCALIZED rings.

What is NOT labeled: the W1/chartE/W2/poly/W3 rungs are `ncard`-only (cardinality via avoidance +
`topDimMinPrimes_ncard_away_eq_of_fgDomain`); they do NOT carry an individual component `I` of the
fibre to a specific component of `O(Σ̄^r)`.

## The question

For a top-dim minimal prime `I` of `sweepFibreRing` I want `M` and `sweepFibreRing⧸I ≃ₐ[k] orbitRing M`.
At the SIGMA end (fact 3) every top component already IS `orbitRing (realizerD m)`. So the wall is the
labeled fibre→sigma transport of an individual `I`, across:
  (a) the radical W3 (sweepFibreRing vs O(fibre)) — but `sweepFibreRing` is already the radical/reduced
      coordinate ring, so this may be free;
  (b) the Schur polynomial extension (poly): `O(F)[Schur] ↦ O(F)`; minimal primes of `R[X_i]` are
      `map C` of minimal primes of `R` (the harness has `map_comap_C_of_mem_minimalPrimes`);
  (c) the localization at `gF` / `dsig` and the chart AlgEquiv `e` (the localization-away ↔ basic-open
      minimal-prime correspondence);
  (d) the `δ`-shift / `Σ^r ↔ Σ̄^r` (W0 — but this has a SET equality `quotTopDimSet`).

### Concrete asks
1. Is the cleanest route to LABEL each rung (build a `comap`/`map`/`AlgEquiv` correspondence carrying
   a single fibre top-component `I` to a single sigma top-component `p = partitionIdeal m`, then
   `sweepFibreRing⧸I ≃ orbitRing(realizerD m)`)? Or is there a SHORTER route that bypasses the chart
   chain entirely — e.g. directly identifying `sweepFibreRing ⧸ I` with `orbitRing M` by a more
   intrinsic geometric argument (the fibre over normalForm E_r is itself, set-theoretically, a union
   of shifted orbit closures, so each top component IS a shifted orbit closure VARIETY, giving the
   ring iso by `vanishingIdeal` of equal varieties)?

2. KEY sub-question on route (intrinsic): The fibre `mult⁻¹(E_r)` top components — is each one, as a
   REDUCED subscheme, isomorphic as a `k`-variety (not just same ncard / same dimension) to a shifted
   Kostant orbit closure `Ō_M` over `d-r`? If yes, the ring iso is `vanishingIdeal(V1) ≃ vanishingIdeal(V2)`
   under a coordinate iso (an affine-space iso `A^{RepCoord d} ≃ A^{RepCoord d'} × A^δ` carrying one
   variety to the other × A^δ, then `O(V × A^δ) ≃ O(V)[δ vars]` is NOT `orbitRing` — the δ-poly
   extension breaks the iso). Does the smoothness consumer actually need `orbitRing M` exactly, or
   would `orbitRing M` tensored with a polynomial ring / a smooth factor also feed `IsSmoothAt`?
   (The consumer needs a finitely-presented DOMAIN that is `IsSmoothAt` at some prime, and an iso
   `sweepFibreRing⧸I ≃ₐ[k] that domain`. If `orbitRing M [δ poly vars]` is ALSO a smooth fp domain,
   could the target be relaxed to that — avoiding the need to kill the δ factor?)

3. Given the SET equality `quotTopDimSet_sigma_eq_topComponents` + the unconditional labeling
   `exists_kostantPartition_partitionIdeal_eq_of`, what is the MINIMUM additional labeled transport
   needed, rung by rung, to get from a fibre top-component `I` to a sigma top-component? Which rungs
   genuinely need a new `AlgEquiv` of quotient rings (not just `comap` of primes)?

4. Estimate the line-count tier for the cleanest route and name the single hardest rung.

5. Is there a trap where the iso `sweepFibreRing⧸I ≃ orbitRing M` is simply FALSE (the dimensions
   differ by δ, so they CANNOT be isomorphic as rings!) — meaning the consumer's stated target is
   wrong and should instead be `≃ orbitRing M [δ poly vars]` or `IsSmoothAt` proved by a different
   bridge? Flag this hard: `dim(sweepFibreRing⧸I) = dim(fibre top comp)` vs `dim(orbitRing M) =
   dim(Ō_M over d-r)` — are these EQUAL or off by δ? If off by δ, the consumer interface is mis-stated.

Be concrete and skeptical. The δ-dimension-matching (ask 5) is the thing I most want adjudicated.
