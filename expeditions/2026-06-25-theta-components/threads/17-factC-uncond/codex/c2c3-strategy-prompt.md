<task>
Lean 4 + Mathlib v4.29 formalisation. Goal: make "the reduced DLN fibre variety is smooth at the
generic point of each top-dimensional component" UNCONDITIONAL.

## What is BANKED (this tide)
- A general CA lemma `localizationAtPrimeQuotientAlgEquiv` (C1): for a REDUCED Noetherian k-algebra R
  with a prime q meeting exactly ONE minimal prime I (I ≤ q, and no other minimal prime ≤ q),
    `Localization.AtPrime R q ≃ₐ[k] Localization.AtPrime (R⧸I) (q.map (mk I))`.
- The smoothness bridge `isSmoothAt_of_isSmoothAt_quotient_unique_minimalPrime` (C1'): same hypotheses
  ⟹ `IsSmoothAt k (q.map mk) (R⧸I)` implies `IsSmoothAt k q R`. (via FormallySmooth.iff_of_equiv.)

## Existing harness facts
- `OrbitSmooth.isSmoothAt_normalFormIdeal`: over [Field k][IsAlgClosed k], the orbit-closure
  coordinate ring `orbitRing M = MvPoly(RepCoord d)⧸vanishingIdeal(orbitSet M)` (a DOMAIN, M a tuple
  over `d : Fin (N+1)→ℕ`) is `IsSmoothAt k (normalFormIdeal M)` at the orbit normal-form point.
- `sweepFibreRing k d r = MvPoly(RepCoord d)⧸vanishingIdeal(sweepFibre)` where
  `sweepFibre = canonicalCoord '' fibre(normalForm E_r)`, `d : Fin (N+2)→ℕ`. This ring is REDUCIBLE
  (θ≥2 ⟹ several minimal primes = top components).
- `FibreBundleReduced.reducedFibre_chartDsig_tensorEquiv_reducedVariety`:
    `Away (chartDsig d r) ≃ₐ[k] SchurLoc(d0)(dlast)(r) ⊗_k sweepFibreRing d r`.  [Infinite k]
- Thread-16 conditional headline `smooth_schurLoc_tensor_away_of_isSmoothAt_sweepFibre`: GIVEN
  `IsSmoothAt k q (sweepFibreRing)` at a top-component prime q, produces `g ∉ q` with
  `Smooth k (SchurLoc ⊗_k Localization.Away g)`.
- The bundle-base homogeneity (B4) shows every rank-r target B's fibre is a base-change image of the
  MODEL fibre `mult⁻¹(E_r)`; and the COUNT side already proves θ = #top components via a chain of
  TopDimMinPrimes ncard-equalities through the chart (NOT via an explicit geometric
  "fibre top component = orbit closure" identity).

## The two genuinely-open geometric facts (C2)
(a) Each top-dimensional minimal prime I_M of `sweepFibreRing` equals (after the chart/Schur strip
    and base change) some orbit-rank-locus ideal that `OrbitSmooth` covers — so the COMPONENT ring
    `sweepFibreRing⧸I_M` is `IsSmoothAt` at the orbit normal-form point's generic prime q'.
(b) That generic prime q' meets exactly ONE minimal prime (sits OFF the other top components), so C1'
    applies.

## The transport (C3)
Transport the conditional `Smooth k (SchurLoc ⊗ Away g)` to `IsSmoothAt k p (Away chartDsig)` across
the banked tensor equiv, via `SchurLoc ⊗ Away g ≃ Away(1⊗g)` in `SchurLoc ⊗ sweepFibreRing`
(localization-of-base-change, `IsLocalization.tensorProduct_tensorProduct`), then the basic-open bridge.
</task>

<output_contract>
1. RANK the realistic options for THIS tide (line-count estimates), given C1 is banked:
   (A) attempt full C2 (a)+(b) now; (B) bank C3 transport + leave C2 as one named conditional;
   (C) something else. Which maximizes honest unconditional progress?
2. For C2: is the geometric identification (a) reachable from the EXISTING harness facts (the count
   chain, B4 homogeneity, OrbitSmooth) WITHOUT building a fresh "fibre component = orbit closure"
   multi-module theory? Or is it a genuine multi-module wall? Be concrete about the missing lemma(s).
3. For (b) "generic prime sits off other components": for a top-dim minimal prime of a reduced ring,
   is the generic prime q = I_M itself (the minimal prime as its own generic point)? If q = I_M, does
   "I_M meets exactly one minimal prime" hold trivially (a minimal prime contains no other minimal
   prime)? If so (b) is FREE and C1' applies with q := I_M. Confirm or refute.
4. For C3: sketch the cleanest Mathlib route, list real v4.29 lemma names if you can, line estimate.
   Is `isSmoothAt` preserved across the `Away g` basic-open + the AlgEquiv?
5. The single sharpest discriminating check I should run before investing.
</output_contract>

<grounding_rules>
Flag clearly which claims are INFERENCE vs facts you are confident exist in Mathlib v4.29. Do not
invent lemma names — if unsure, say "verify existence of a lemma doing X".
</grounding_rules>
