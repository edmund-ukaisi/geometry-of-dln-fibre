<task>
I am formalising in Lean 4 / Mathlib (v4.29). Setting: a field k, algebraically closed.
GOAL: prove the reduced fibre variety of a multiplication map is SMOOTH at the generic /
normal-form point of each top-dimensional irreducible component — i.e. `Algebra.IsSmoothAt k p`
(= `FormallySmooth k (Localization.AtPrime p)`) at a prime p corresponding to that generic point.
The fibre is REDUCIBLE (θ ≥ 2 components meeting), so global `Smooth k (FibreRing)` is FALSE;
only the per-component-generic-point `IsSmoothAt` is true.

BANKED Lean facts I can build on:
1. A per-chart product trivialization of the REDUCED variety:
   `Away chartDsig ≃ₐ[k] SchurLoc ⊗[k] sweepFibreRing`   (k-algebra iso; needs [Infinite k]).
   - `SchurLoc = Localization.Away (detSchurS …)` — a localization of a polynomial ring over k,
     hence `Smooth k SchurLoc` (via `Algebra.Smooth.of_isLocalization_Away` + polynomial smoothness).
   - `sweepFibreRing = MvPolynomial (RepCoord d) k ⧸ vanishingIdeal(fibre)` — the reduced fibre
     coordinate ring (the REDUCIBLE thing).
   - `Away chartDsig` = coordinate ring of the source pivot chart {detΔ≠0} of the rank-r locus Σ^r.
2. `OrbitSmooth`: for an orbit-closure ring `orbitRing M = MvPolynomial (RepCoord d') k ⧸
   vanishingIdeal(orbitSet M)` over IsAlgClosed k, it proves
   `isSmoothAt_normalFormIdeal : Algebra.IsSmoothAt k (normalFormIdeal M)`
   at the normal-form point ideal m_M. Route: G_d dense orbit + generic smoothness over perfect k +
   G_d-transport. This is POINTWISE IsSmoothAt, not global Smooth.
3. Top components of Σ̄^r are exactly the inclusion-maximal orbit closures Ō_M of minimal codim;
   the fibre's top components correspond (after a base change / "shift") to shifted-side Σ̄ orbit
   closures.

Mathlib smoothness API available (real, verified line numbers in Smooth/Basic.lean):
- `FormallySmooth.comp [FormallySmooth R A][FormallySmooth A B] : FormallySmooth R B`
- `Algebra.Smooth.baseChange [Smooth R A] : Smooth B (B ⊗[R] A)`
- `FormallySmooth.of_equiv (e : A ≃ₐ[R] B) : FormallySmooth R A → FormallySmooth R B`; also `iff_of_equiv`
- `Smooth.of_isLocalization_Away (r:R)[IsLocalization.Away r A]: Smooth R A`
- `FormallySmooth.localization_map`, `of_isLocalization`, `FormallySmooth (Localization M)`
- `Algebra.IsSmoothAt R p := FormallySmooth R (Localization.AtPrime p)`
- `Algebra.FormallySmooth.iff_of_equiv` transfers FormallySmooth across a k-algebra equiv.

The FALLBACK route (banked `FibreSmoothPlumbing`): `SubmersivePresentation` with one chosen square
(C+δ)-minor a unit in the chart ⟹ `Smooth k (ChartAlg v)`; wrappers transport across an iso to a
localization. Needs `IsUnit (e (subJacobian v a ha))` discharged by a determinantal rank≥C+δ lower
bound at the generic point. Mathlib determinantal-rank support is thin.

Numerically/combinatorially VERIFIED (pen-and-paper threads, 15600 dimension vectors + Singular certs):
generic Jacobian rank = codim = C+δ on every top component (fact (C)), and rank ≤ codim universally
(fact (D)). So the fibre IS generically smooth of expected dim on every top component — the MATH is settled.
</task>

<questions>
1. ROUTE CHOICE. Three routes:
   (LEAD) transport pointwise `IsSmoothAt` across `Away chartDsig ≃ SchurLoc ⊗ sweepFibreRing`,
     getting smoothness of the chart from smoothness of `sweepFibreRing` at the fibre point, which
     in turn comes from `OrbitSmooth` IF I can identify `sweepFibreRing` localized at the top-component
     generic point with the orbit-closure ring localized at m_M.
   (FALLBACK) SubmersivePresentation + discharge the minor-unit by determinantal rank.
   (FLOOR) conditional theorem `…_of_isSmoothAt_fibre` or `…_of_minor_isUnit` carrying the one honest hyp.
   Which is cheapest to LAND HONESTLY in a bounded tide? Rank them.

2. LEAD soundness. Is there a clean Mathlib-level lemma chain for: given a k-algebra iso
   `e : C ≃ₐ[k] A ⊗[k] B` with `Smooth k A` (A a localized polynomial ring), and `IsSmoothAt k q` for
   B at a prime q of B, conclude `IsSmoothAt k p` for C at the prime p = e⁻¹(image of the product
   prime A⊗q-ish)? Concretely: does smoothness of the SchurLoc factor + IsSmoothAt of the
   sweepFibreRing factor at a point give IsSmoothAt of the tensor product `SchurLoc ⊗ sweepFibreRing`
   at the corresponding prime — and is the "corresponding prime" identification clean in Mathlib, or is
   it a swamp (primes of a tensor product are NOT simply products of primes)? Flag whether the
   localization-of-tensor = tensor-of-localizations step is the wall.

3. LEAD crux. `sweepFibreRing` (fibre coordinate ring) vs `orbitRing M` (shifted-side orbit closure):
   is "fibre ≅ shifted orbit closure" plausibly a CLEAN iso, or only an iso AFTER removing the
   end-block / SchurLoc factor (i.e. the iso is exactly what the tensor trivialization encodes, and
   `sweepFibreRing` itself is the shifted orbit-closure UNION, still reducible)? If `sweepFibreRing`
   is the reducible union of shifted orbit closures (not a single Ō_M), then `OrbitSmooth`'s
   `IsSmoothAt (normalFormIdeal M)` is about ONE orbit ring — I'd need that the fibre's localization at
   a top-component generic point equals that single orbit ring's localization at m_M (the other
   components don't pass through the generic point of this one). Is that "components are disjoint at
   each other's generic points ⟹ local ring sees only one component" step a known clean Mathlib move,
   or itself substantial?

4. Given a bounded tide and the determinantal-rank thinness, is the FLOOR (a precisely-named conditional
   carrying `IsSmoothAt k (sweepFibreRing-fibre-point)` OR the minor-unit) the RATIONAL landing, with
   LEAD/FALLBACK scoped as the unconditional follow-on? What EXACTLY would the unconditional proof cost?
</questions>

<output_contract>
Four numbered sections matching the four questions. For Q1 give a strict ranking with one-line why.
For Q2/Q3 be concrete about WHERE the wall is (name the missing Mathlib lemma or the substantial step).
For Q4 give a crisp verdict + the cost line. Flag inference vs. what you can assert from the Mathlib API
I quoted. Be terse; no code dumps.
</output_contract>
