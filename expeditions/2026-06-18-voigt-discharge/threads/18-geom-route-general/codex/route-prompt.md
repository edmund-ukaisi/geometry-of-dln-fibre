<task>
Lean 4 + Mathlib (pinned at v4.29.0). I am formalising a piece of algebraic geometry and must decide
between two formalisation routes for the SAME goal. I want an independent assessment of which route is
LESS Lean work and has the SMALLER risk of hitting an absent Mathlib "brick" (a needed lemma/API that
does not exist at this pin and would have to be built as a sub-library).

SETTING (concrete, already formalised):
- Fixed `k : Type*` `[Field k] [IsAlgClosed k]`. A dimension vector `d : Fin (N+1) → ℕ`.
- `Rep := ∏_i Matrix (Fin (d i.succ)) (Fin (d i.castSucc)) k` — tuples of composable matrices (an
  equioriented type-A_N quiver rep). Coordinatised as a polynomial ring `MvPolynomial (RepCoord d) k`.
- A group `G = ∏_v GL_{d_v}(k)` acts on `Rep` by `(P • A)_i = P_{i.succ} A_i P_{i.castSucc}⁻¹`.
- A fixed point `M ∈ Rep` (an arbitrary direct sum of "interval modules" — arbitrary rank pattern).
- `O_M := G · M` is the orbit (a locally closed point set in `k^n`, n = #RepCoord).
- ALREADY PROVED: `O_M` is Zariski-irreducible: `vanishingIdeal(O_M) = ker(μ_M^*)` is PRIME, where
  `μ_M^* : MvPolynomial (RepCoord d) k → 𝒪(G) = Localization.Away Δ` is the orbit-map pullback into the
  DOMAIN `𝒪(G)` (the coordinate ring of G as a principal open of affine space). The orbit map
  `μ_M : G → Rep`, `P ↦ P • M` is a morphism of varieties; its differential at `1 ∈ G` is a known
  k-linear map `δ⁰ : C⁰ → C¹` (a "deformation differential"), with `range δ⁰` the tangent-to-orbit.
- ALREADY PROVED (general M): transitivity — `rankPattern A = rankPattern M ↔ ∃ P : G, P • A = M`
  (the orbit is exactly a level set of the rank pattern).
- A general-purpose AG bridge is ALREADY BUILT and is the SINGLE consumer interface:
  `smooth_point_isRegularLocalRing : [IsAlgClosed k] → (m : Ideal A) [m.IsMaximal] [IsSmoothAt k m]
   → IsRegularLocalRing (Localization.AtPrime m)`, where `A` is the coordinate ring of the variety,
  `m = m_M` the maximal ideal at the point `M`, and `IsSmoothAt k m` UNFOLDS to
  `Algebra.FormallySmooth k (Localization.AtPrime m)` (Mathlib `Algebra.IsSmoothAt`). This bridge +
  `finrank_cotangentSpace_eq_of_isSmoothAt` then give: `varietyDim = finrank(cotangent at m_M)`.

THE TWO GOALS I must discharge for GENERAL M (arbitrary rank pattern, arbitrary d):
- L3: produce the instance `IsSmoothAt k m_M`, i.e. `Algebra.FormallySmooth k (Localization.AtPrime m_M)`.
- L2: identify the Zariski tangent space / cotangent at `m_M` with `range δ⁰` (so the finrank matches
  `dim Ext¹ = n − dim range δ⁰`).

ROUTE A — UNIFORM EXPLICIT CHART. Construct, for general M, a principal open `D(f) ∋ m_M` in the
coordinate ring and an explicit `AlgEquiv` `(𝒪(O_M))_f ≅ Localization.Away f (MvPolynomial (Fin r) k)`,
`r = dim range δ⁰`, parametrising the orbit locally by its `range δ⁰` directions (a structural pivot of
the normal-form matrices; determined entries are Laurent monomials in the free ones, denominator =
product of pivot entries). For the smallest case (a 2x2x2, single orbit) this AlgEquiv was certified by
Gröbner basis (graph ideal = localized closure ideal, single pivot, r=5). `Localization.Away` of a
polynomial ring is `FormallySmooth` ⟹ L3; the chart's coordinates give L2 directly.
QUESTION FOR ROUTE A: for GENERAL M (arbitrary direct sum of interval modules), is the chart a UNIFORM
bounded lemma (a single induction/closed formula over the bar-list, proving the residual generators lie
in the graph ideal by explicit Laurent cofactors), or does it become a genuine SUB-LIBRARY (per-orbit
cell combinatorics, matrix-Schubert-like, with case explosion in the pivot selection)? What is the
hardest general step?

ROUTE B — HOMOGENEITY (uniform, no charts). `O_M` is smooth at every point because it is a homogeneous
space for G:
 (i) generic smoothness — over the perfect field k, the smooth locus of the (reduced, irreducible,
     finite-type) variety `O_M` is dense/nonempty;
 (ii) the smooth locus is G-STABLE (G acts by k-algebra automorphisms of the coordinate ring, preserving
      `IsSmoothAt`/FormallySmooth);
 (iii) G acts TRANSITIVELY on O_M (the transitivity lemma above) ⟹ smoothLocus(O_M) ⊇ O_M ⟹ smooth at M.
 For L2: tangent at M = image of the orbit-map differential at 1 = `range δ⁰` (uniform).
RELEVANT MATHLIB I have found at v4.29:
 - `Algebra.smoothLocus`, `Algebra.IsSmoothAt`, `Algebra.basicOpen_subset_smoothLocus_iff_smooth`,
   `Algebra.isOpen_smoothLocus`, `IsSmoothAt.exists_notMem_smooth` — RING-SIDE, for FinitePresentation.
 - `Scheme.Hom.dense_smoothLocus_of_perfectField` — generic smoothness, but SCHEME-SIDE (needs the orbit
   as an integral `Scheme` X with `f : X ⟶ Spec K`, `LocallyOfFinitePresentation`).
 - `AlgebraicGeometry.smooth_of_grpObj_of_isAlgClosed` — a reduced group SCHEME over alg-closed k is
   smooth (the homogeneity argument, but for the group object itself, scheme-side, via `GrpObj`/
   `Over.mk`/`mulRight`).
QUESTION FOR ROUTE B: at v4.29, are each of (i) generic smoothness applied to the AFFINE variety O_M
(the "Spec detour": Spec of the coordinate ring → scheme → apply dense_smoothLocus → transport the
scheme-side `genericPoint ∈ smoothLocus` back to the ring-side `IsSmoothAt k m`), (ii) building the
G-action as k-algebra automorphisms of the coordinate ring and proving smoothLocus is stable, (iii) the
transitivity-moves-smoothness step, and the L2 differential-image=tangent step — each a BOUNDED amount
of Lean (a few lemmas using existing API), or does any of them require an ABSENT sub-library? What is the
single hardest / highest-absent-brick-risk step?

Note: I do NOT currently model O_M, G, or the orbit as schemes or group objects — everything is
point-set + coordinate ring (MvPolynomial quotient / localization). Modelling cost is part of the
estimate.
</task>

<output_contract>
Respond in these sections, terse:
1. ROUTE A general-chart: BOUNDED vs SUB-LIBRARY, with the hardest step named and WHY (the case-explosion
   risk in pivot selection / residual-ideal membership for arbitrary bar-lists).
2. ROUTE B homogeneity: for EACH of (i) Spec-detour generic smoothness, (ii) G-stability via algebra
   automorphisms, (iii) transitivity step, (iv) L2 differential=tangent — BOUNDED vs ABSENT-BRICK, with
   the single hardest step named. In particular: is the affine Spec detour (ring → Spec scheme → dense
   smoothLocus → back to ring-side IsSmoothAt) a standard short bridge at v4.29, or does transporting
   "scheme genericPoint ∈ smoothLocus" to "ring-side IsSmoothAt k m at a CLOSED point m" need an absent
   lemma? Does the closed point m even contain the generic point's smoothness (specialization /
   openness of the smooth locus closes this — is that wired up ring-side)?
3. RECOMMENDATION: which route is less Lean work / fewer absent bricks for GENERAL M, and the decisive
   reason. Note any HYBRID (e.g. homogeneity for L3, a local computation only to pin the tangent for L2).
4. The single biggest uncertainty in your assessment (what you would check first).
</output_contract>

<grounding_rules>
- Distinguish what you KNOW is in Mathlib v4.29 from what you INFER should be. Flag inferences.
- If you are unsure a specific lemma exists at this pin, say so rather than asserting it.
- Do not propose code; the diagnosis (bounded vs absent-brick, hardest step) is what I need.
- "Bounded" = a handful of lemmas on existing API. "Sub-library" / "absent brick" = a multi-module
  foundational build Mathlib lacks.
</grounding_rules>
