<task>
Lean 4 + Mathlib (pin v4.29). Setting: representations of the equioriented type-A_N quiver as
tuples of matrices `M = (M_i)`, with the base-change group `G_d = ∏_v GL_{d_v}` acting by
`(P • A)_i = P_{i+1} · A_i · P_i^{-1}`. Fix a tuple `M`; let `O_M = G_d · M` be its orbit, viewed
as a locally-closed subset of the affine coordinate space `Rep_d = ∏_i Mat_{d_{i+1} × d_i}`.

We have, ALREADY PROVED in Lean (do not re-derive):
  - `vanishingIdeal(O_M) = ker(μ_M^*)` is PRIME, where `μ_M^* : k[Rep_d] → 𝒪(G_d)` is the orbit-map
    pullback and `𝒪(G_d) = Localization.Away (∏_v det) (poly ring)` is an integral domain.
  - The orbit-map differential `dμ_M` at `1 ∈ G_d` has image = `range δ⁰`, where
    `δ⁰(φ)_i = φ_{i+1} M_i − M_i φ_i` is the deformation/coboundary map (tangent-to-orbit = `B¹`).
  - `r := finrank_k(range δ⁰)` is the expected orbit dimension; for our running example `d=(2,2,2)`,
    `r = 5`, codim 3.

We need a Lean-provable route to the AG bridge L4★, which needs exactly ONE instance:
  `IsSmoothAt k (m_M)` (the maximal ideal of `M` in `k[Rep_d]/vanishingIdeal(O_M)` is a smooth point),
  plus `κ(m_M)=k` and the local Krull dimension `= r`. Then Mathlib's
  `smooth_point_isRegularLocalRing` + `finrank_cotangentSpace_eq_of_isSmoothAt` close it.

TWO CANDIDATE ROUTES for establishing smoothness of `O_M` at `M`:
(A) EXPLICIT CHART: exhibit a principal-open neighbourhood of `M` in `O_M` isomorphic (as `k`-algebra)
    to `Localization.Away f (MvPolynomial (Fin r) k)`, by solving the local defining equations
    (determinantal + product-vanishing) for the non-free entries as a graph over r free coordinates,
    on the locus where a pivot minor `f` is a unit. Smoothness then immediate from
    `Algebra.FormallySmooth.mvPolynomial` + localization.
(B) SMOOTH-DESCENT: `μ_M : G_d → O_M` is a surjective `Stab(M)`-torsor; `G_d` is smooth/k (a det-
    localization of a polynomial ring). If `μ_M` is faithfully flat (fppf) and smoothness descends
    along fppf surjections, then `O_M` smooth/k.

QUESTIONS:
1. For route (B): does Mathlib (v4.29, current) actually PROVIDE fppf descent of formal/algebraic
   smoothness (descent of `Algebra.FormallySmooth` / `Algebra.Smooth` along a faithfully flat ring
   map)? Name the declaration(s) if so. Does it provide tools to prove an orbit map `μ_M` faithfully
   flat / to construct the `Stab(M)`-torsor structure as a flat morphism? Or is this genuinely-absent
   Mathlib (would need a sizeable build)?
2. For route (A): what Mathlib API supports gluing the local-chart `AlgEquiv` to `IsSmoothAt`? List
   the load-bearing lemmas (localization-away formal smoothness, transfer of `IsSmoothAt` across an
   `AlgEquiv` of localizations, the `Localization.atPrime` ↔ `Localization.Away` comparison).
3. Which route is CLEANER vs HEAVIER for a single instance at a known point with a known r? Give a
   sharp recommendation.
4. For L2 (cotangent = `range δ⁰`): the differential `dμ_M` at `1` has image `range δ⁰`; we want the
   Zariski cotangent space `m_M/m_M²` (over k, since `κ(m_M)=k`) identified as the DUAL of `range δ⁰`.
   What is the exact Mathlib statement chain (CotangentSpace, dual_finrank_eq) the formaliser must
   prove, and does an explicit chart make this near-automatic vs a determinantal-Jacobian route?
</task>

<output_contract>
Sections: (1) fppf-descent availability verdict + named decls or "absent"; (2) chart-to-IsSmoothAt
API list; (3) sharp route recommendation (A or B) with one-paragraph why; (4) L2 cotangent chain.
Be concrete about Mathlib declaration names at the v4.29 pin; mark any you are UNSURE exists as
"unverified — check". Keep under ~500 words.
</output_contract>

<grounding_rules>
Distinguish Mathlib decls you are confident exist (v4.29) from ones you infer should exist. Do not
claim a descent-of-smoothness lemma exists unless you can name it; if unsure, say "absent / unverified"
— that is itself the load-bearing answer. Do not invent API.
</grounding_rules>
