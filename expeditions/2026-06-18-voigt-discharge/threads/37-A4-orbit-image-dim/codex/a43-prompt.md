<task>
Lean 4 + Mathlib v4.29. I need the cleanest PROOF ROUTE (or an honest "scope it, here is the minimal
residual") for ONE equality — the char-free differential-rank identity A4.3:

  genericDifferentialRank k B (genericOrbitCoord M) = finrank k (LinearMap.range (deformationδ M M))

where (all LANDED, compiling):
- B := groupRing d := Localization.Away (groupDenom d) of MvPolynomial (GroupCoord d) k, a domain.
  K := FractionRing B.
- genericDifferentialRank k B f := Module.finrank K (Submodule.span K (Set.range fun i ↦
    KaehlerDifferential.D k K (algebraMap B K (f i))))   -- f : RepCoord d → B, RepCoord d finite.
- genericOrbitCoord M : RepCoord d → B, x ↦ (r,c)-entry of  Pgen_{i+1} · M_i · Pgen_i⁻¹  in B,
  where Pgen_v = genericUnit d v (generic invertible matrix, entries = the X variables), Pgen_v⁻¹ =
  genericUnitInv d v (= det⁻¹ • adjugate, lives in the localization B). M_i = genericFactor (constant).
  RepCoord d = Σ (i : Fin N), Fin (d i.succ) × Fin (d i.castSucc).
- deformationδ M M : C⁰ →ₗ[k] C¹  is the EXPLICIT k-linear coboundary  φ ↦ (φ_{i+1} M_i − M_i φ_i)_i,
  C⁰ = ∏_v Matrix (Fin d_v) (Fin d_v) k,  C¹ = ∏_i Matrix (Fin d_{i+1}) (Fin d_i) k.
  finrank k (LinearMap.range (deformationδ M M)) is the target RHS (a concrete linear-map rank).

THE PEN-AND-PAPER CERTIFICATE (verified symbolically over generic M, thread 36 §2):
The orbit map μ_M : G → Rep, P ↦ P•M = (P_{i+1} M_i P_i⁻¹)_i. Its differential at the identity e equals
deformationδ M M exactly: d/dt[(I+tφ_{i+1}) M_i (I+tφ_i)⁻¹]|_0 = φ_{i+1} M_i − M_i φ_i. Homogeneity
(μ_M(QP) = Q•μ_M(P), Q•(−) a linear iso of Rep) ⟹ rank dμ_M|_P is constant in P ⟹ the GENERIC rank
(= my genericDifferentialRank, the K-rank of the span of the coordinate differentials) equals rank at e
= rank(deformationδ M M) = finrank(range δ⁰). Char-free.

THE GAP. My genericDifferentialRank is a KAEHLER-DIFFERENTIAL span rank over the fraction field K, NOT a
"Jacobian matrix evaluated at a point". The certificate's argument is geometric (group action, dμ at e,
constant rank). I need to bridge: the K-rank of span{D_K(genericOrbitCoord M x)} equals finrank_k(range δ⁰).

WHAT I HAVE LANDED that may help:
- KaehlerDifferential.mvPolynomialBasis (Ω of poly ring free on {dx}), mvPolynomialBasis_repr_apply
  (Ω-coords = pderiv), KaehlerDifferential.map_D, mapBaseChange, KaehlerDifferential.isLocalizedModule_map
  (Ω of a localization is the localized Ω), tensorKaehlerEquiv.
- The genericUnit/genericUnitInv/genericFactor evaluation API (eval at a group point), deformationδ_apply
  (rfl-simp: deformationδ M M φ i = φ i.succ * M i - M i * φ i.castSucc).
- I PROVED trdeg ≤ genericDifferentialRank (the criterion direction). I do NOT yet have the reverse.

KEY QUESTIONS (be concrete about v4.29 API; flag uncertain lemma names with (verify)):

1. Is the cleanest route to compute genericDifferentialRank via the EXPLICIT pderiv/Jacobian of
   genericOrbitCoord (i.e. the K-matrix (∂(orbit coord_x)/∂(GroupCoord variable)) and its column-rank),
   OR via an abstract group-equivariance argument on the Kähler module Ω[K/k]? Rank the two by Lean cost.
   For the pderiv route: genericOrbitCoord involves det⁻¹ (the adjugate/det of generic matrices) — is the
   pderiv of a localization element (D_K of algebraMap B K (entry of Pgen M Pgen⁻¹)) tractable, given
   Ω[K/k] localizes Ω[MvPoly/k] and D_K(algebraMap b) = map_D image of D_{MvPoly}... but b itself is in
   the localization B, not MvPoly. How do I get a workable formula for D_K(genericOrbitCoord M x)?

2. The homogeneity/constant-rank step: in the Kähler framework, is there a clean way to express
   "rank of span{D(orbit coords)} = rank at the identity" WITHOUT a manifold/tangent-bundle? E.g. the
   group G acts on B by k-algebra automorphisms (left translation), inducing automorphisms of Ω[K/k] that
   carry the coordinate-differential span to itself up to an iso. Does Mathlib have enough Derivation/
   AlgEquiv-on-Ω functoriality (KaehlerDifferential.mapEquiv? or via map of an AlgEquiv) to run this?

3. HONEST SCOPE TRIAGE. If the full A4.3 is a large concrete build, what is the SINGLE cleanest scoped
   lemma to leave as the residual, such that everything else (the criterion direction, the assembly) is
   landed? Options: (a) leave the whole equality genericDifferentialRank = finrank(range δ⁰) scoped;
   (b) split into "genericDifferentialRank = rank of the explicit Jacobian K-matrix" (provable?) + "that
   Jacobian rank = finrank(range δ⁰)" (the dμ_e=δ⁰ + constant-rank content, scoped); (c) prove only the
   inequality genericDifferentialRank ≤ finrank(range δ⁰) (which SUFFICES for the bound, combined with my
   trdeg ≤ genericDifferentialRank — do I even need equality, or does ≤ suffice for varietyDim ≤ finrank δ⁰?).
   Crucially: for the headline bound varietyDim Z_M ≤ finrank(range δ⁰), do I need the EQUALITY hA43 or
   only genericDifferentialRank ≤ finrank(range δ⁰)? (varietyDim = trdeg ≤ genericDifferentialRank, so I'd
   need genericDifferentialRank ≤ finrank(range δ⁰) — the ≤ direction. Confirm.)

4. For the ≤ direction genericDifferentialRank ≤ finrank(range δ⁰): is there a SHORTCUT? The orbit
   coordinates are entries of Pgen M Pgen⁻¹; their differentials D_K(...) — is the span of these
   differentials manifestly contained in (or surjected onto by) a space of dimension finrank(range δ⁰)?
   E.g. a surjective K-linear map (K ⊗ C⁰) → span{D(orbit coords)} factoring through δ⁰? Give the cleanest
   K-linear surjection whose existence bounds the rank by rank(δ⁰).
</task>

<output_contract>
Sections Q1..Q4. For Q3 give a DEFINITE answer on whether the headline needs equality or only ≤. For Q4,
if a clean surjection exists, write its definition (the K-linear map and why its image is the span and its
domain has dim finrank(range δ⁰) after base change). End with VERDICT: "PROVABLE via <route>, ~N lemmas"
or "SCOPE: leave <exact lemma> as residual, prove the rest".
</output_contract>

<grounding_rules>
Flag every lemma/typeclass name you are not sure exists at v4.29 with (verify). Distinguish "Mathlib has
this" from "the math is true but Mathlib may lack it". The verdict (equality-vs-≤, and provable-vs-scope)
is what I am buying.
</grounding_rules>
