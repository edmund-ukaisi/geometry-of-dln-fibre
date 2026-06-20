<task>
Setting (equioriented type-A quiver, characteristic 0, k algebraically closed). Fix the dimension
vector d = (d_0,...,d_N) and the representation space Rep_d = ⊕_{i} Hom(k^{d_i}, k^{d_{i+1}}) of
composable matrix tuples A = (A_0,...,A_{N-1}). The group G = ∏_v GL_{d_v} acts by
(P·A)_i = P_{i+1} A_i P_i^{-1}. Fix a tuple M (a representation). Define:

- The orbit O_M = G·M ⊆ Rep_d, locally closed, irreducible (image of irreducible G under the
  polynomial orbit map μ_M : G → Rep_d, P ↦ P·M). We have PROVED: vanishingIdeal(O_M) = ker(μ_M^*),
  prime (μ_M^* : k[Rep_d] → 𝒪(G) into a domain).
- Z_M = orbit closure = Ō_M. By Lehalleur-Rimanyi Thm 3.8 (cited), Z_M as a SET equals the rank
  locus { A : rank(A_{j}...A_{i+1}) ≤ r_{ij}(M) ∀ i≤j } (interval-subproduct ranks).
- The coboundary space: C¹ = Rep_d (ambient tangent), C⁰ = ⊕_v End(k^{d_v}) (Lie algebra of G),
  δ⁰ : C⁰ → C¹, δ⁰(φ)_i = φ_{i+1} M_i − M_i φ_i. range(δ⁰) = the image of the orbit-map differential
  dμ_M at the identity = the "tangent to the orbit" B¹. dim range(δ⁰) = #Rep_d − dim Ext¹(M,M) =:
  r (this finrank equality is PROVED, purely linear algebra).

We are formalising in Lean 4 / Mathlib (v4.29). We have PROVED a general commutative-algebra bridge
(call it L2a), UNCONDITIONAL at a k-rational point:

  For R = k[σ] (σ finite), an ideal I = span(range g) with a FINITE GENERATING FAMILY
  g : Fin m → R, and a k-rational point a ∈ V(I) (eval_a(g_i)=0), with A = R/I and m_A the maximal
  ideal at a:  finrank_k(CotangentSpace(Localization.AtPrime m_A)) = finrank_k(ker(Jacobian g a)),
  where Jacobian g a : (σ→k) → (Fin m → k), v ↦ (∑_x eval_a(∂g_i/∂x) v_x)_i.
  REQUIREMENT: g must generate I = vanishingIdeal(Z_M) as an ideal (the family enters as
  I = span(range g)).

We have ALSO PROVED an L4★/M2 package: IF we can exhibit ONE instance IsSmoothAt k m_M (formal
smoothness of the local ring at the maximal ideal m_M of the point M in the coordinate ring
A = k[Rep_d]/vanishingIdeal(Z_M)), THEN:
  - ringKrullDim(Localization.AtPrime m_M) = n, where n = finrank of Ω[S/k] on a standard-smooth
    chart S = A[1/f] (f ∉ m_M), computed by an ETALE-over-affine-space route (non-circular, does
    NOT use the cotangent/tangent identity);
  - varietyDim(Z_M) = ringKrullDim(AtPrime m_M) = n;
  - finrank(CotangentSpace at m_M) = n  (smooth point ⟹ regular local ring).

Our goal (the final geometry headline) is: varietyDim(Z_M) = r = finrank(range δ⁰).

The remaining gap (call it L2b) is to identify finrank(CotangentSpace at m_M) — equivalently
finrank(ker(Jacobian)) from L2a, or n from L4★ — with r = finrank(range δ⁰).

QUESTIONS (be rigorous; distinguish proved-fact from inference; flag any step that needs a
substantial sub-library Mathlib lacks):

(A) CIRCULARITY. Is the orbit-map/differential route to "ker(Jacobian of the defining ideal at M)
    ⊆ range(δ⁰)" (equivalently the reverse inclusion of the Zariski tangent ⊆ coboundaries)
    circular, GIVEN that the only thing it would feed is dim O_M = r? Concretely: dμ_M surjects
    onto its image range(δ⁰) by definition; the Zariski tangent T_M Z_M ⊇ range(δ⁰) always (orbit
    ⊆ variety); to get T_M Z_M = range(δ⁰) one wants dim T_M Z_M = dim Z_M = dim O_M, but dim O_M
    is exactly what we're trying to compute. Is there ANY non-circular route via smoothness alone
    (e.g. using that O_M is open in Z_M, plus smoothness of Z_M at M, WITHOUT pre-assuming
    dim O_M = r)? Or is the determinantal/Jacobian-of-minors computation the only non-circular
    route to identifying the tangent/cotangent dimension with r?

(B) DETERMINANTAL PREREQUISITE. To use L2a, the generating family g must generate the RADICAL
    vanishing ideal vanishingIdeal(Z_M). Are the rank-locus minors — the (r_{ij}+1)×(r_{ij}+1)
    minors of the interval sub-products A_j...A_{i+1} — a generating family of vanishingIdeal(Z_M),
    i.e. is vanishingIdeal(Z_M) = (those minors) as an ideal (radical/prime)? Is this a bounded,
    self-contained fact, or does it require the Lakshmibai-Magyar / Knutson-Miller-Shimozono
    "quiver determinantal ideal is prime and minor-generated" theory? State precisely what is
    needed and whether Mathlib v4.29 has any of it.

(C) JACOBIAN KERNEL. GIVEN the minors as generators, is ker(their Jacobian at M) = range(δ⁰)
    (equivalently the minors' differentials at M span exactly the annihilator of range(δ⁰)) a
    UNIFORM linear-algebra computation that works for every orbit type by one argument, or is it
    per-orbit-type combinatorics depending on the bar/lace structure of M? Sketch the uniform
    argument if one exists.

(D) Is there a CLEANER route to varietyDim(Z_M) = r that sidesteps the tangent/cotangent subspace
    identification entirely — e.g. computing dim O_M = dim G − dim Stab(M) = dim G − dim End(M)
    directly (orbit-stabiliser), and dim Z_M = dim O_M (closure preserves dimension), so that one
    never differentiates the minors at all? What would such a route need that Mathlib lacks
    (affine algebraic group orbit-dimension theory: dim of orbit = dim G − dim stabiliser; that an
    orbit is open in its closure; dim closure = dim orbit)?

(E) Does L2b only need the FINRANK equality finrank(ker Jacobian) = finrank(range δ⁰), or the
    actual SUBSPACE identity ker(Jacobian) = range(δ⁰)? Given L4★ delivers
    varietyDim = finrank(cotangent) = finrank(ker Jacobian) already, the subspace identity seems
    unnecessary — confirm or correct.
</task>

<output_contract>
Answer (A)-(E) in order, each a short tight paragraph. For (B) and (D) explicitly state: BOUNDED
(self-contained, Mathlib has the pieces) vs SUB-LIBRARY (needs a substantial absent theory), and
name the absent theory precisely. End with a one-line verdict: which of the candidate routes
(determinantal-Jacobian / orbit-stabiliser-dimension / smoothness-only) is the smallest
non-circular path to varietyDim(Z_M) = finrank(range δ⁰), and whether ANY of them is bounded or all
pull a sub-library.
</output_contract>

<grounding_rules>
Mark each claim as FACT (standard theorem you can name) or INFERENCE. Do not assert Mathlib has a
lemma unless you are confident of the area; if unsure say "likely absent, needs checking". Keep the
representation-theory facts (orbit-stabiliser, End(M), Ext¹, hereditary Euler form) precise. The
field is algebraically closed, characteristic 0. Equioriented type A only.
</grounding_rules>
