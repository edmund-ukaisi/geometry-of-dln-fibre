<task>
I am sizing ONE Lean 4 + Mathlib (pinned v4.29) formalisation obligation for a quiver-orbit
codimension theorem, to decide: is it a 1-2 module BUILD, or a genuine multi-module sub-expedition?

SETTING (all objects already proved/landed in Lean, sorry-free):
- k a field, [IsAlgClosed k]. Equioriented type-A_N quiver. A "tuple" M = (M_i)_i is matrices
  M_i : Mat(d_{i+1} x d_i)(k), i=0..N-1 (a representation).
- Group G = ∏_v GL_{d_v}(k) acts: (P • M)_i = P_{i+1} M_i P_i^{-1}. Orbit O_M = G•M (a point set
  in the affine space Rep_d = ∏_i Mat(d_{i+1} x d_i), dimension Σ_i d_{i+1} d_i).
- Z_M := closure(O_M) = the rank locus {A | rankPattern A ≤ rankPattern M} (determinantal variety,
  CITED Thm 3.8). vanishingIdeal Z_M is PRIME (LANDED: O_M is image of irreducible G under a
  polynomial orbit map μ_M, so van(O_M) = ker(μ_M^*) into a domain 𝒪(G)=Localization.Away(∏ det)).
- C⁰ := ∏_v Mat(d_v x d_v)(k) (= Lie G when matched). C¹ := ∏_i Mat(d_{i+1} x d_i)(k) (= Rep_d
  tangent). δ⁰ : C⁰ → C¹ the k-linear map φ ↦ (φ_{i+1} M_i − M_i φ_i)_i. This δ⁰ IS the orbit-map
  differential dμ_M at the identity.
- LANDED (free): ker δ⁰ = End(M)=Hom(M,M); rank-nullity finrank(range δ⁰)+finrank(ker δ⁰)=finrank C⁰;
  orbitLinearCodim M := finrank C¹ − finrank(range δ⁰) = finrank Ext¹(M,M) (= the paper's codim).
- LANDED dimension stack (the "Jacobian ladder"): for the smooth k-point M of Z_M,
  varietyDim Z_M = ringKrullDim(R/van Z_M) = ringKrullDim(Localization.AtPrime m_M)
                 = finrank_k(cotangent at m_M) = finrank_k(ker Jac(minors) at M).
  This is all PROVED via L0(Nullstellensatz height+dim=card), L4d(Noether-normalization
  equidimensionality), M3(smooth⟹regular⟹cotangent=dim), L2a(cotangent=ker Jacobian) — MODULO an
  IsSmoothAt-at-m_M hypothesis (call it L3, a separate ladder, assume delivered).

THE TARGET EQUALITY (this is the whole obligation, call it hVoigt-half):
    finrank(range δ⁰) = varietyDim Z_M.
- EASY direction (≤): range δ⁰ ⊆ ker Jac (orbit tangent ⊆ Zariski tangent, since O_M ⊆ Z_M), giving
  finrank(range δ⁰) ≤ finrank(ker Jac) = varietyDim Z_M. (cheap)
- HARD direction (≥): finrank(range δ⁰) ≥ varietyDim Z_M = dim O_M. THE ORBIT-MAP SUBMERSION.

MATHLIB FACTS I HAVE VERIFIED BY GREP (v4.29):
- NO fibre-dimension theorem (dim O = dim G − dim Stab); NO scheme quotient G/H.
- NO ringKrullDim = transcendence-degree (Algebra.trdeg exists only as a Cardinal, no bridge to
  ringKrullDim).
- NO "dimension of image of a dominant morphism" theorem.
- Smooth/Fiber.lean only has smooth-fibers⟹smooth (wrong direction). smoothLocus is open + dense
  over perfect field (KNOWN). FormallySmooth.of_equiv KNOWN.
- A scheme-group precedent AlgebraicGeometry.Group.Smooth.smooth_of_grpObj_of_isAlgClosed exists but
  is group-object-specific (uses GrpObj.mulRight), not reusable for an external action.
- Stab(M) = Aut(M) = (End M)ˣ = the principal open D(∏ det) ⊂ the LINEAR space Hom(M,M)=ker δ⁰.
  So "dim Stab = finrank Hom(M,M)" is morally cheap. Likewise G = ∏ GL = D(∏ det) ⊂ C⁰, so
  "dim G = finrank C⁰ = Σ d_v²" is morally cheap. The gap is ONLY the fibre-dimension bridge tying
  these to dim O_M.

THE NUMERICS CHECK OUT (I verified on (2,2,2), both the (1,1)-orbit and the zero-product locus):
finrank(range δ⁰) = dim G − finrank End(M) = dim O_M = varietyDim Z_M exactly. The math is correct;
the question is purely the cheapest LEAN PATH and an HONEST module count.
</task>

<questions>
1. Is there a route to the HARD direction finrank(range δ⁰) ≥ varietyDim Z_M that AVOIDS a general
   fibre-dimension theorem, by exploiting that BOTH G and Stab(M) are principal opens of LINEAR
   spaces (D(det) ⊂ C⁰ and D(det) ⊂ ker δ⁰)? Specifically: does the orbit map μ_M : G → Z_M, being
   a map from a principal-open-of-affine-space to an affine variety, admit a cheap dimension bound
   dim(image) ≥ rank(differential at a point) WITHOUT building general fibre-dimension theory? Or is
   "dim of constructible image ≥ rank of generic differential" itself the multi-module theorem?

2. CANDIDATE SHORTCUT — Noether normalization on the pullback subalgebra. The engine ALREADY proves
   dim Z_M via Noether-normalizing R/van(Z_M). Since van(Z_M)=ker(μ_M^*), we have
   R/van(Z_M) ≅ image(μ_M^*) ⊆ 𝒪(G). So varietyDim Z_M = ringKrullDim(image μ_M^*). Can I get
   ringKrullDim(image μ_M^*) ≤ finrank(range δ⁰) directly — e.g. by bounding the transcendence degree
   of Frac(image μ_M^*) by the rank of the differential — using only the LANDED Noether-normalization
   dim API (ringKrullDim_eq_of_integral_injective, ringKrullDim_mvPolynomial_fin_field) plus
   linear-algebra rank facts? Is this a real shortcut or does it secretly need the same submersion
   theorem (relating trdeg of the image to the rank of the Jacobian of μ_M^*)?

3. If a fibre-dimension/submersion bridge is genuinely unavoidable, what is the MINIMAL theorem to
   port for THIS explicit linear action — stated precisely — and honestly how many Lean modules
   (count + the single hardest sub-lemma)? Distinguish: (a) a minimal "dim image of orbit map =
   dim G − dim generic fibre" specialised to μ_M; (b) building the local structure of μ_M as a
   smooth surjection onto O_M with fibres = Stab-cosets; (c) anything else.

4. Where EXACTLY does char-0 / separability enter? My prior is it enters ONLY at the HARD direction
   (the Frobenius example 𝔾ₐ ↷ 𝔸¹, t•x=x+t^p has dμ=0 ≠ dim O). Confirm or refute that the EASY
   direction and the whole landed Jacobian stack stay char-free, so [CharZero k] is a single
   localized hypothesis on the hVoigt-discharging theorem.

5. BOTTOM LINE: BUILD (1-2 modules, give the lemma statements) or SUB-EXPEDITION (give module count +
   the cleanest theorem to port + effort)? Be concrete and Bayesian — the explicit linear structure
   (Stab = units of a matrix algebra = principal open of a linear space) is the lever; say whether it
   actually collapses the count or is a red herring.
</questions>

<output_contract>
Answer each of 1-5 in order, with headers. For each, mark every Mathlib claim as KNOWN (exists at
v4.29) / INFER (standard but you're not certain it's in Mathlib) / MISSING. Keep it tight: lemma
statements where you assert a route, module counts where you assert a size. End with a one-line
verdict: BUILD-<n>-modules or SUB-EXPEDITION-<n>-modules.
</output_contract>

<grounding_rules>
Do not assume a Mathlib lemma exists unless you are confident at the v4.29 pin; if unsure, say INFER
and name the closest thing you know. The numerics and the algebra are already verified — do not
re-derive them; focus on the LEAN PATH and the honest size. If you think route 2 (Noether on the
pullback subalgebra) hides the submersion theorem, say so explicitly and explain where.
</grounding_rules>
