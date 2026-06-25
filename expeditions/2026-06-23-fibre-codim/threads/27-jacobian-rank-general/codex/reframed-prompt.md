<task>
Same setting as before (deep linear network / type-A quiver, char-0 alg-closed field; N≥1;
d=(d_0,...,d_N); mult(A)=A_{N-1}...A_0; E=diag(I_r,0) rank r; r≤min_i d_i; F=mult^{-1}(E);
card=Σ d_{i+1}d_i; C=cCodim(d,r)=codim Σ̄^r; δ=r(d_N+d_0−r)).

We have now SETTLED the geometry by exact computation (Singular primary decomposition + exact
sympy Jacobian ranks), and want you to red-team the GENERAL ARGUMENT and the ROUTE CHOICE for
the formaliser. Key verified facts:

(F1) For (3,3,3) r=1: C=3, δ=5, C+δ=8, card=18. The fibre F has dim 10 (codim 8 = C+δ),
     and 3 irreducible components of dims 10, 9, 9. The ideal (mult−E) is radical (checked on
     (2,2,2) r=1; component dims for (3,3,3) confirm reduced top component).
     - TOP component (dim 10): the "middle-rank" locus where BOTH endpoint factors are rank 2
       (= generic rank subject to product=E), product drops to rank 1 in the middle. At a generic
       point: rank(d mult_A)=8=C+δ exactly, dim=card−8=10. SMOOTH there.
     - The two dim-9 components: A0 invertible (A1=E A0^{-1}, rank 1) and A1 invertible. At their
       generic points rank(d mult_A)=9 > C+δ.
(F2) For (2,2,2) r=1: 2 components both dim 4 (codim 4 = C+δ), both TOP; generic rank=4 each.
(F3) The factor-rank strata are NOT the components. At a profile-[1,1] point (both 3×3 factors
     rank 1) of (3,3,3) r=1, rank(d mult)=5 < C+δ=8; that point is a SINGULAR point lying in the
     CLOSURE of the dim-10 top component (it is not a separate component; card−rank=13 there is the
     singular tangent dim, NOT a local dimension). So "rank ≥ C+δ uniformly over ALL of F" is FALSE;
     the bound holds only at GENERIC (smooth) points of each component.
(F4) image(d mult_A) ⊇ T_E Mat^{≤r} (dim δ) at EVERY A∈F, via the endpoint GL×GL orbit-tangent
     (mult((P,Q)·A)=P·mult(A)·Q^{-1}, velocity = {XE+EY} = T_E Mat^{≤r}). So rank ≥ δ everywhere.
     Verified the EXACT formula "rank(d mult_A)=δ+codim Ō_M(A)" is FALSE at non-generic orbit pts.

THE PROPOSED GENERAL ARGUMENT for the hard direction codim F ≥ C+δ (route B, Jacobian + generic
smoothness):
  Step 1 (generic smoothness, char 0): each irreducible component F_α of (F)_red is generically
    smooth; at a generic smooth point A∈F_α, dim F_α = dim T_A F = card − rank(d mult_A), PROVIDED
    the scheme F is generically reduced along F_α (so the scheme tangent = reduced tangent).
  Step 2 (the per-component bound): at a generic point of EVERY component F_α, rank(d mult_A) ≥ C+δ.
  Step 3: hence dim F_α ≤ card − C − δ for every α, so dim F ≤ card−C−δ, i.e. codim F ≥ C+δ.

The ALTERNATIVE route (equivariant fibration, you recommended last time):
  Let Z = mult^{-1}(Mat^{=r}) (or Σ̄^r). The connected group G=∏GL_{d_i} acts; the endpoint action
  is transitive on Mat^{=r}. G connected ⟹ preserves each irreducible component Z_j of Z. Each
  Z_j → Mat^{=r} is surjective with isomorphic fibres, so dim(Z_j ∩ F) = dim Z_j − δ. Since
  codim Z_j ≥ C (codim Σ̄^r = C = min over its components), every component of F has dim ≤
  card−C−δ. Done — no Jacobian, no generic reducedness.

QUESTIONS:
Q1. Is Step 2 (rank ≥ C+δ at a generic point of EVERY component) actually a THEOREM with a clean
    proof, or does it secretly need to know what the components ARE (which depends on d,r)? Note: at
    a generic SMOOTH point of F_α, rank(d mult_A) = card − dim F_α automatically (Step 1). So Step 2
    "rank ≥ C+δ on every component" ⟺ "dim F_α ≤ card−C−δ for every α" ⟺ Step 3's conclusion. So
    Steps 1–3 are CIRCULAR unless rank ≥ C+δ is proven WITHOUT first knowing dim F_α. Is there an
    INDEPENDENT proof of rank(d mult_A) ≥ C+δ at a generic component point that does NOT go through
    the dimension? (e.g. exhibiting C+δ independent rows/cols of the Jacobian structurally.) If not,
    route B does not actually prove anything beyond what the fibration already gives. Be blunt.
Q2. The equivariant-fibration route: verify each step is sound and identify which parts are
    LANDED-engine-friendly vs need new AG. In particular: (i) "G connected ⟹ preserves each
    irreducible component" — is this a clean standard fact (connected group acting on a variety
    permutes components, fixes them since connected)? (ii) "Z_j → Mat^{=r} surjective with isomorphic
    fibres ⟹ dim(Z_j∩F)=dim Z_j − δ" — this is the orbit-homogeneity / equidimensional-fibres
    statement; over Mat^{=r} which is a SINGLE G_end-orbit (homogeneous), all fibres are literally
    isomorphic (translates), so this is honest. (iii) codim Z_j ≥ C: needs codim Σ̄^r = C = min over
    components AND that the EXACT-rank Σ^r=mult^{-1}(Mat^{=r}) has the same components/codim as its
    closure Σ̄^r. Confirm Σ̄^r = closure(Σ^r) and codim Σ^r = codim Σ̄^r (LR Cor 4.4 / Lemma 4.5).
Q3. CRUCIAL for the formaliser: the engine works with codimRepCanonical = height(vanishingIdeal) and
    varietyDim, NOT with scheme/Spec machinery. The fibration route needs "dim(Z_j∩F)=dim Z_j − δ"
    which is a fibre-dimension theorem for the morphism mult|_{Z_j} : Z_j → Mat^{=r}. Mathlib v4.29
    LACKS a general fibre-dimension theorem (this is the recurring wall). BUT Mat^{=r} is a single
    homogeneous space (G_end-orbit), so ALL fibres are G_end-TRANSLATES of F (literally isomorphic
    varieties), not just equidimensional. Does THIS (translate-isomorphism, an explicit GL action,
    which the engine HAS as baseChange) let us prove dim(Z_j ∩ F) = dim Z_j − δ WITHOUT a general
    fibre-dim theorem — e.g. dim Z_j = dim(G_end-orbit of any fibre) = δ + dim(fibre), via the
    orbit-dimension machinery the engine already has (OrbitImageDim / dim O = dim G − dim Stab)?
    Sketch how the fibration dim-additivity becomes an ORBIT-dimension computation on the engine's
    landed machinery. Is THAT the cleanest formaliser route?
Q4. Bottom line: for the hard direction codim F ≥ C+δ, which is the smallest, most-landed-engine-
    reusing route — (a) Jacobian + generic smoothness, (b) equivariant fibration via a general
    fibre-dim theorem, or (c) equivariant fibration recast as an ORBIT-dimension count
    (dim Σ̄^r = δ + dim F via the G_end action sweeping F across Mat^{=r})? Rank them on formaliser
    surface + risk. If (c), state the precise dim-additivity identity to hand the formaliser.
Q5. The MOST LIKELY ERROR in the above, and the cheapest test.
</task>

<output_contract>
  ≤ ~1000 words. Sections: 1. Is Step 2 circular? (Q1, blunt YES/NO + why). 2. Fibration route
  soundness (Q2, per-step). 3. The orbit-dimension recast (Q3 — does the homogeneous base let us
  dodge the general fibre-dim theorem? sketch the identity). 4. ROUTE RANKING (Q4). 5. Likely error
  + cheapest test (Q5).
</output_contract>

<grounding_rules>
  - The numbers in (F1)-(F4) are EXACT (Singular + exact sympy), treat as ground truth.
  - Distinguish THEOREM (provable/sketchable) from CONJECTURE. Be blunt about circularity.
  - Engine objects: codimRepCanonical=height(vanishingIdeal); varietyDim; Σ̄^r=productRankLocusLE;
    cCodim; the GL_d baseChange action with mult-equivariance mult(P•A)=P_N·mult(A)·P_0^{-1};
    OrbitImageDim/orbit-dimension machinery (dim orbit via Jacobian/trdeg); deformationδ.
  - char 0, alg-closed; N≥1; r≤min_i d_i.
</grounding_rules>
