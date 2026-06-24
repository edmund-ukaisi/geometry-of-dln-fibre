<task>
Same setting (deep linear net / type-A quiver; char-0 alg-closed; N≥1; d=(d_0,...,d_N);
mult(A)=A_{N-1}...A_0; E=diag(I_r,0); r≤min d_i; F=mult^{-1}(E); δ=r(d_N+d_0−r);
C=cCodim(d,r)=codim Σ̄^r; card=Σ d_{i+1}d_i).

We have NAILED a clean structural decomposition of the differential's image, verified EXACTLY
(Singular + exact-ℚ sympy) at every fibre-over-E point of (2,2,2)r1, (3,3,3)r{1,2}, (3,2,3)r1,
(2,2,3)r1. We want you to judge whether the remaining "+C" lower bound is INDEPENDENTLY provable
(closing the Jacobian route via G1's one-point reduction), or still circular.

THE DECOMPOSITION (THEOREM, verified, uniform over ALL A∈F):
  Let V_orbit := T_E Mat^{≤r} = {M ∈ Mat_{d_N×d_0} : bottom-right (d_N−r)×(d_0−r) block = 0},
  dim V_orbit = δ. Let π_BR : Mat → BR-block ≅ Mat/V_orbit be the projection to that block.
  (a) V_orbit ⊆ image(d mult_A) for EVERY A∈F. [Proof: the endpoint GL×GL orbit-tangent identity
      d mult_A(δ⁰_A(X,Y)) = X·E − E·Y, and {XE−EY : X∈gl_{d_N},Y∈gl_{d_0}} = V_orbit exactly. Clean,
      char-free, no genericity. VERIFIED: image∩V_orbit = δ at every E-point.]
  (b) Hence rank(d mult_A) = δ + dim π_BR(image(d mult_A))   [direct sum image = V_orbit ⊕ (π_BR-part)].
  So the WHOLE content of "rank ≥ C+δ" is the "+C" claim:
      (★C)  dim π_BR(image(d mult_A)) ≥ C   at a suitable point A∈F.

WHAT WE KNOW ABOUT π_BR(image) (EXACT):
  - π_BR ∘ d mult_A = d(π_BR ∘ mult)_A, the differential of the composite map g := π_BR∘mult :
    Rep_d → BR-block. The zero locus of g (in the E-chart) is exactly Σ̄^r ∩ chart (the BR Schur
    block vanishing ⟺ rank ≤ r), so g is the local defining map of Σ̄^r near E-fibre points.
  - At the genuine fibre-over-E points (built by a section: A_0 rank ρ_0 with rowspace ⊇ rows of E,
    A_1 solving A_1 A_0 = E), dim π_BR(image) takes values ≥ C, with MIN = C exactly:
      (3,3,3)r1: C=3, π_BR ∈ {3,4,4} over branches (ρ_0=1,2,3); min=3=C.
      (3,2,3)r1: C=2, π_BR ∈ {2,2}; (2,2,3)r1: C=1, π_BR∈{1,2}; (2,2,2)r1: C=1, π_BR∈{1,1}.
  - BUT at DEEP SINGULAR points (e.g. both 3×3 factors rank 1, product rank 1, the (1,1)-stratum of
    (3,3,3)r1), dim π_BR(image) = 0 < C=3. So (★C) is NOT uniform over F; it holds only at
    generic/component points, FAILS at deep singular points.

THE QUESTION:
Q1. Is dim π_BR(image(d mult_A)) = rank(d g_A) (g = local Σ̄^r-defining map) bounded BELOW by C at a
    smooth point of Σ̄^r? At a SMOOTH point of Σ̄^r the differential of the defining map g has rank =
    codim(Σ̄^r-component through A). For a point on a TOP component of Σ̄^r (codim C) that is also in F,
    rank(d g_A) = C. So (★C) at such a point ⟺ "A is a smooth point of a top Σ̄^r-component AND lies in
    F". Is the existence of such an A (a smooth point of a top Σ̄^r-component lying in F=mult⁻¹(E)) a
    clean fact? (E is rank-exactly-r, a generic point of Mat^{≤r}; mult|_{Σ̄^r} dominant onto Mat^{≤r};
    so a generic fibre point lies in the smooth locus of Σ̄^r — IS that the clean independent argument
    for (★C)?) Or does "generic fibre point ∈ smooth locus of Σ̄^r" itself need generic flatness /
    the same wall?
Q2. CRUX: with G1 (codim F is the SAME for every rank-r target, so we need rank(d mult_A) ≥ C+δ at
    ONE well-chosen A in SOME rank-r fibre, plus generic smoothness of THAT fibre at A), can we choose
    A = a smooth point of a top component of Σ̄^r whose product mult(A) has rank exactly r? Then:
      rank(d g_A) = codim(top Σ̄^r comp) = C  [smooth pt of Σ̄^r],
      rank(d mult_A) = δ + C  [decomposition (b)],
      A is a smooth point of F (=fibre), dim F-component = card − (C+δ).
    Is THIS a non-circular proof of (★C) — i.e. is "rank(d g_A) = C at a smooth point of a top
    Σ̄^r-component" INDEPENDENT of the fibre dimension (it's a fact about Σ̄^r, codim C is LANDED), and
    does it transfer to rank(d mult_A) via decomposition (b) WITHOUT assuming the fibre dimension?
    Be blunt: does choosing A on the SMOOTH LOCUS OF Σ̄^r (not "generic point of a fibre component")
    break the circularity, since codim Σ̄^r = C is independently known (LANDED) and smoothness of Σ̄^r
    is generic + standard?
Q3. The one gap: we need such an A to ALSO be a smooth point of the FIBRE F (so dim F-comp = card −
    rank d mult_A). At a point A that is smooth on Σ̄^r with mult(A) of rank exactly r, is A
    automatically a smooth point of F = mult^{-1}(E')? (mult|_{Σ̄^r} → Mat^{=r} is a submersion at a
    smooth pt of Σ̄^r where the rank is exactly r, BECAUSE π_BR∘mult cuts Σ̄^r and the remaining δ
    directions of mult are the submersion onto Mat^{=r}; so the fibre is smooth of codim δ IN Σ̄^r,
    hence smooth of codim C+δ in Rep_d). Is that the clean closing argument? Verify the logic:
    "smooth pt of Σ̄^r + mult submersive onto Mat^{=r} along the δ-directions ⟹ fibre smooth, codim C+δ".
Q4. Compare to the homogeneous-sweep route (dim Σ^r = δ + dim F via the GL×GL action, all fibres
    H-translates). Which is the smaller formaliser surface: (a) this Jacobian-via-smooth-pt-of-Σ̄^r
    argument [needs: codim Σ̄^r = C LANDED; Σ̄^r generically smooth; the submersion-onto-Mat^{=r}
    along δ-directions; decomposition (b)], or (b) the homogeneous sweep [needs: the orbit-dimension
    sweep identity dim Σ^r = δ + dim F]? Rank them honestly for the engine.
Q5. The MOST LIKELY ERROR in the Q2/Q3 closing argument, and the cheapest exact test.
</task>

<output_contract>
  ≤ ~900 words. Sections: 1. (★C) via smooth-pt-of-Σ̄^r — is it independent/non-circular? (Q1,Q2
  blunt). 2. The fibre-smoothness closing step (Q3) — valid logic? 3. Route ranking Jacobian-via-Σ̄^r
  vs homogeneous-sweep (Q4). 4. Likely error + cheapest test (Q5).
</output_contract>

<grounding_rules>
  - Numbers are exact (Singular + sympy). Distinguish THEOREM from CONJECTURE; be blunt about circularity.
  - LANDED engine facts: codim Σ̄^r = C (cCodim, SigmaCodim); the δ thermometer (dim Mat^{≤r}=δ);
    G1 (codim F same for all rank-r targets); the GL_d baseChange + mult-equivariance; orbit-dim machinery.
  - The decomposition (a),(b) above is a verified THEOREM. char 0, alg-closed, N≥1, r≤min d_i.
</grounding_rules>
