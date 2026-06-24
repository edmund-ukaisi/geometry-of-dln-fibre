<task>
Setting (deep linear networks / type-A quiver, char-0 algebraically closed field k=ℂ̄).
Fix a dimension vector d = (d_0, d_1, ..., d_N) with N ≥ 1. The representation space is
Rep_d = ⊕_{i=0}^{N-1} Mat_{d_{i+1} × d_i}(k); a point is a tuple A = (A_0, ..., A_{N-1}) of
"composable" matrices (A_i : d_i → d_{i+1}). Write
  card := dim Rep_d = Σ_{i=0}^{N-1} d_{i+1} d_i.

The multiplication map mult : Rep_d → Mat_{d_N × d_0}(k) sends A ↦ A_{N-1} A_{N-2} ... A_1 A_0
(the ordered product, a degree-N polynomial map). Fix an integer r with 0 ≤ r ≤ min_i d_i and let
E = diag(I_r, 0) ∈ Mat_{d_N × d_0}, the rank-r normal form. The object of interest is the fibre
  F := mult^{-1}(E) ⊆ Rep_d.

Known/landed facts (treat as given; all proved in our Lean engine):
1. The closed product-rank locus Σ̄^r := { A : rank(A_{N-1}...A_0) ≤ r } has geometric codimension
   codim_{Rep_d} Σ̄^r = C := cCodim(d, r), where C is the type-A "Ext / Kostant" combinatorial codimension.
   Concretely Σ̄^r = ⋃_M Ō_M, a finite union of GL_d-orbit closures Ō_M (M ranges over the
   type-A representations with all suffix/prefix ranks ≤ r and total rank exactly... the "corner-≤r" orbits),
   and codim Ō_M = finrank(deformationExt1(M,M)) = finrank C¹(M,M) − finrank(range δ⁰_M), where
   δ⁰_M : C⁰(M,M) → C¹(M,M), δ⁰_M(φ)_i = φ_{i+1} M_i − M_i φ_i, is the deformation (Voigt) coboundary, and
   - C⁰(M,M) = ⊕_v Mat_{d_v × d_v}  (one square block per vertex; this is the Lie algebra of GL_d = ∏_v GL_{d_v}),
   - C¹(M,M) = ⊕_i Mat_{d_{i+1} × d_i} = Rep_d (the arrow space).
   So codim Ō_M = card − dim O_M and the orbit tangent space at M is exactly image(δ⁰_M) ⊆ C¹ = Rep_d, of
   dimension dim O_M = finrank(range δ⁰_M). The MINIMAL codim over the components is C (i.e. the TOP /
   biggest-dimensional components achieve codim Ō_M = C; the smaller components have codim Ō_M > C).
2. The determinantal target stratum Mat^{=r} := { rank = r } ⊆ Mat_{d_N × d_0} is smooth irreducible of
   dimension δ := r(d_N + d_0 − r), and its tangent space at E is
   T_E Mat^{≤r} = { X : X has the (d_N−r)×(d_0−r) bottom-right block = 0 } (block w.r.t. the splittings
   k^{d_N}=k^r⊕k^{d_N−r}, k^{d_0}=k^r⊕k^{d_0−r}), of dimension δ.
3. The differential of mult at A, d(mult)_A : Rep_d → Mat_{d_N×d_0}, is the Leibniz product rule
   d(mult)_A(δA) = Σ_{i=0}^{N-1} (A_{N-1}...A_{i+1}) · δA_i · (A_{i-1}...A_0)
   (suffix · δA_i · prefix). Entrywise the Jacobian column at coordinate (i,s,t) is the rank-one outer
   product (suffix column s) ⊗ (prefix row t).
4. (Reduce-to-E, landed) codim mult^{-1}(B) depends only on rank(B); so WLOG B = E.
5. The target identity we want (the HARD direction): codim_{Rep_d}(F) ≥ C + δ. The EASY direction
   codim(F) ≤ C+δ is separately handled. Combined: codim(F) = C+δ, i.e. dim F = card − C − δ.
   (Numeric anchor: d=(2,2,2), r=1: C=1, δ=3, card=8, so dim F = 4. d=(2,2,2) r=0: C=3, δ=0, dim F=5.)

The ROUTE for the hard direction is generic smoothness + Jacobian rank: every variety over a char-0
field is generically smooth, so at a generic point A of EACH irreducible component F_α of F,
  dim F_α = card − rank(d(mult)_A),
because the tangent space to F_α at the smooth point A equals ker(d(mult)_A) restricted appropriately
(F is locally cut by the entries of mult − E, whose Jacobian is d(mult)_A). Hence if we can show
  (★)  rank(d(mult)_A) ≥ C + δ  at a generic point A of EVERY irreducible component F_α of F,
then every component has dim ≤ card − C − δ, so dim F ≤ card − C − δ, i.e. codim F ≥ C + δ. DONE.

WHAT IS KNOWN ABOUT (★) (from a prior pen-and-paper certificate, 13 exact cases via Singular Krull dim +
exact sympy Jacobian rank):
- F is REDUCIBLE in general. At a generic point of a TOP-dimensional component, rank(d(mult)_A) = C+δ
  exactly (so that component has dim card−C−δ). At generic points of LOWER-dimensional components,
  rank(d(mult)_A) is STRICTLY LARGER (up to d_N·d_0, the full submersion rank). So (★) is an INEQUALITY
  "≥ C+δ on every component", with equality only on the top ones.
- "rank = C+δ at ANY generic fibre point" is FALSE — it depends on which component.

THE JOB: produce the cleanest GENERAL ARGUMENT (a proof, not a per-case computation) that (★) holds:
rank(d(mult)_A) ≥ C+δ at a generic point of every irreducible component F_α of F, for ALL d and all
r ≤ min_i d_i.

Two candidate mechanisms to evaluate (find the cleanest, or a better one):

(M1) STRUCTURAL LOWER BOUND (decompose the image of d(mult)_A into a δ-part and a C-part):
   (a) δ-part (orbit-tangent of the endpoint GL×GL action): the curve t ↦ (P_t, Q_t)·A with
       mult((P,Q)·A) = P_N · mult(A) · Q_0^{-1} sweeps the GL_{d_N}×GL_{d_0}-orbit of E inside
       Mat_{d_N×d_0}; its velocity at t=0 lands in image(d(mult)_A) and equals {X E + E Y : X∈gl_{d_N},
       Y∈gl_{d_0}}... which is exactly the tangent space T_E(rank-≤r locus) = T_E Mat^{≤r}, of dim δ.
       So image(d(mult)_A) ⊇ T_E Mat^{≤r}, giving rank(d(mult)_A) ≥ δ UNIFORMLY (every A∈F, every component).
       [Caveat flagged previously: an earlier claim image ⊆ T_E Mat^{≤r} was FALSE; here we only claim ⊇.]
   (b) +C part: is there a clean complementary C-dimensional subspace W ⊆ image(d(mult)_A), transverse to
       T_E Mat^{≤r} (so rank ≥ δ + C)? Candidate: the variation that MOVES the matrix tuple along directions
       NORMAL to the orbit closure Ō_M containing the generic point A — i.e. directions in
       C¹/image(δ⁰_M), of dimension codim Ō_M ≥ C. Does d(mult)_A map a normal complement to image(δ⁰_M)
       injectively into Mat/T_E? Or is there a coordinate/Schur-block argument exhibiting C+δ visibly-
       independent columns of the Jacobian? Evaluate whether (M1) actually closes, and how the "+C" sits
       relative to the orbit-component structure.

(M2) PER-COMPONENT + dim-count: identify the irreducible components F_α of F, argue each has dim ≤
   card−C−δ by a SEPARATE structural dimension count (e.g. the fibration mult|_{Σ̄^r} : Σ̄^r ↠ Mat^{=r}
   has generic fibre dim = dim Σ̄^r − dim Mat^{=r} = (card−C)−δ over the generic rank-r point E; combine with
   the fact F = the full fibre over E and the components of F come from components of Σ̄^r intersected with
   the fibre). Does this give the per-component bound (★) cleanly, or only the generic/top one?

CRITICAL QUESTIONS:
Q1. Does (M1) genuinely produce a CLEAN UNIFORM lower bound rank(d(mult)_A) ≥ C+δ on EVERY component,
    or does the "+C" part fail/degenerate on lower-dimensional components (where rank is even bigger, so
    ≥ C+δ should still hold, but the +C MECHANISM may differ component-to-component)? Be precise about
    whether the δ-part ⊇ T_E Mat^{≤r} and a transverse C-part really sum to ≥ C+δ.
Q2. The "+C" should come from C = codim Σ̄^r. But A lies in a component Ō_M of Σ̄^r with codim Ō_M
    possibly > C (lower components). On such a component the orbit-normal space has dim codim Ō_M ≥ C.
    So the natural structural bound is rank ≥ δ + codim Ō_M(A) ≥ δ + C, with the inequality codim Ō_M ≥ C
    being EXACTLY the "C = min over components" fact. Is THIS the cleanest framing — rank(d(mult)_A) =
    δ + codim(of the orbit Ō_M through A), the +C being min-over-components — and is it actually TRUE
    (rank(d(mult)_A) = δ + codim Ō_M(A) on each orbit-component, EXACTLY, not just ≥)? If exact, that
    both proves (★) AND explains the lower-components-have-higher-rank phenomenon in one formula.
Q3. Generic smoothness: confirm the chain "char-0 ⟹ each component generically smooth ⟹ at a generic
    smooth pt A∈F_α, dim F_α = dim T_A F_α = dim ker(d(mult)_A) = card − rank(d(mult)_A)". Is the
    tangent-space-to-the-fibre = ker(d(mult)_A) identity valid at a smooth point even though F is cut by
    mult−E whose ideal may be non-radical globally (we work at a generic point of a component, where the
    LOCAL ring is regular / the component is generically reduced)? Pin the precise hypotheses.
Q4. The FORMALISER-FACING statement. We have in Lean: fibreJacobianMatrix d E A with entry
    = multSuffix(A,i+1)(r,s)·multPrefix(A,i)(t,c); finrank(ker fibreJacobian) + rank(fibreJacobianMatrix)
    = card; and codim(F) = height(fibreGenIdeal). We have the engine's deformationδ, orbitLinearCodim,
    codimRepCanonical Σ̄^r = C. What is the cleanest LEMMA(S) to hand a formaliser — ideally the EXACT
    formula rank(fibreJacobianMatrix d E A) = δ + (codim of orbit through A) if Q2 holds, or a uniform
    ≥ C+δ bound — phrased against fibreJacobianMatrix / eval_pderiv_multPoly / deformationδ?
Q5. Is the WHOLE generic-smoothness+Jacobian route actually NECESSARY, or does the fibration dim-count
    (M2 / the "dim Σ̄^r = dim F + dim Mat^{=r}" identity over the dominant restricted mult) reach codim
    F ≥ C+δ more directly WITHOUT per-component Jacobian rank? Which route has the smaller, more
    robust formaliser surface (we want to AVOID flatness/trivialization — a prior route walled on a
    determinantal-presentation circularity)?
</task>

<output_contract>
  Structured, ≤ ~1200 words. Sections in this order:
  1. VERDICT on (★): is rank(d(mult)_A) ≥ C+δ provable uniformly at a generic point of every component?
     (YES with mechanism / NO with where it breaks). One paragraph.
  2. THE CLEANEST MECHANISM: state the load-bearing identity or inequality precisely (answer Q1, Q2 —
     in particular whether rank(d(mult)_A) = δ + codim Ō_M(A) EXACTLY on each orbit-component, with proof
     sketch). Distinguish what is a THEOREM vs a CONJECTURE/heuristic.
  3. GENERIC SMOOTHNESS (Q3): the precise statement + hypotheses, and the tangent=ker validity at the
     generic smooth point. Flag any subtlety (non-radical ideal, reducedness only generic).
  4. FORMALISER-FACING STATEMENT (Q4): the cleanest lemma(s), phrased in our objects.
  5. ROUTE CHOICE (Q5): Jacobian-rank vs fibration-dim-count — which is the smaller, safer formaliser
     surface for codim F ≥ C+δ, and why. Be willing to recommend AGAINST the Jacobian route if the
     fibration is cleaner.
  6. THE ONE THING MOST LIKELY TO BE WRONG in the above, and the cheapest exact test to settle it.
</output_contract>

<grounding_rules>
  - Ground every structural claim in the given facts (the deformation complex δ⁰, orbit closures,
    T_E Mat^{≤r}, the Leibniz differential). Do not invent Lean lemma names; refer to the objects as named.
  - Distinguish THEOREM (you can prove/sketch) from CONJECTURE (plausible, untested). Mark each.
  - If you assert rank(d(mult)_A) = δ + codim Ō_M(A), give the proof sketch (why the image splits as
    T_E Mat^{≤r} ⊕ (something of dim codim Ō_M), or why the kernel is dim O_M + dim F_α, etc.).
  - char 0, algebraically closed; r ≤ min_i d_i. N ≥ 1.
  - Withhold nothing about failure modes: if (M1)'s "+C" does not split cleanly, say so explicitly.
</grounding_rules>
