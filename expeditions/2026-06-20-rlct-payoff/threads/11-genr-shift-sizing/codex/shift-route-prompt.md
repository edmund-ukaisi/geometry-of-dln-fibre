<task>
I am sizing ONE Lean 4 + Mathlib (pinned v4.29) formalisation obligation, to decide: PROVE zero-cited
(give the route + module count + hardest sub-lemma), or CITE a published lemma as a named interface.

SETTING (a deep-linear-network / type-A quiver paper, all the listed objects already LANDED in Lean,
sorry-free).
- k a field; for the geometry [IsAlgClosed k] [CharZero k]. N+1 dimensions d_0..d_N. Rep_d = ∏_{i} Mat(d_{i+1} x d_i)(k), a tuple A=(A_1,...,A_N).
- mult : Rep_d → Mat(d_N x d_0)(k), mult(A) = A_N ⋯ A_1 (ordered product).
- fibre d B := {A | mult A = B}  (an affine variety, NOT a quiver orbit / orbit closure).
- Σ̄^r := productRankLocusLE d r := {A | rank(mult A) ≤ r}  (the closed rank-≤r product locus; a UNION
  of quiver-orbit closures of the GL_d = ∏_v GL_{d_v} action P•A=(P_{i+1}A_i P_i^{-1})).
- Σ^r := {A | rank(mult A) = r} (open, exactly rank r). codim Σ^r = codim Σ̄^r (LANDED-equivalent fact).

LANDED Lean machinery (sorry-free, all in the engine `Core`):
1. codimRepCanonical (Z : Set Rep_d) : ℕ∞ — a Zariski codimension via Ideal.height of the vanishing
   ideal of the flattened locus.
2. For ANY single quiver orbit-closure O_M (= rank locus {A | rankPattern A ≤ rankPattern M}, a
   determinantal variety, GL_d-stable):
   codimRepCanonical (orbitRankLocus M) = orbitLinearCodim M = finrank Ext^1(M,M)  [the VOIGT discharge].
   This was proved via a route-c "submersion" chain: varietyDim Z_M = ringKrullDim(image of the orbit
   pullback μ_M : G=∏GL_{d_v} → Z_M) = trdeg(image) = genericDifferentialRank(μ_M) = finrank(range δ⁰),
   where δ⁰ is the quiver deformation differential φ ↦ (φ_{i+1}M_i − M_i φ_i). KEY: this whole chain is
   tailored to the GL_d orbit map μ_M; the differential is the quiver End/Ext deformation map.
3. codimRepCanonical (fibre d 0) = codimRepCanonical (Σ̄^0) = C := cCodim d 0 (the combinatorial codim).
   This worked because fibre d 0 = Σ̄^0 (over a field rank=0 ↔ =0), and Σ̄^0 IS a union of orbit closures,
   so the orbit-codim machinery (item 2 + "codim of a finite union = min over components") applies.
4. cCodim d r = cCodim (d − r) 0 (a LANDED combinatorial rank-shift), and cCodim is the geometric codim
   of Σ̄^r. Concrete: cCodim (2,2,2) 0 = 3, cCodim (2,2,2) 1 = 1.

THE TARGET (the published "Lemma 4.6", proof reproduced verbatim below):
   codim_{Rep_d} mult⁻¹(B) = codim_{Rep_d} Σ̄^r + r(d_0 + d_N − r),  for any B with rank B = r ≤ min d.
Equivalently dim mult⁻¹(B) = dim Σ̄^r − r(d_0+d_N−r). The shift r(d_0+d_N−r) is the dimension of the
determinantal variety Mat^{rk=r}_{d_N,d_0} (the rank-exactly-r matrices, ONE orbit of G_out = GL_{d_N} ×
GL_{d_0} acting by B ↦ P_N B P_0^{-1}).

PUBLISHED PROOF (complex-analytic / algebraic-geometry, verbatim): "We may assume k=ℂ. Mat^{rk=r} is an
orbit of the G_out action. Fix B, A* ∈ mult⁻¹(B). The action map G_out → Mat^{rk=r} (P ↦ P_N B P_0^{-1})
is a smooth submersion onto the single orbit Mat^{rk=r}; its local sections induce, by G_out-equivariance
(note mult(P•A) = P_N mult(A) P_0^{-1} where P•A acts only on the OUTER ends A_1's right and A_N's left),
local trivialisations of mult : Σ^r → Mat^{rk=r}. Hence mult|Σ^r is a locally trivial fibre bundle over
Mat^{rk=r}, so dim Σ^r = dim(fibre) + dim Mat^{rk=r} = dim(fibre) + r(d_0+d_N−r)."

So the math rests on: (i) Mat^{rk=r} is a single G_out-orbit of dimension r(d_0+d_N−r); (ii) the orbit map
G_out → Mat^{rk=r} is a submersion with local sections; (iii) mult : Σ^r → Mat^{rk=r} is G_out-equivariant
and the local sections trivialise it → locally trivial bundle → dim adds.

VERIFIED Mathlib gaps at v4.29 (from a prior recon I trust): NO fibre-dimension theorem (dim total =
dim base + dim fibre for a flat/locally-trivial/dominant map); NO algebraic-group-quotient G/H scheme; NO
"dim of a locally trivial bundle = base + fibre"; NO general "image of orbit map dimension" theorem. The
landed route-c (item 2) is a from-scratch substitute BUT it is specific to the GL_d orbit map μ_M whose
differential is the quiver deformation δ⁰; it is NOT a general fibre-dimension or bundle theorem.
</task>

<questions>
Evaluate each of these four routes to the TARGET, marking every Mathlib claim KNOWN/INFER/MISSING at the
v4.29 pin, and giving an honest Lean module count (+ the single hardest sub-lemma) for any route you call
provable:

1. DIRECT FIBRE-CODIM: Is mult⁻¹(B) itself a locus whose codim the LANDED orbit-codim machinery (item 2:
   codimRepCanonical via Ideal.height, the Voigt route-c) computes directly? mult⁻¹(B) is NOT GL_d-stable
   (mult(P•A) = P_N mult(A) P_0^{-1} ≠ mult(A) in general). For B≠0 it is not a union of orbit closures.
   Does item-2 machinery apply, or does B≠0 break the orbit-closure structure that item 3 relied on?

2. HOMOGENEOUS-FIBRATION: Σ^r = ⊔_{rank B'=r} mult⁻¹(B'); the rank-exactly-r B' form ONE G_out-orbit
   (dim r(d_0+d_N−r)); all fibres mult⁻¹(B') are G_out-translates hence isomorphic. So dim Σ^r =
   dim(fibre) + r(d_0+d_N−r) IF "dim(union over a single homogeneous orbit base) = fibre + base". Does the
   homogeneity (orbit-stabiliser, all fibres isomorphic by a group translation) let one AVOID a general
   Chevalley/fibre-dimension theorem — e.g. is there a Mathlib path "G acts, single orbit base, equivariant
   map ⟹ dim total = dim fibre + dim orbit" — or does this hit the SAME wall (no clean algebraic orbit-dim
   / quotient in Mathlib)?

3. ROUTE-C-STYLE DODGE for the fibre directly: bypass the bundle entirely — compute dim(mult⁻¹(B)) via
   trdeg of its coordinate ring / a Jacobian-rank argument at a smooth point, like the landed route-c did
   for Z_M. Is mult⁻¹(B) reachable with the LANDED Core AG stack (Nullstellensatz height+dim, Noether
   normalization equidimensionality, smooth⟹regular⟹cotangent=dim, cotangent=ker Jacobian, trdeg≤diffrank
   via formal smoothness)? What is the differential whose rank would give dim(fibre), and is its rank
   computable in closed form = dim Rep_d − codim Σ̄^r − r(d_0+d_N−r) WITHOUT already knowing the bundle?
   I.e. does route-c-for-the-fibre still need the bundle/equivariance to identify the rank?

4. CITE the published lemma as a named `Cited` interface (a carried structure field, exactly as the rlct
   value rlct(K^DLN_B)=½ codim mult⁻¹(B) is already Cited to Aoyagi in this codebase). Statement carried:
   "for rank B = r ≤ min d, codimRepCanonical(fibre d B) = codimRepCanonical(Σ̄^r) + r(d_0+d_N−r)", named
   `cited_bundle_shift_lemma46`. Is this the honest move given 1–3, and what is the precise minimal carried
   statement so the consumer R2-general gets rlct(K^DLN_B) = (cCodim d r + r(d_0+d_N−r))/2?

Also: independent of routes — is there a SLICKER elementary algebraic proof of the shift that sidesteps
fibre-dimension entirely (e.g. an explicit isomorphism mult⁻¹(B) ≅ mult⁻¹(B_0) × (something), or a direct
"the fibre over B is a translate/section bundle" giving codimRepCanonical equality by a Lean-expressible
constructive map)? If yes, sketch the map and size it; if no, say so.
</questions>

<output_contract>
Answer 1,2,3,4 in order with headers; then the "slicker proof?" question. For each provable route give
module-count + single hardest sub-lemma; for each blocked route name the exact missing Mathlib theorem.
Mark every Mathlib assertion KNOWN/INFER/MISSING. End with a one-line verdict:
PROVE-route-<n>-<modules>-modules  OR  CITE-lemma-4.6.
</output_contract>

<grounding_rules>
Do not assume a Mathlib lemma exists unless confident at the v4.29 pin; if unsure say INFER and name the
closest thing. The numerics and the math of the shift are already verified independently — do not re-derive
them; focus on the cheapest HONEST Lean path and size. If a route secretly re-hides the missing
fibre-dimension / orbit-dimension theorem, say so explicitly and say WHERE. I genuinely do not know whether
to prove or cite — do not anchor on either; give your independent read.
</grounding_rules>
</task>
