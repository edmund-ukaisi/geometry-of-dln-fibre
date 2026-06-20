<task>
I am formalising, in Lean 4 + Mathlib (toolchain v4.29.0), a single theorem from
quiver-representation theory / algebraic geometry, and I need a coverage map of Mathlib's
foundations plus a realistic build-ladder.

THE THEOREM (Voigt's lemma, restricted to equioriented type-A quivers).
Fix a field k and a dimension vector. Rep_d is the affine space of tuples of matrices
(the representation space of the equioriented A_N quiver: matrices A_i : k^{d_i} -> k^{d_{i+1}}).
The group G_d = prod_v GL_{d_v} acts on Rep_d by base change. For a representation M, its orbit
closure Ō_M is an irreducible closed subvariety. I have ALREADY PROVED, in pure finite-dimensional
linear algebra, that the 2-term Ringel/Voigt deformation complex gives
   orbitLinearCodim M = dim C^1 - dim(im δ^0) = dim coker δ^0 = dim Ext^1(M,M),
where δ^0 : C^0 -> C^1 is the explicit differential of the orbit map and im δ^0 is the tangent
space to the orbit at M. I want to prove the GEOMETRIC statement:
   codim(Ō_M in Rep_d) = orbitLinearCodim M  ( = dim Ext^1(M,M) ).
Here "codim" is defined concretely in my Lean as Ideal.height of the vanishing ideal of the locus
inside MvPolynomial (one variable per matrix entry) over k.

THE PLANNED ROUTE (tangent space + smoothness, NOT classical determinantal-ideal height):
  1. Ō_M is irreducible (closure of the image of the irreducible group G_d under the orbit map a ↦ a·M).
  2. M is a smooth point of Ō_M with Zariski tangent space exactly im δ^0 (homogeneity: G_d acts
     transitively on the orbit, smooth locus is dense and G-stable, so the orbit is smooth everywhere;
     tangent space = image of the orbit-map differential).
  3. smooth point ⇒ local Krull dimension of the local ring = dimension of the Zariski tangent space.
  4. height(I(Z)) = dim Rep_d − dim Z for the irreducible Z (dimension formula / catenary in
     MvPolynomial over a field).
  Combine: codim = dim Rep − dim Ō_M = dim Rep − dim(tangent) = dim C^1 − dim(im δ^0) = dim Ext^1.

QUESTIONS.
A. Is this tangent-space+smoothness route the standard, cleanest Lean/Mathlib path to a
   quiver-rep orbit-closure codimension = dim Ext^1 result? Or is there a cleaner route I'm missing
   (e.g. an orbit-dimension route dim O = dim G − dim Stab; or going via the rank-locus
   determinantal ideal; or a fibre-dimension / generic-fibre argument)? Compare them for a Lean build.
B. For EACH of the four AG/commutative-algebra pillars below, what does Mathlib v4.29 actually
   contain (give exact declaration names / namespaces if you know them), and what is realistically
   ABSENT and must be built from scratch?
     P1. Krull dimension / height in polynomial rings: ringKrullDim, Ideal.height, Ideal.primeHeight;
         Krull dim of MvPolynomial (Fin n) k = n over a field; the dimension formula
         height p + coheight p = ringKrullDim (or dim R/p = dim R − height p) for finite-type
         k-algebras / MvPolynomial; catenary instances.
     P2. Zariski tangent / cotangent space and regularity: cotangent space, KaehlerDifferential,
         IsRegularLocalRing; the bridge "regular/smooth local ring ⇒ Krull dim = embedding/tangent
         dimension".
     P3. Smoothness and GENERIC smoothness: Algebra.Smooth / Algebra.FormallySmooth, AG smoothness;
         is "a finite-type domain over a field has a dense open regular/smooth locus" available, and
         what field hypotheses does it need (char 0? perfect? algebraically closed?)?
     P4. Irreducibility and the variety side: Nullstellensatz (vanishingIdeal / zeroLocus, radical
         ideals ↔ closed sets, prime ↔ irreducible), GL_n / a product of GL's as an irreducible
         variety, image and closure of an irreducible set under a morphism.
C. FIELD HYPOTHESES: what is the cleanest hypothesis set on k under which the WHOLE chain holds
   (algebraically closed? char 0? perfect?), and which steps force which hypothesis? In particular
   does generic smoothness force char 0 or perfect, and does smooth ⇒ regular need algebraically closed?
D. The closing criterion forbids new "cited interfaces": everything must be PROVED in Lean (field
   hypotheses like [IsAlgClosed k] are allowed as hypotheses). Given that, give a realistic
   dependency-ordered build ladder with size reads ("one PR/tide", "a module", "a sizeable
   sub-library") and name the 3-5 biggest must-build pieces.
</task>

<output_contract>
Answer in five sections, terse and concrete, declaration names where you have them:
  A. Route verdict — is tangent+smoothness right; cleaner alternative if any; one-paragraph compare.
  B. Pillar-by-pillar coverage (P1..P4): PRESENT (with decl names) vs ABSENT.
  C. Field hypotheses — the cleanest set + which step forces what.
  D. Build ladder — dependency-ordered, with size reads; the 3-5 biggest must-build pieces.
  E. Biggest risk / the one thing most likely to make this much bigger than it looks.
Distinguish what you KNOW is in Mathlib from what you INFER. If unsure a decl exists, say "uncertain".
</output_contract>

<grounding_rules>
Do not invent Mathlib declaration names. If you are not confident a declaration exists at the v4.29
pin, mark it "uncertain — verify". Prefer naming the namespace/file over guessing an exact lemma name.
The diagnosis (which foundations exist, which are absent, route comparison) is what I need; any code
is illustrative only.
</grounding_rules>
