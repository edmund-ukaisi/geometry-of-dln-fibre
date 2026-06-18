<task>
Setting: equioriented type-A quiver Q = (0 -> 1 -> 2 -> ... -> N) over a field k; path algebra kQ.
Modules are finite-dim representations (chains of vector spaces V_0 -> ... -> V_N). The indecomposables
are the interval modules M_{ij} for 0<=i<=j<=N (k on vertices [i,j] with identity arrows, 0 elsewhere) —
Gabriel for type A.

We are formalising in Lean 4 + Mathlib the codimension of G-orbits in the representation variety
Rep(Q,d) = prod_t Mat_{d_{t+1}, d_t}, where G = prod_i GL_{d_i} acts by base change. We want the
standard development of three things, and a check that they are the textbook way:

  (1) Ext^1(M_{ij}, M_{uv}) between interval modules over kQ.
  (2) The Euler/Ringel form for this quiver and the hereditary identity.
  (3) Voigt's lemma: codim of the G-orbit O_M in Rep(Q,d) equals dim Ext^1(M,M).

Please answer, independently and from first principles, each of:

  A. Give the standard projective resolution of an interval module M_{ij} over kQ (equioriented A_{N+1}),
     in terms of the indecomposable projectives P_p. Then state the resulting closed form for
     dim Ext^1(M_{ij}, M_{uv}) as an indicator over the four endpoints i,j,u,v. State dim Hom(M_{ij},M_{uv})
     likewise. Be explicit about the index convention you use (which vertex set the interval covers, arrow
     direction) since conventions differ.

  B. Write the Euler (Ringel) bilinear form <a,b> for this quiver on dimension vectors a,b in Z^{N+1}.
     State the hereditary identity relating dim Hom, dim Ext^1, and <a,b>. Confirm whether the category of
     kQ-modules for equioriented type A is hereditary (gl.dim <= 1) and Hom-finite.

  C. State Voigt's lemma precisely (tangent space to the orbit = coboundaries B^1 = image of the action
     map's differential; T_M Rep = 1-cochains Z^1-ambient; Ext^1 = Z^1/B^1) and the exact chain of
     standard facts an algebraic-geometry formalisation must establish to conclude codim O_M = dim Ext^1(M,M).
     Note any subtlety specific to: orbits being locally closed / smooth, char k, reduced vs scheme-theoretic
     tangent space, or stabiliser dimension.

  D. Is this the standard development as found in the representation-theory / quiver literature (Assem-Simson-
     Skowronski, Ringel, Gabriel-Roiter, Crawley-Boevey notes)? Name where each piece sits. Call out any
     subtlety in the equioriented type-A / hereditary special case that a formalisation might trip on.
</task>

<output_contract>
  Four sections A, B, C, D in that order. In A and B give the explicit closed-form indicators / form with
  your stated index convention. In C give the exact ordered list of facts (numbered). In D give named
  references and a short list of formalisation tripwires. Be concise; formulas over prose.
</output_contract>

<grounding_rules>
  This is a mathematics derivation + standardness review, not code. Flag explicitly anything that is your
  inference vs an established textbook fact. If a closed-form indicator depends on a convention choice, say
  so and give the form under your stated convention. Do not guess Mathlib API; if you mention Mathlib,
  mark it as a pointer to check, not a fact.
</grounding_rules>
