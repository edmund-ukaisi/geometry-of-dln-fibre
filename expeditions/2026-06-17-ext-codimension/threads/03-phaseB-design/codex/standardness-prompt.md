<task>
Setting: formalising in Lean 4 + Mathlib (toolchain v4.29.0) a result from representation theory of
quivers / module varieties.

FIXED OBJECTS (already formalised, honest, sorry-free):
- Q = equioriented type-A quiver A_{N+1}: vertices 0→1→…→N, all arrows one direction.
- Rep_d = the representation variety: literally the finite-dimensional k-vector space
  Tuple d = ∏_{i=0}^{N-1} Matrix (k^{d_{i+1}}) (k^{d_i})  — a tuple of edge matrices. Affine space A^n.
- G_d = ∏_{v=0}^{N} GL_{d_v}(k), acting on Tuple d by base change
  (P • A)_t = P_{t+1} · A_t · P_t^{-1}.  Already a Mathlib MulAction.
- The deformation/Ringel complex δ_M : C⁰(M,M) → C¹(M,M), with
  C⁰ = ∏_v End(M_v) = Lie(G_d), C¹ = ∏_t Hom(M_t, M_{t+1}) = Tuple d = T_M Rep_d,
  δ_M(ξ)_t = ξ_{t+1} M_t − M_t ξ_t. (im δ_M is the tangent space to the orbit G_d·M at M.)
- Ext¹(M,M) := coker δ_M (the deformation-complex Ext¹; honest for hereditary kQ since Z¹=C¹).
  finrank(Ext¹(M,M)) is already proved equal to a known multiplicity sum.

GOAL: prove, as a Lean theorem (NOT merely cite), the GEOMETRIC identity
  codim_{Rep_d}( closure of the orbit G_d·M ) = finrank Ext¹(M,M).

Confirmed Mathlib coverage at this pin (I have grepped):
- NO algebraic groups / group schemes / LinearAlgebraicGroup. NO Lie algebra of a matrix group as
  a packaged object. NO scheme-theoretic Zariski tangent space. NO variety dimension; NO
  "dim orbit = dim G − dim stabilizer" in any form (orbit–stabiliser in Mathlib is purely a
  cardinality/group-equiv statement, MulAction.orbitEquivQuotientStabilizer — zero dimension content).
- NO Chevalley constructible-image, NO fibre-dimension theorem, NO generic flatness.
- PRESENT: ringKrullDim, topologicalKrullDim, Ideal.height + Krull's height theorem (Höhensatz, as an
  INEQUALITY height ≤ spanrank), ringKrullDim_quotient_le (INEQUALITY only), MvPolynomial Krull dim
  = card of variables (Noetherian). NO "dim R/I = dim R − height I" equality (no catenary/
  equidimensional dimension theory). NO transcendence-degree = Krull-dimension theorem for f.g.
  domains over a field.
- PRESENT and heavily used: full finite-dim linear algebra (LinearMap.range/ker/finrank, rank-nullity,
  Submodule.finrank_quotient_add_finrank, LinearEquiv.finrank_eq).

QUESTIONS:
1. What is the STANDARD mathematical proof that codim of a G-orbit closure in a representation
   variety equals dim Ext¹(M,M)? Lay out the two classical routes precisely:
   (a) tangent-space / Voigt: T_M(orbit) = im δ_M, orbit smooth ⇒ dim orbit = dim im δ_M, orbit
       open dense in closure ⇒ dim closure = dim orbit, codim = dim Rep − dim im δ = dim coker δ;
   (b) orbit–stabiliser fibre dimension: dim orbit = dim G − dim Stab, Stab = Aut(M) open in End(M).
   For EACH, name the precise non-elementary inputs (which theorems about varieties/algebraic groups
   are actually invoked).
2. Given the Mathlib desert above, which route is more Lean-feasible, and what is the MINIMAL
   foundational package each requires? Is there a way to get the geometric codimension that
   AVOIDS building a general algebraic-group / variety-dimension library — e.g. by working with
   topologicalKrullDim of the Zariski topology on the affine space k^n directly, or via Krull
   dimension of the coordinate-ring quotient by the orbit-closure ideal? What precisely breaks?
3. The honest gap: the finrank coker δ identity is pure linear algebra and already done. Pin down
   exactly which geometric facts (orbit locally closed; dim closure = dim orbit; smoothness of the
   orbit; dim orbit = finrank im δ) are the genuine from-scratch builds vs. citable-in-Lean, and
   estimate the SIZE/shape of building each honestly in Lean (small wrapper / medium / large library /
   research-grade). Is "codim orbit closure = dim Ext¹" realistically provable in Lean at this pin
   without first contributing a substantial AG dimension-theory library to Mathlib?
4. Is there a NON-OBVIOUS shortcut specific to THIS situation that sidesteps general AG: e.g.
   (i) the orbit closure as the explicit determinantal rank-variety {A : rank patterns ≤ r}, whose
   codimension might be computable by an explicit regular sequence / known determinantal-variety
   codim formula; (ii) defining "dim orbit" purely as finrank im δ_M and "codim" as
   finrank Rep − finrank im δ_M, proving THAT equals finrank Ext¹ trivially, and then separately
   justifying that this finrank-codim equals the topological/Krull codim? Which sidestep is the most
   honest and the most Lean-feasible, and what is its residual cited assumption?
</task>

<output_contract>
Terse, sectioned by question. For each named theorem, mark KNOW vs INFER about Mathlib v4.29.
For the standard math, mark textbook-standard vs your inference. End with: the single route you would
recommend, and the single residual fact that must be Cited/Assumed if any.
</output_contract>

<grounding_rules>
Distinguish what you KNOW about Mathlib's current contents from what you INFER; say "verify" when unsure.
Flag literature claims (Voigt's lemma, Gabriel, determinantal-variety codimension, module-variety
geometry) as standard vs inference. Do not invent Mathlib declaration names.
</grounding_rules>
