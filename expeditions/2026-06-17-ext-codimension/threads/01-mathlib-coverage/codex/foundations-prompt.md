<task>
We are formalising Lehalleur–Rimányi 2024 Corollary 3.5 in Lean 4 / Mathlib (toolchain v4.29.0):
the Ext-codimension of G_d-orbit closures in the representation variety Rep_d of the EQUIORIENTED
type-A quiver A_{N+1} (vertices 0→1→…→N, all arrows one direction). Target identity:
codim O_M = dim Ext^1(M,M) (Voigt), with dim Ext^1(M,M) = sum over interval-module multiplicities.

Confirmed Mathlib coverage at this pin:
- Quiver, Quiver.Path (Mathlib/Combinatorics/Quiver/), Prefunctor. NO path algebra of a quiver.
  NO quiver-representation type or category. NO Euler/Ringel form. NO hereditary/global-dimension API.
- ModuleCat with abelian structure, enough projectives (HasExt instance for Small.{v} R),
  ProjectiveResolution, Projective in ModuleCat.
- Modern derived Ext: CategoryTheory.Ext X Y n in Mathlib/Algebra/Homology/DerivedCategory/Ext/Basic.lean,
  with Ext.biprodAddEquiv (additivity over binary biproducts), Ext.biproductAddEquiv (finite).
  Older CategoryTheory.Abelian.Ext (left-derived linearYoneda functor) also present.
- ModuleCat.finite_ext: Ext N M i finitely generated, but stated over Noetherian COMMUTATIVE rings.
  Our path algebra kQ is NONcommutative — so this instance does NOT directly apply.
- AG side: NO algebraic groups at all (no GL_n group scheme, no LinearAlgebraicGroup class),
  NO orbit-dimension theorem (dim G − dim stabilizer), NO Zariski tangent space at a point of a
  scheme as a packaged result. Present: KaehlerDifferential, Module.Cotangent (cotangent of a ring
  extension), Ideal.height / Ideal.primeHeight, topologicalKrullDim, Module.length.
- Rep_d in our existing Lean engine is literally a finite product of matrix spaces
  Tuple d = ∀ i, Matrix (Fin d_{i+1}) (Fin d_i) k — a finite-dim k-vector space. The G_d-action
  (∏ GL) by conjugation is already a MulAction.

Two questions.

(a) ALGEBRA — Hom/Ext for kQ-modules. Which is the standard Lean/Mathlib development:
  (i) build kQ explicitly (MonoidAlgebra/FreeAlgebra-on-paths or k-linearisation of Paths category)
      and use ModuleCat (kQ); or
  (ii) define quiver representations directly (functor category / tuple-of-spaces structure), prove
      abelian + enough projectives, use the generic CategoryTheory.Ext there; or
  (iii) for equioriented A_{N+1} (hereditary, Ext^{≥2}=0), DEFINE Ext^1(M,N) concretely as the cokernel
      of the Hom-differential in the standard 2-term "Ringel" sequence
        0 → Hom(M,N) → ⊕_v Hom(M_v,N_v) → ⊕_{a:v→w} Hom(M_v,N_w) → Ext^1(M,N) → 0,
      avoiding derived functors entirely.
  Is (iii) the textbook development for hereditary/quiver algebras, or a bespoke shortcut we'd regret?
  If we want derived Ext to AGREE with the Ringel-sequence Ext^1, what is the cleanest bridge?

(b) ALGEBRAIC GEOMETRY / Voigt — codim O_M = dim Ext^1(M,M).
  Is an orbit-dimension (dim G − dim stab) development on Mathlib AG a large standard library build
  (roughly how large / what prerequisites: group schemes, smoothness, generic flatness, Chevalley
  constructible image, dimension of fibres)? OR is there an HONEST elementary route that stays in
  finite-dim linear algebra: Rep_d a finite-dim k-vector space; the orbit map G_d → Rep_d at M has
  differential whose image is the tangent space to the orbit; dim O_M = dim G_d − dim Aut(M) =
  dim(tangent to orbit) where the tangent space = image of (g ↦ g·M − M) = boundaries
  ∂: ⊕_v End(M_v)→⊕_a Hom(M_v,M_w); and the normal space Rep_d / T_M O_M ≅ Ext^1(M,M)
  (Voigt), all as finrank of explicit k-linear maps. Does this elementary route give the HONEST
  codim (codim of the orbit-closure as a variety) without scheme-theoretic algebraic groups, given
  that over an algebraically closed field the orbit is open in its closure and dim closure = dim orbit?
  What is the precise gap between "dim O_M computed as finrank of the tangent map image" and the
  genuine variety codimension, and is that gap citable or must it be built? Name concrete Mathlib
  declarations to build on for whichever route is standard.
</task>

<output_contract>
Four sections, terse:
1. (a) verdict: rank (i)/(ii)/(iii); name the textbook standard; one paragraph why.
2. (b) verdict: is the elementary finrank route HONEST and standard, or does it hide a gap that
   needs real AG? State the precise gap and whether it is Cited-acceptable or must be Proved.
3. The 3 concrete Mathlib declarations / namespaces to build the chosen routes on.
4. The single biggest risk in this plan.
</output_contract>

<grounding_rules>
Distinguish what you KNOW about Mathlib's current contents from what you INFER. If you are unsure a
declaration exists at v4.29, say "verify" rather than asserting it. Flag any claim about the
representation-theory literature (Ringel sequence, Voigt's lemma, Gabriel) as standard vs your inference.
</grounding_rules>
