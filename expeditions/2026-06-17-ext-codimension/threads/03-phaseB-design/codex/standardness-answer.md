**1. Standard Proofs**

Assume the usual classical setting: algebraically closed base field, classical affine varieties, or equivalently scheme dimensions after base change.

Route (a), tangent/Voigt: textbook-standard/literature-standard.

\[
T_M\operatorname{Rep}_d=C^1(M,M),\qquad d_e(G_d\to \operatorname{Rep}_d)=\delta_M.
\]

Voigt’s lemma/orbit tangent theorem gives

\[
T_M(G_d\cdot M)=\operatorname{im}\delta_M.
\]

Since the orbit is a smooth locally closed variety,

\[
\dim(G_d\cdot M)=\dim T_M(G_d\cdot M)=\dim\operatorname{im}\delta_M.
\]

The orbit is open dense in its closure, so

\[
\operatorname{codim}_{\operatorname{Rep}_d}\overline{G_d\cdot M}
=\dim C^1-\dim\operatorname{im}\delta_M
=\dim\operatorname{coker}\delta_M
=\dim\operatorname{Ext}^1(M,M).
\]

Non-elementary inputs:

- Orbits of algebraic-group actions are locally closed. Math: textbook-standard. Mathlib: KNOW absent from your inventory.
- Orbit tangent theorem / Voigt lemma. Math: standard in module-variety geometry. Mathlib: KNOW absent.
- Smoothness of algebraic groups and homogeneous spaces, or separability of the orbit map. Math: textbook-standard. Mathlib: KNOW absent.
- Smooth variety has dimension equal to tangent-space dimension. Math: textbook-standard. Mathlib: KNOW absent/verify.
- Dense open subsets have the same dimension as their closure. Math: textbook-standard. Mathlib: INFER absent/verify.

Route (b), orbit-stabiliser/fibre dimension: textbook-standard.

\[
\operatorname{Stab}_{G_d}(M)=\operatorname{Aut}_Q(M),
\qquad
\operatorname{End}_Q(M)=\ker\delta_M.
\]

\(\operatorname{Aut}_Q(M)\) is the determinant-nonvanishing open subset of the vector space \(\operatorname{End}_Q(M)\), hence

\[
\dim\operatorname{Stab}(M)=\dim\ker\delta_M.
\]

Also \(G_d\) is open in \(C^0(M,M)\), so \(\dim G_d=\dim C^0\). Fibre dimension / homogeneous-space dimension gives

\[
\dim(G_d\cdot M)=\dim G_d-\dim\operatorname{Stab}(M)
=\dim C^0-\dim\ker\delta_M
=\dim\operatorname{im}\delta_M.
\]

Then the same codimension computation finishes.

Non-elementary inputs:

- Dimension formula \(\dim G\cdot x=\dim G-\dim G_x\). Math: textbook-standard. Mathlib: KNOW absent.
- Chevalley / constructibility and fibre-dimension theorem, if proving via the orbit map. Math: textbook-standard. Mathlib: KNOW absent.
- Dimension of nonempty principal opens equals ambient affine-space dimension. Math: textbook-standard. Mathlib: INFER absent/verify.

**2. Lean Feasibility**

Route (b) is slightly more Lean-feasible than route (a), because the stabiliser side is mostly linear algebra plus determinants:

\[
\operatorname{End}_Q(M)=\ker\delta_M,\qquad
\operatorname{Aut}_Q(M)\subseteq \operatorname{End}_Q(M)
\]

is a principal open condition.

But the hard point remains exactly the same: converting a polynomial orbit map into a statement about geometric dimension of its image closure. That needs either fibre dimension, homogeneous-space dimension, or equivalent AG dimension theory.

Working directly with `topologicalKrullDim` of \(k^n\) does not avoid this. Over a finite or non-algebraically closed field, the point-set Zariski topology on \(k^n\) is not the right geometric object. Even over algebraically closed \(k\), proving the orbit closure has the desired dimension still needs irreducibility/image-closure/fibre-dimension machinery.

Working with the coordinate-ring quotient also hits the wall:

\[
\operatorname{codim}\overline{O}=\operatorname{height} I(\overline{O})
\]

requires knowing \(I(\overline{O})\) is the right radical/prime ideal, and computing its height. Your inventory has height inequalities, not the equality/catenary/equidimensional machinery needed to compute

\[
\dim R/I = \dim R-\operatorname{height} I.
\]

So the break is not the linear algebra. It is the missing dimension theory for images/orbit closures.

**3. Honest Gap**

Already honest / small:

- \(C^1/\operatorname{im}\delta_M=\operatorname{coker}\delta_M\): KNOW present by finite-dimensional linear algebra.
- \(\dim C^1-\dim\operatorname{im}\delta_M=\dim\operatorname{coker}\delta_M\): KNOW present.
- \(\operatorname{End}_Q(M)=\ker\delta_M\): small linear-algebra proof.
- \(\operatorname{Aut}_Q(M)\) is determinant-nonvanishing in \(\operatorname{End}_Q(M)\): small/medium.

Genuine geometric builds:

- Orbit locally closed: large AG library.
- Orbit smooth / homogeneous space \(G/G_M\): large AG/algebraic-group library.
- \(T_M(G\cdot M)=\operatorname{im}\delta_M\): medium if tangent/orbit infrastructure exists; large from scratch.
- \(\dim\overline{G\cdot M}=\dim(G\cdot M)\): medium once variety dimension exists; otherwise large.
- \(\dim(G\cdot M)=\dim\operatorname{im}\delta_M\): large via tangent/smoothness or fibre dimension.
- Codimension of affine subvariety via Krull/topological dimension: medium-large unless already packaged.

Conclusion: as a geometric theorem, this is not realistically provable at this Mathlib pin without first building substantial AG dimension infrastructure, or isolating one strong geometric theorem as an assumption.

**4. Shortcuts**

(i) Type-A rank-variety shortcut: promising but still not elementary.

For equioriented type \(A\), orbit closures are standard quiver rank loci:

\[
\overline{G_d\cdot M}
=
\{A:\operatorname{rank}(A_{j-1}\cdots A_i)\le \operatorname{rank}(M_{j-1}\cdots M_i)\}.
\]

Math: standard in type-A quiver/module-variety geometry. Mathlib: INFER absent/verify.

This avoids algebraic groups after the closure theorem, but proving the codimension formula for these determinantal/quiver rank loci is still a large AG/commutative-algebra project. If assumed as one theorem, it is the cleanest geometric bridge.

(ii) Linear “codim” shortcut: most Lean-feasible, but not geometric by itself.

Define

\[
\operatorname{linCodim}(M):=\dim C^1-\dim\operatorname{im}\delta_M.
\]

Then Lean proves immediately:

\[
\operatorname{linCodim}(M)=\dim\operatorname{Ext}^1(M,M).
\]

This is honest if named as tangent/expected/orbit-linear codimension. It becomes geometric only after assuming the residual theorem

\[
\operatorname{codim}_{\operatorname{Rep}_d}\overline{G_d\cdot M}
=
\dim C^1-\dim\operatorname{im}\delta_M.
\]

**Recommendation**

Formalise the linear theorem now, and for the geometric bridge use the type-A quiver-rank-locus route rather than general algebraic groups.

Single residual fact to cite/assume if you want the Lean theorem soon:

\[
\overline{G_d\cdot M}
\text{ is the type-A quiver rank locus, and its codimension equals }
\dim\operatorname{Ext}^1(M,M).
\]

Without that or an equivalent Voigt/fibre-dimension theorem, the full geometric identity requires a substantial AG dimension-theory library first.