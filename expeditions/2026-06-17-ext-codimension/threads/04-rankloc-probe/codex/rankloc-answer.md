**Bottom Line**

(1) **Yes, for equioriented type A this is a theorem.** If `r = r(M)` is the rank array of a representation `M`, then the orbit closure is exactly the rank locus cut out by the inequalities
\[
\operatorname{rank}(A_j\cdots A_{i+1})\le r_{ij}(M).
\]
A precise modern statement is Knutson-Miller-Shimozono, Definition 1.1 and Lemma/Convention 1.3-1.4: for an occurring rank array, the quiver locus `Ω_r` is the closure of the `GL`-orbit with that rank array. Their Theorem 1.14 identifies it scheme-theoretically via the Zelevinsky map with a Schubert patch. Lakshmibai-Magyar, Theorem 2.2, proves the stronger ideal statement: the minors-of-products ideal is prime and is the vanishing ideal. These results are over an arbitrary field; KMS explicitly say their schemes are defined over `Z` and their results hold over arbitrary `k`. ([arxiv.org](https://arxiv.org/pdf/math/0308142))

So distinguish:

- **Set/variety equality:** yes, orbit closure equals rank-pattern locus.
- **Scheme/ideal statement:** also yes in type A equioriented: the product-minor ideal is radical, in fact prime, and the scheme is reduced; KMS/LM further give normal and Cohen-Macaulay, with rational singularities in characteristic zero language. ([arxiv.org](https://arxiv.org/pdf/alg-geom/9709018))

The older standard degeneration-order reference is Abeasis-Del Fra, *Degenerations for the representations of a quiver of type A_m*, J. Algebra 93 (1985), 376-412; Lakshmibai-Magyar list it as the dimension/degeneration source. ([arxiv.org](https://arxiv.org/pdf/alg-geom/9709018))

**Codimension**

The standard codimension formula is
\[
\operatorname{codim}(\Omega_r)
=
d(r)
=
\sum_{0\le i<j\le N}
(r_{i,j-1}-r_{ij})(r_{i+1,j}-r_{ij}),
\]
the sum of the areas of the Buch-Fulton rectangles. Equivalently, with lace multiplicities `s_{ab}`,
\[
d(r)=\ell(v(r))-\ell(v(\mathrm{Hom}))
=
\sum_{0\le k\le i<j\le m\le N}
s_{k,j-1}s_{i+1,m}.
\]
This is stated in Buch-Fulton and in KMS Corollary 1.16. ([arxiv.org](https://arxiv.org/pdf/math/9804041))

But this is **not** a naive sum of generic determinantal codimensions for all interval products. The conditions are highly dependent. The correct theory is quiver loci / Zelevinsky maps / Schubert determinantal ideals / matrix Schubert varieties, not a regular sequence of all product minors. KMS explicitly frame these ideals as “minors in products of generic matrices” analyzed through Schubert determinantal ideals and Zelevinsky’s map. ([arxiv.org](https://arxiv.org/pdf/math/0308142))

One correction to the premise: for a **non-adjacent single product** `BA`, the locus `rank(BA) ≤ r` in the space of pairs `(A,B)` need not have generic matrix codimension `(m-r)(n-r)`. Example, for two `2×2` maps and condition `BA=0`, the ambient dimension is `8`, while the component with `rank A = rank B = 1` and `im A ⊂ ker B` has dimension `5`, so codimension `3`, not `4`. This is my calculation, not a cited theorem.

**Complete Intersection?**

No, not in general. These quiver ideals are **Cohen-Macaulay, normal, reduced/prime** in the equioriented type-A case, but they are not generally complete intersections. Their height is the Buch-Fulton/KMS rectangle sum above, not the sum of all individual interval determinantal heights. The right CA/geometric package is Schubert/quiver determinantal theory: Zelevinsky, Lakshmibai-Magyar, Buch-Fulton, Knutson-Miller-Shimozono; Bobinski-Zwara extend normality/CM/rational-singularity results to arbitrary type-A orientations. ([arxiv.org](https://arxiv.org/abs/1307.6261))

**Ext¹ Comparison**

The equality
\[
\operatorname{codim}\overline{O_M}=\dim \operatorname{Ext}^1(M,M)
\]
is usually proved by the representation-theoretic orbit-dimension route:
\[
\dim O_M=\dim GL_{\mathbf d}-\dim \operatorname{End}(M),
\]
combined with the hereditary Euler form. That proof genuinely uses algebraic-group/orbit-dimension ideas. It is not the same as the Lakshmibai-Magyar/KMS codimension proof.

Inference: in equioriented type A, one can separately compute `dim Ext¹(M,M)` from interval summands and match the KMS lace-sum formula, but that is a combinatorial homological comparison, not a generic determinantal-height or regular-sequence proof.

**Lean Feasibility**

A from-scratch Lean proof via “determinantal CA” is the larger build. You would need polynomial rings, minors, determinantal ideals, radical/prime/height, matrix Schubert ideals or standard monomial/Groebner theory, and dimension-height infrastructure not currently assumed.

The algebraic-group/orbit-dimension route is still substantial, but smaller and more self-contained for proving `codim = Ext¹`: mostly finite-dimensional linear algebra, `End`, `Ext¹` via an explicit complex, rank-nullity, plus a comparatively small amount of affine orbit-dimension theory. If the goal is a Lean formalization, I would not start with quiver determinantal CA.