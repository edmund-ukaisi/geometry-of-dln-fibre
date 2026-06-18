<task>
Setting: the equioriented type-A quiver Q = (1 ->A1 2 ->A2 ... ->A_{N-1} N) with dimension
vector d = (d_0, ..., d_N). A representation is a tuple of matrices A_t : k^{d_{t-1}} -> k^{d_t}.
Rep_d = affine space of such tuples (dim = sum d_{t-1} d_t). GL_d = prod GL(d_t) acts by base change;
its orbits are the isomorphism classes of representations. For an indecomposable-decomposition class M,
the orbit O_M has a closure Ō_M.

Two classical facts I want you to assess for provability by CLASSICAL COMMUTATIVE ALGEBRA (regular
sequences, determinantal ideal heights, Eagon-Northcott, Cohen-Macaulayness) WITHOUT invoking
algebraic-group / orbit-dimension theory (dim O = dim G - dim Stab, Chevalley fibre dimension,
scheme tangent spaces):

(1) For equioriented type A, is the orbit closure Ō_M exactly the "rank locus"
      Ō_M = { tuple A : rank(A_j ... A_{i+1}) <= r_{ij}(M) for all 0<=i<=j<=N }
    cut by the minors of the interval products? (This is the orbit-closure order = rank-pattern order.)
    What is the precise statement and its standard reference?

(2) Is the CODIMENSION of this rank locus in Rep_d computable by classical determinantal CA?
    I.e. is codim Ō_M = sum of determinantal-height contributions, via a known regular sequence /
    determinantal ideal height theorem, so that one could in principle PROVE codim = dim Ext^1(M,M)
    using only commutative-algebra height theory (Krull height, Cohen-Macaulay determinantal rings)
    rather than algebraic-group orbit dimension?
</task>

<output_contract>
- State whether (1) is a theorem and cite it precisely (author/result), and whether it holds over a
  general field / in arbitrary characteristic. Distinguish "the SET equality of varieties" from "the
  IDEAL of minors is radical / defines a reduced/normal scheme".
- For (2): give the standard codimension result for type-A quiver orbit closures. Is it a CLASSICAL
  determinantal-CA computation, or does the standard proof genuinely route through algebraic groups
  (Ext, orbit dimension)? Be explicit about which.
- Key question: for the SINGLE interval i->j the codim of {rank(product) <= r} is the generic
  determinantal codim (m-r)(n-r). But the type-A orbit closure intersects MANY such loci
  simultaneously (a "matrix Schubert"-like / quiver-flag situation). Is the resulting ideal a complete
  intersection? Cohen-Macaulay? Is its height the SUM of the individual contributions, or is there
  excess intersection? Name the relevant theory (Zelevinsky / Lakshmibai-Magyar quiver loci,
  Knutson-Miller-Shimozono, Buch-Fulton, Bobinski-Zwara normality/CM).
- Estimate the SIZE of a from-scratch Lean (Mathlib) build of "codimension of a type-A quiver rank
  locus by determinantal CA". Compare to a from-scratch "algebraic-group + orbit-dimension" build.
  Which is the smaller / more self-contained foundational build?
- Flag every place you are inferring vs citing a definite theorem.
</output_contract>

<grounding_rules>
- Distinguish set-theoretic variety equality from scheme-theoretic / ideal-radicality claims explicitly.
- If the codimension does NOT decompose as a sum of independent determinantal heights (excess
  intersection / non-complete-intersection), say so and explain what the correct CA statement is.
- Do not assume Mathlib has any of: algebraic groups, orbit dimension, determinantal variety codim,
  the catenary equality dim R/I = dim R - height I. It has only Krull dim, Ideal.height, and Krull's
  height theorem (height <= number of generators), as inequalities.
</grounding_rules>
