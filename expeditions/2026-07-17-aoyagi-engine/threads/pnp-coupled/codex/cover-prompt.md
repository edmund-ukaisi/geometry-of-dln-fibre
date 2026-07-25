<task>
Setting: real-analytic RLCT (real log-canonical threshold / learning coefficient) of
F(C) = ||C^(1) C^(2) ... C^(L)||_Frob^2, the squared Frobenius norm of a product of L real
matrices ("deep linear network core"), at the origin C=0. Widths are positive integers d
(monotone). This is Aoyagi (2023)'s learning-coefficient computation for DLNs. The known answer:
rlct_0(F) = (1/2) * min_t Mval(t), a minimum over admissible rank-profiles t of an explicit
codimension Mval(t) (a sum of per-layer codimension drops). The upper bound rlct <= (1/2)*codim is
Watanabe-standard; Aoyagi's content is the matching lower bound.

Established facts (take as given; verified by exact algebra + Groebner in this project):
1. Ideal-invariance (Aoyagi Lemma 1): rlct_0(sum f_i^2) depends only on the ideal <f_i> in the
   local ring of real-analytic germs at 0. (Two-sided, proven.)
2. Block-elimination (Schur): for a unit pivot block, unipotent-polynomial Q1,Q2 give
   Q1 A Q2 = diag(A1, Delta), so <A> = <diag(A1,Delta)> as ideals. General corank. (Proven.)
3. Aoyagi's resolution is an EXPLICIT sequence of blow-ups (a "buildTree" (S,J) recursion, Cases 1/2),
   NOT abstract Hironaka. On each leaf-chart the pullback ideal <(prod C) o g> equals a monomial ideal
   <diag(b_1,...,b_M)> with b_1 | b_2 | ... | b_M (a divisibility chain), so ||prod C||^2 o g = b_1^2 * unit.
4. At a genuinely COUPLED corank>=2 minimizer (e.g. widths (3,3,4), profile t=(1,0), Mval=8), the
   per-branch resolution is: block-elim peel -> radial resolution of the pivot row ||T||^2 (exceptional q)
   AND radial resolution of the coupled 2x2 residual ||Delta S||^2 (exceptional u) -> JOIN (blow up {q=u=0},
   q=E, u=E*alpha). Result on that chart: F o g = E^2 * (U_T + alpha^2 * G) with unit(0)=1, Jacobian E^7,
   ratio (7+1)/2 = 4 = (1/2)*8. The coupling RAISES the threshold vs the naive independent estimate
   (which undershoots: e.g. (3,3,2,2) coupled branch gives 2, naive max-of-parts gives 3/2).

The project's own decorrelated review flagged that the ALGEBRA (facts 1-3, the per-chart ideal identity
and its maintenance across the (S,J) recursion) is general and sound, but that the GEOMETRIC HALF is
un-probed at coupled corank>=2, specifically:
- (Jacobian) each leaf-chart's |det Dg| = monomial * nonvanishing-unit on the WHOLE chart domain (not just
  the germ at the chart origin).
- (COVER) the finite family of leaf-charts, each restricted to a COMPACT sub-domain, covers a punctured
  neighbourhood of 0 up to a measure-zero set. The charts are composites (blow-up o unipotent-shear o
  blow-up o ...); the shears depend on the coupled residual. A naive "pivot-box x everything-else" chart
  can let a direction ESCAPE (illustrated by F=x^2+y^4: a resolution that omits the y-direction gives a
  wrong, too-high lower bound).

<questions>
Q1. For the LOWER bound rlct_0(F) >= (1/2) min Mval, is the geometric COVER (that the explicit blow-up
    leaf-charts with compact sub-domains cover a punctured nbhd up to measure zero) genuinely NECESSARY,
    or can the lower bound be obtained WITHOUT a full cover -- e.g. by a from-below domination F >= (monomial)
    valid globally near 0, or by ideal-invariance applied on the original (un-blown-up) space? Give the
    decisive reason either way.
Q2. IF the cover is necessary: is proving it for an EXPLICIT sequence of blow-ups interleaved with
    unipotent polynomial shears a BOUNDED / decomposable computation (a fan-completeness / box-inflation
    bookkeeping that a patient team can reproduce for general widths), or does it hide a genuinely deep /
    open input (a resolution-of-singularities monument, or a properness failure specific to coupled
    corank>=2)? What is the load-bearing fact, and could coupled corank>=2 introduce a NEW escape
    mechanism absent at corank<=1?
Q3. Is there any lighter route to the lower bound that is specific to sum-of-squares of a MATRIX PRODUCT
    (using the multilinear structure) rather than a general resolution? e.g. a Lojasiewicz-type inequality,
    a direct integral estimate, or a homogeneity/scaling argument.
</questions>
</task>

<output_contract>
Three sections Q1/Q2/Q3. For each: a direct verdict in the first sentence, then <=8 lines of reasoning.
For Q2 end with a one-word classification: BOUNDED-REPRODUCE or DEEP-MONUMENT or GENUINELY-SPLIT, plus the
single sharpest test that would discriminate. Mark every claim as [FACT] (standard/provable) or
[INFERENCE] (your judgement). Be adversarial: if the "cover is bounded" story has a hole at coupled
corank>=2, find it. Do not rubber-stamp.
</output_contract>

<grounding_rules>
You may use standard singularity-theory / RLCT facts (Watanabe, Atiyah-Bernstein-Gelfand resolution of
integrals, toric resolution, Newton-polyhedron rlct). Flag anything you assert about THIS specific DLN
tree that you cannot derive from the given facts as [INFERENCE]. Do not accept my framing if wrong -- if
the cover is NOT necessary, say so and give the shortcut.
</grounding_rules>
