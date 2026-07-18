<task>
Independent read on a blow-up/monomialization construction (Aoyagi 2023, "learning
efficiency of deep linear networks"). I withhold my own conclusions; give yours.

CONTEXT (page-pinned from the preprint, pp.14-22; treat as verbatim ground truth):

The construction resolves the ideal <prod_{s=1}^L C^{(s)}> by a recursive blow-up. State
carries a residual block D_J = (d_ij) of size (M(S)-J) x (M^{(S+1)}-J), a diagonal of
monomials diag(b_1,...,b_{M(S)}) in exceptional coordinates u_{s,k}, and per-coordinate
label vectors T_{s,k} in Z^L with running-min tilde_t_{s,k} = min_S' t^{(S')}_{s,k}.

CASE 1 (p.15-16): a run b_{J+1}=...=b_{J+J1}, b_{J+J1+1} != b_{J+J1}. Fix the Def-4-minimal
u_{s,k} with tilde_t = J+J1. Then p.16 top, VERBATIM:
  "Construct the blow-up along the submanifold
     { d_ij = 0 (i=J+1,...,J+J1, j=J+1,...,M^{(S+1)}),  u_{s,k} = 0 }."
Then the paper presents:
  Case 1(1): "Consider instances in which [ the whole d-block ] = u_{s,k} * [ d'-block ]"
             (i.e. u_{s,k} factored out of the entire block; the d_ij become d'_ij = d_ij/u_{s,k}).
  Case 1(2): "Consider instances in which [ the d-block ] = u_{S,J+1} * [ corner=1; d'_ij ]"
             (i.e. the CORNER entry d_{J+1,J+1} becomes the exceptional coordinate u_{S,J+1},
             corner ratio = 1, and u_{s,k} = u_{S,J+1} * u'_{s,k}).
After 1(2) she applies a regular (unipotent) shear Q to clean the first row.

CASE 2 (p.19-20): blow-up along { d_ij = 0 (i=J+1,...,M(S), j=J+1,...,M^{(S+1)}) } (the whole
residual block, NO u variable in the center). Presented via the corner d_{J+1,J+1}=u_{S,J+1} as
representative.

Between cases the invariant "T_{s,k} <= T_{s',k'} or T_{s,k} >= T_{s',k'}" (total comparability
of all label vectors) is maintained (p.15).

QUESTIONS:

Q1 (chart count / recursion fan-out). A blow-up along the submanifold {d_ij=0 (block), u_{s,k}=0}
   is a blow-up of a smooth center. (i) What is the codimension of that center in the ambient, in
   terms of J1, M^{(S+1)}, J? (ii) How many standard affine coordinate charts does such a blow-up
   have, and does a faithful resolution's recursion descend into ALL of them, or only into the two
   the paper writes (1(1) and 1(2))? (iii) Are Case 1(1) and Case 1(2) the ONLY two charts, or are
   they representatives (1(1) = the chart where u_{s,k} is the pivot; 1(2) = one representative of
   the charts where some d_ij is the pivot)? If representatives, how many charts total, and what
   role does the "by a blow-up process" phrasing + the total-comparability invariant play in the
   paper's compression to two written cases?

Q2 (does a corner-only chart set cover?). Consider ONLY the u-pivot chart (1(1)) plus the SINGLE
   corner d-pivot chart (1(2) at (J+1,J+1)). Does the union of these two charts' images cover a
   neighbourhood of the blown-up center, or is there a gap? Give a concrete missed point if there
   is a gap (e.g. in a 2x1 residual block, coordinates (c11,c12), what happens to the point
   (0, eps)?).

Q3 (a faithful covering family). Claim under review: "the blow-up of R^d at the coordinate origin
   is covered EXACTLY by its d standard affine pivot charts in the max-modulus normalization:
       chart_i(u)_k = u_i           if k = i
                    = u_i * u_k      if k != i,
   with domain { |u_i| <= R and |u_k| <= 1 for all k != i }; the union of the d chart-images over
   these domains equals the cube [-R,R]^d." Is this a faithful/standard rendering of the affine
   charts of a blow-up of a codimension-d coordinate center? Is the equality (union of images =
   cube) correct? Does a single fixed chart (say chart_0) fail to cover the cube for d>=2, and
   what does it miss? Does the Jacobian determinant of chart_i equal u_i^{d-1}?

Q4 (bottom line for a formal coverage proof). To PROVE (not assert) that the enumerated charts
   cover a neighbourhood of the zero locus at each blow-up node, must the construction emit the
   FULL per-node pivot family (one edge per center coordinate), or can it emit just the two written
   representatives and recover full coverage later via the total-comparability invariant across the
   tree's deeper branching? Which is it, and why?
</task>

<output_contract>
Answer Q1-Q4 in order, terse. For each, lead with the direct answer (a number / yes-no), then
one or two sentences of justification. End with a one-line BOTTOM LINE naming which of these two
readings is correct:
  (a) recursion descends into the full per-node pivot family (one chart per center coordinate);
  (b) two written charts per node suffice and full coverage is recovered via the invariant across
      deeper branching.
</output_contract>

<grounding_rules>
Distinguish standard algebraic-geometry FACT (blow-up chart theory) from INFERENCE about Aoyagi's
specific intent. Flag explicitly where you are inferring her intent vs stating blow-up fact. Do not
claim the paper says something it does not; the verbatim center + case descriptions above are all
you have from the pages.
</grounding_rules>
