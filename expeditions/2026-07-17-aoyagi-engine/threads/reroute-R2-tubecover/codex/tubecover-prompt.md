<task>
Independent adjudication (exact algebra + real analysis). A resolution-of-singularities atlas
question for a real-log-canonical-threshold (RLCT) LOWER bound. Decide: does the per-pivot
blow-up "fan" of charts cover a neighbourhood of the origin UP-TO-NULL in the sense the RLCT
lower bound needs, or is there a positive-measure UNCOVERED region that can break the bound?
</task>

<facts>
INSTANCE (a real, banked witness — deep-linear-network product-map, (3,3,3,2,2), t=(2,2,1,0)).
After two det-1 block-elim peels + radialising two shared factors, ONE terminal leaf chart has:
  C3bar = [[1,p],[q,s],[u,v]]  (3x2),   C4bar = [[1,c],[d, c*d+f]]  (2x2),
  Y = C3bar*C4bar  (3x2),
  loss  = (w*y)^2 * R,   where  w,y are the two exceptional radials (coordinates >=0),
  R = ||Y_row0||^2 + (d2)^2 ||Y_row1||^2 + (d1)^2 ||Y_row2||^2   (d1,d2 = coupling scalars),
  R(origin) = 1   (because Y[0,0] = 1 + p*d has constant term 1: the "kept rank-survivor pivot").

The chart's TWO-SIDED ideal identity <loss's ideal> = <(w*y)^2> requires dividing by the pivot
quotient  u_piv := Y[0,0] = 1 + p*d, whose reciprocal 1/(1+pd) is regular only on {1+pd != 0}.
So the chart's clean two-sided (normal-crossing) form is valid on {1+pd != 0}, a CODIM-1 open set;
its zero locus {1+pd = 0} = {pd = -1} is a codim-1 hypersurface NOT through the origin (min dist
sqrt(2) in (p,d)). A compact source box sits inside {1+pd != 0} but a large-enough box meets the
tube {|1+pd| < eps} (positive measure).

The "born-sibling fan": the OTHER pivot choices in the two blow-ups (pivot on a different entry of
C3 / of C4). Different sibling => different exceptional radials => different pivot quotient.

EXACT FACTS I have verified (sympy, over Q / real):
 - {R = 0} (real, sum of squares => every summand 0) = {Y = 0} = {p*d=-1, f=0, q=s/p, u=v/p}
   for generic d1,d2 != 0: CODIM 4 (not codim 1).
 - On the codim-1 tube {1+pd = 0} MINUS the codim-4 {R=0}: R > 0 (sampled min ~0.012).
 - loss = (w*y)^2 * R. Singular locus {loss=0} = {w*y=0} UNION {R=0}.
 - {1+pd=0} meets {loss=0} only on: {w*y=0} (exceptional divisor) OR {R=0} (codim 4).
</facts>

<questions>
Q1. For the RLCT LOWER bound rlct(loss) >= 1/2 * Mval computed as sum over charts of the
    per-chart monomial read-off (from the w,y divisor exponents): what is the correct object that
    each chart must have "bounded below" on its integration domain -- the single pivot quotient
    (1+pd), or the full residual R (sum of squares)? State precisely why.
Q2. Given {R=0} is codim 4 while {1+pd=0} is codim 1: on the codim-1 tube {1+pd ~ 0}, where
    w*y != 0 and R > 0, does the w,y-divisor read-off remain VALID (i.e. does the vanishing of
    the single pivot quotient 1+pd lower the RLCT there)? Consider that loss = (w*y)^2 * R with R
    a strictly positive continuous factor there.
Q3. At the exceptional corner {1+pd ~ 0} AND {w*y ~ 0} (both small): is this corner covered, for
    the LOWER bound, by the SAME (canonical) chart's monomial reading, or does it require a
    DIFFERENT born-sibling whose own pivot quotient is nonzero there? (loss = (w*y)^2 * R, R>0.)
Q4. The genuinely unresolved locus {R=0} (codim 4) is itself a smaller matrix-product-vanishing
    locus {C3bar*C4bar = 0}. Is resolving it (a) the SAME recursion one level down (detail-at-
    scale), or (b) a new obstruction? Does the born-sibling FAN at THIS level need to cover the
    {R=0} tube, or does the recursion's deeper charts handle it?
Q5. OBSTRUCTION test: is there a POSITIVE-MEASURE region near the origin that (i) meets the
    singular locus {loss=0} AND (ii) lies in the {pivot-quotient ~ 0} tube of EVERY born-sibling
    simultaneously -- a genuine cover hole for the lower bound? Or is every such common-tube
    intersection contained in the codim>=2 locus {R=0}?
</questions>

<output_contract>
For each Q1..Q5: a direct verdict + a one-paragraph exact-reasoning justification. Distinguish
INFERENCE from PROVEN. End with: is the born-sibling fan cover a DETAIL-AT-SCALE obligation
(clean up-to-null, recursion handles the deep stratum) or a MONUMENT-ADJACENT hole (positive-
measure uncovered singular region), for the LOWER bound specifically.
</output_contract>

<grounding_rules>
Reason from the facts given; do not invent a different instance. Sum-of-squares real geometry:
a real sum of squares vanishes iff every summand vanishes. RLCT lower bound needs the atlas to
cover a nbhd of the SINGULAR locus up-to-null; loss-regular regions (loss bounded away from 0)
need no chart. Keep "the single pivot quotient" and "the full residual R" strictly distinct.
</grounding_rules>
