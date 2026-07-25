<task>
Independent adjudication (exact algebra + real analysis) for an RLCT (real-log-canonical-threshold)
LOWER bound via a resolution atlas. A per-pivot blow-up "fan" of charts covers the SINGULAR locus,
but a positive-measure "escape cone" is NOT covered by the (fixed-normalization) valid charts.
Decide: does the escape cone BREAK the lower bound rlct >= (1/2)*minAdm, or is it benign?
</task>

<facts>
SETTING: deep-linear-network (DLN) product map. Matrices C1 (3x3), C2 (3x4); loss = ||C1*C2||_F^2
(squared Frobenius), RLCT taken at the origin (all entries 0). Target lower bound: rlct >= (1/2)*minAdm,
minAdm = 8 for (3,3,4) so the bound is rlct >= 4 (for the deeper-mixed (3,3,3,2,2) instance the bound is
rlct >= (1/2)*4 = 2 by the same mechanism). Coordinates x_0..x_20 ARE the original matrix entries
(0..8 = C1's 9 entries, 9..20 = C2's 12 entries).

THE FAN: per-pivot blow-up charts. "Valid" (normal-crossings) charts pivot on V = {0,1,2,3,20}. The
charts that would pivot on W = {4,5,6,7} (shear-written C1 entries) are non-normal-crossings UNDER A
FIXED shear (their Jacobian carries a polynomial, not a monomial). The valid charts' images lie in the
cone {max_{w in W}|x_w| <= C*max_{v in V}|x_v|}. Hence the ESCAPE CONE
      E = { max_{w in W}|x_w| > C*max_{v in V}|x_v| }
is positive-measure, scale-invariant, and meets every ball around the origin, and is covered by NO valid
chart. Witness direction x = t*e_4 (only C1 entry #4 nonzero, C2 = 0).

EXACT FACTS I have:
 - The Frobenius loss ||C1*C2||^2 is INVARIANT under simultaneous coordinate permutations:
   C1 -> P*C1*Q, C2 -> Q^{-1}*C2*S for permutation matrices P,Q,S (||P M S|| = ||M||).
 - Row/column permutations of C1 act transitively on C1's 9 entries (any entry -> any entry).
 - At x = t*e_4 (t != 0): C1 = t*E_{4}, C2 = 0, loss = 0. Near it, loss = ||t*E_4*C2||^2 =
   t^2 * ||(one row of C2)||^2, a nondegenerate quadratic in the 4 entries of that C2-row.
</facts>

<questions>
Q1. Local RLCT at x = t*e_4 (t != 0 fixed): from loss ~ t^2 * ||C2-row||^2 (4 quadratic transverse
    directions, the rest loss-regular), what is the local rlct at that point? Compare to the bound
    (1/2)*minAdm.
Q2. Is the escape cone E loss-ISOMETRIC to a VALID sector? Concretely: is there a coordinate
    permutation phi (a symmetry of the loss) with phi(E) contained in the region where a valid pivot
    (v in V) dominates? If so, what does that imply for rlct(loss restricted to E) versus
    rlct(loss restricted to the valid region)?
Q3. For a loss-isometry phi and A a subset of B: order rlct(loss|A) vs rlct(loss|B). Use this + Q2 to
    bound rlct(loss|E) below. Does the (uncovered) escape cone contribute BELOW the threshold
    (1/2)*minAdm, or AT/ABOVE it?
Q4. LOWER-bound logic: vol{loss<eps} = vol{loss<eps, covered} + vol{loss<eps, escape}. Even if the
    fixed-shear atlas never covers E, does rlct >= (1/2)*minAdm still hold, given the escape cone's
    own local rlct >= (1/2)*minAdm? State precisely why (min-of-poles logic).
Q5. Is the non-coverage a MONUMENT-ADJACENT hole (a positive-measure region dragging rlct BELOW the
    bound) or a DETAIL-AT-SCALE artifact of using a FIXED shear/normalization instead of a
    pivot-adapted (permutation-closed) one? If the latter, does adapting the shear WITH the pivot
    (so the W-pivot chart becomes normal-crossings, isometric to a valid chart) close it?
</questions>

<output_contract>
For each Q1..Q5: a direct verdict + one-paragraph exact justification. Distinguish PROVEN from
INFERENCE. End with: is the escape cone (B1) a MONUMENT-ADJACENT positive-measure hole that breaks
rlct >= (1/2)*minAdm, or a DETAIL-AT-SCALE artifact dissolvable by a permutation-closed
(pivot-adapted-normalization) atlas?
</output_contract>

<grounding_rules>
Reason from the facts. Frobenius loss permutation-invariance: ||P M S||=||M|| for permutations.
RLCT via resolution: rlct(loss on U) = min over the singular strata in U of the local rlct; for A
subset of B, rlct(loss|A) >= rlct(loss|B). A loss-isometry preserves local rlct. Lower bound needs
every stratum (covered or not) to have local rlct >= the bound; loss-regular regions contribute +inf.
Keep "covered by a chart" and "local rlct value" distinct.
