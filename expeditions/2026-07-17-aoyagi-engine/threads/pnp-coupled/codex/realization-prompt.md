<task>
Real-analytic RLCT of F = ||C1 C2 ... CL||_Frob^2 (product of real matrices, "DLN core") at 0.
Known value: rlct_0(F) = (1/2) minAdm, minAdm = min over rank-profiles of the codimension (a QIP min).
Upper bound rlct <= (1/2)codim is Watanabe-standard; the LOWER bound is Aoyagi's content.

For the lower bound one exhibits an explicit blow-up tree (buildTree, an (S,J) recursion) resolving F to
normal crossings and checks EVERY exceptional divisor v has ratio A(v)/ord_v(F) >= (1/2)minAdm
(A = log-discrepancy, ord_v(F) = 2*ord_v of the ideal <prod C>). KILL = one divisor with ratio < (1/2)minAdm.

Exact-algebra facts I have established (take as given):
1. MONOMIAL (toric) valuations on the original matrix entries: the min ratio over all per-entry weight
   vectors is >= (1/2)minAdm for every instance tested; and it EQUALS (1/2)minAdm only for some instances
   ((3,3,2,2),(3,3,3,2,2),(4,4,2,2)). For (3,3,4) the toric-min is 9/2 > (1/2)*8 = 4, and for (4,4,4,2)
   it is 4 > 7/2. So in those the RLCT-binding divisor is NOT monomial -- it is a COUPLED (non-monomial)
   valuation coming from the Schur block-elimination shear (Delta = C22 - C21 C12).
2. The coupled binding divisor is constructed explicitly (peel + radial of the pivot row ||T||^2 + radial
   of the coupled residual ||Delta S||^2 + JOIN of the two exceptionals) and gives ratio EXACTLY
   (1/2)minAdm (Groebner-verified at (3,3,4): ratio 4; (4,4,4): 6; (3,3,3,2,2): 2).
3. Monte-Carlo estimates of rlct are biased LOW by ~0.3-0.5 uniformly (high-dim thin-shell sampling +
   log-multiplicity corrections) -- they undershoot even in the toric-binding cases where rlct=(1/2)minAdm
   is exact, so MC gives NO reliable undershoot signal.

<questions>
Q1. Given the RLCT-binding divisor can be a NON-MONOMIAL (coupled) valuation strictly below the toric min,
    is there any mechanism by which a DEEPER coupled valuation (born when a shared factor's residual core
    G = ||Dbar S||^2 recurses in a non-pivot chart) could have ratio STRICTLY BELOW (1/2)minAdm -- i.e.
    could rlct < (1/2)minAdm? If Watanabe gives rlct <= (1/2)codim and Aoyagi proves equality, does that
    already forbid any undershoot, or is "= (1/2)minAdm" for the DLN codim itself the thing in question?
Q2. The "realization / no-over-vanishing" obligation is: on every terminal chart of the tree, the pullback
    F o g achieves order exactly 2*Mval(branch) (a realizing entry exists, unit residual), NOT over-vanishing.
    Is verifying this a BOUNDED per-divisor computation (compute min-order of the explicit pulled-back
    entries along each divisor + check <= target -- decomposable, general-d), or does it require Aoyagi's
    full (S,J) induction / a global argument that cannot be reduced to a finite per-divisor check?
Q3. Is there an INDEPENDENT exact route to certify rlct_0(F) = (1/2)minAdm for a specific deep-mixed
    instance (e.g. via complex lct of the ideal <prod C> + a real/complex comparison, integral closure /
    Newton polyhedron of a monomialization, or a D-module / Bernstein-Sato computation) that does NOT go
    through constructing buildTree -- something a CAS (Singular/Macaulay2/Sage) could check on a small case?
</questions>
</task>

<output_contract>
Q1/Q2/Q3, one-sentence verdict each then <=7 lines. Mark [FACT] vs [INFERENCE]. For Q1 be adversarial:
if a coupled deeper valuation CAN undershoot (making the DLN codim/value claim the load-bearing open thing),
say so and name the mechanism. For Q3 give the most practical exact cross-check + its feasibility.
</output_contract>

<grounding_rules>
Standard singularity theory (lct, log-discrepancy, integral closure, resolution, Newton polyhedron,
Bernstein-Sato, semicontinuity) allowed. Flag claims about THIS DLN tree you cannot derive as [INFERENCE].
Do not accept my framing if wrong.
</grounding_rules>
