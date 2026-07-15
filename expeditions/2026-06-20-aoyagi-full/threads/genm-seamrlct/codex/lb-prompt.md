<task>
Decide ONE sharp question about deep linear network (DLN) RLCTs. Argue whichever way the math goes; I
withhold my own leaning. Exact algebra / resolution of singularities.

BACKGROUND (established, take as given):
- DLN loss K(A)=||L_{p-1}...L_0||_F^2 (product of composable real matrices), zero set = fiber mult^{-1}(0),
  codim = minAdm (a composite-rank codimension). Watanabe universal bound: rlct_x <= codim_x/2 everywhere.
- CITED theorem (Aoyagi): the GLOBAL rlct = codim/2 (saturates). The LOCAL statement rlct_x = codim_x/2 at
  every fiber point is an OPEN conjecture (Lehalleur-Rimanyi state it as "future work").
- Prop rlct_elem tools: (S1) rlct(F+G)=rlct(F)+rlct(G) for F,G>=0 in DISJOINT variables; (S2) rlct(FG)=
  min(rlct F,rlct G) disjoint; (S4) rlct(sum of e squares)=e/2; (S3) invariance under nonzero-Jacobian
  coordinate change and bounded-factor equivalence.

THE SETUP. An explicit resolution (a "telescoping-Schur atlas") stratifies the parameter space by the rank
profile of the successive layer-products, and on each big-cell CHART writes the loss (up to S3) as a sum of
"biquadratic seam" blocks ||F_j E_j||^2 (each E_j a transverse Schur block, each F_j a spectator = a product
of the deeper layers), plus a reduced-head recursion. On a chart, deepgate proved the Nat inequality
C_k >= minAdm - ab (codim with a corank charge), where C_k is the chart's transverse codimension.

WHAT IS NEEDED (strictly weaker than the open conjecture): a LOWER BOUND
        rlct_x( loss )  >=  (minAdm - ab)/2      at EVERY point x,
NOT the sharp equality rlct_x = codim_x/2. There is SLACK at deeper strata: C_k > minAdm-ab strictly
(the deep-degeneration codim grows ~ k^2 while the target is fixed), so the lower bound tolerates a rlct
DEFICIT below codim/2 as long as the deficit is smaller than the slack.

THE QUESTION (answer decisively):
  Does the complete rank stratification (every point lies in the big-cell INTERIOR of its own actual rank
  profile) + the biquadratic Morse-Bott structure give rlct_x >= (minAdm-ab)/2 at EVERY point NATIVELY (from
  S1-S4 + the Nat gate, no Aoyagi)? OR is there a genuine point -- the "entangled" locus where the shared
  head acquires a kernel aligned with both the reduced layer H and a seam FE while a spectator loses rank --
  where the transverse loss is NOT boundedly-equivalent to a sum/product of disjoint biquadratic blocks, so
  the native lower bound (not just the equality) can fail, and only cited Aoyagi / the open conjecture secures
  it?

SUBQUESTIONS:
Q1. Can a DLN transverse loss be boundedly-equivalent to a "cyclic" monomial such as
    e1^2 e2^2 + e2^2 e3^2 + e3^2 e1^2 (every variable degree <=2, but Newton-nondegenerate with rlct 3/4 <
    codim/2 = 1)? I.e. do genuine rlct DEFICITS below codim/2 occur at deep DLN points, or does the
    multilinear (linear-in-each-layer) structure of the product forbid the offending Newton polyhedra?
    Note each entry of the product is MULTILINEAR (degree 1 in each layer), so each monomial of the loss has
    every variable to degree <= 2 -- but as the cyclic example shows, degree<=2 alone does NOT forbid a
    deficit. Give an explicit smallest DLN chain + fiber point with rlct_x < codim_x/2, or prove none exists.
Q2. If a deficit occurs, is it bounded by the slack? Give the worst deficit ratio rlct_x/(codim_x/2)
    achievable at a DLN point, and compare to (minAdm-ab)/codim_k on the deep strata (does the slack always
    dominate the deficit, so the LOWER bound survives even when the equality fails?).
Q3. Is proving rlct_x >= (minAdm-ab)/2 natively (via the resolution, no Aoyagi) strictly easier than the open
    equality conjecture, or are they equivalent in difficulty? In particular, on a chart is rlct_chart >=
    C_chart/2 equivalent to the equality (via the cap rlct<=codim/2), or does the weaker target (minAdm-ab)/2
    < C_chart/2 give genuine room a native argument can exploit?
Q4. The 2-layer (matrix product FE) case is Morse-Bott at every fiber point (no entanglement, deficits
    impossible) -- entanglement needs >=3 layers. Confirm/deny, and identify the mechanism that first
    produces a possible deficit at 3 layers.

GROUNDING: real RLCT over R; Frobenius-squared losses; codim = composite-rank (parameter-space) codim, not
determinantal. Give exact rationals; if you invoke a Newton polyhedron, state the vertices and the diagonal
piercing point. Mark [FACT] vs [INFERENCE].
</task>

<output_contract>
- A decisive [NATIVE / NEEDS-AOYAGI / DEPENDS] verdict on the boxed lower-bound question.
- For Q1: an explicit DLN deficit point (widths + point + transverse Newton polyhedron + rlct) OR a proof
  that the multilinear structure forbids deficits.
- For Q2: the worst deficit ratio and whether the slack absorbs it (native lower bound survives?).
- End with: the cleanest native sufficient condition for rlct_x >= (minAdm-ab)/2, and whether it covers ALL
  in-scope points or leaves a residual that genuinely needs Aoyagi.
- Do NOT assume benign because Aoyagi's global theorem exists; the question is whether the NATIVE resolution
  gives the LOWER bound without citing it.
</output_contract>
