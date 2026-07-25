<task>
Deep linear network (DLN) singularity resolution, Aoyagi-style. Setting: real matrices
C1 (3x3), C2 (3x4), product X = C1*C2 (3x4), Frobenius loss L = ||X||^2 = sum_{i,j} X[i,j]^2.
Deepest point: origin (all entries 0). We resolve L near 0 by a fan of blow-up charts to
lower-bound the real log-canonical threshold (RLCT): goal rlct(L) >= 1/2 * minAdm = 4.

A "born chart" is g_p = (block blow-up at pivot p in a center Z) composed with a fixed
unipotent block-shear (Schur block-elimination). A block blow-up at pivot p sends
w_p |-> w_p, and each other center coord w_j |-> w_p*w_j, spectators fixed. So after g_p,
the pivot coordinate is the surviving radial and the loss pulls back to
L o g_p = (monomial_p)^2 * R_p, where monomial_p is a product of the blow-up radials and
R_p is the residual.

Established facts (verified by exact algebra + Groebner in prior probes, over Q):
1. For a chart whose blow-up monomial is a MATCHED product term of a surviving product-entry
   X[i,j] (e.g. blow up the pivot PAIR (C1[0,1], C2[1,0]) which is one of the two additive
   terms of X[0,0] = C1[0,0]C2[0,0] + C1[0,1]C2[1,0]), the residual R_p satisfies R_p(0)=1
   (a "kept-survivor" constant term). Then L o g_p = monomial_p^2 * R_p with R_p(0) != 0:
   the "sandwich".
2. For a MISMATCHED pivot (e.g. blow up C1[0,1], C2[0,0] which is NOT a single term of any
   X[i,j]), R_p(0) = 0: the sandwich FAILS. Such charts are not fan members; the region they
   would cover is a comparable-monomial locus handled by a deeper blow-up (recursion).
3. A fan indexed by "which input radial is blown up, keeping a fixed survivor entry" covers
   0% of the {survivor entry ~ 0} tube. A fan indexed by "which product-entry X[i,j] survives"
   (the survivor-ENTRY fan, one member per generator of the residual ideal) covers 100% of a
   neighborhood up to the null hole {X = 0} (codim >= 2).
4. The single canonical chart (blow up the (C1[0,0],C2[0,0]) diagonal pivot, standard shear)
   carries the full two-sided ideal identity <X o g> = <b1> (single monomial) on nbhd = univ.

The Lean assets: a per-node up-to-null cover atom is proven abstractly over a finite index set
of generators gen : iota -> E -> R, with per-chart hypothesis
  hchart_a : survivorRegion(gen,a) ∩ box ⊆ chart_a '' dom_a   (each a independent),
plus hole-nullity. Separately a step constructor emits, per pivot p in a center Z, one born
chart g_p, each independently carrying its own Jacobian/injectivity certificate (never a
transported one). A RETIRED architecture tried to build sibling charts by TRANSPORTING one
valid chart's certificate through a loss-isometry / coordinate-permutation gauge orbit
(sibling A's certificate = sigma-image of sibling B's); it WALLED because the transport group
was disjoint from the cover-set on node pivots and a valid gauge co-permutes the adjacent
layer (moving an ancestor pivot).

<output_contract>
Answer these, each with a one-word verdict then <=4 sentences of exact-algebra reasoning:

Q1. To discharge, for each born chart, BOTH (a) "covers its survivor region" and (b) the
    sandwich L o g_p = monomial_p^2 * R_p with R_p(0) != 0 — is anything MORE than
    (per-chart block-blow-up surjectivity onto its region) + (the kept-survivor constant term
    R_p(0)=1, from the chart's OWN monomial being a matched product term of a survivor entry)
    required? In particular, is a separate loss-isometry/matched-pairing STRUCTURE needed
    beyond the fact that each chart's monomial is a product term of one survivor generator?

Q2. Can each born chart's (a)+(b) be discharged from THAT pivot's own construction alone, or
    does discharging chart A's clause ever REQUIRE reading a sibling chart B's certificate
    (i.e. sibling A = gauge-orbit image of sibling B)? Distinguish (i) using the loss-isometry
    group merely to ENUMERATE which pivots/generators index the fan, from (ii) deriving one
    sibling's cover/sandwich certificate as the sigma-image of another's.

Q3. Does the cover conjunct (a) and the sandwich/ideal conjunct (b) for a given born chart
    live on the SAME chart/region, or would they force different regions?

Q4. Sharpest failure mode: name the ONE thing that, if the build reached for it, would
    re-introduce the retired inter-sibling gauge-orbit transport. Is it avoidable by the
    born-per-pivot construction (blow up the matched pivot pair directly, sandwich from its
    own monomial)?
</output_contract>

<grounding_rules>
Reason from the exact algebra of block blow-ups and the sum-of-squares residual. Keep
INFERENCE separate from what is FORCED by the algebra. Do not propose Lean code. If a claim
depends on generality beyond the (3,3,4) instance, say so.
</grounding_rules>
