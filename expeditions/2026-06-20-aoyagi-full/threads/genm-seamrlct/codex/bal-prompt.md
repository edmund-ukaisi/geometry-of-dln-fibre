<task>
Decide whether a specific hypergraph, arising from deep-linear-network (DLN) RLCT resolution, is always
BALANCED (integer vertex-cover number tau = fractional vertex-cover number tau*). Argue whichever way; give
exact combinatorics. I withhold my leaning.

CONTEXT. K(A)=||L_{p-1}...L_0||_F^2, product of p composable real matrices. Resolving the rank-drop strata by
a telescoping-Schur atlas, on each chart the transverse loss is (up to bounded-factor + nonzero-Jacobian
equivalence)
    K_perp  ~  sum_i u_i^2  +  sum_{S in H} ( prod_{j in S} v_j )^2 ,
a sum of Morse squares plus squared products of transverse blocks. H is the "seam-incidence hypergraph":
vertices = transverse rank-drop blocks (one per PEEL LEVEL, ordered by depth in the linear chain), hyperedges
= the monomials of the resolved loss. The real-log-canonical threshold is
    rlct(K_perp) = (q + tau*(H))/2,     codim = q + tau(H),     deficit = (tau - tau*)/2,
so a DEFICIT below codim/2 occurs iff tau > tau* iff H is NOT balanced. Bipartite / acyclic / balanced H
(Koenig) give tau=tau*, no deficit. The classic non-balanced case is an ODD CYCLE (triangle
v1v2, v2v3, v3v1 has tau=2, tau*=3/2, deficit 1/2).

ESTABLISHED (take as given):
- 2-layer (single matrix product FE): the incidence is BIPARTITE (F-block vertices vs E-block vertices),
  tau=tau*, no deficit. [Morse-Bott at every point of a 2-factor fiber.]
- The telescoping recursion: peeling the last layer at rank r introduces ONE transverse block E; the seam
  term is ||Z_head . F . E||^2 where Z_head = product of DEEPER layers, F = spectator (a piece of the next
  deeper layer). Coupling edges therefore always join the CURRENT peel level to STRICTLY DEEPER levels
  (a partial order by depth). A p-layer chain has p-1 transverse peel levels.
- 3-layer chains: only 2 transverse levels => H is a path (bipartite), always balanced, no deficit.
- The first COMBINATORIALLY possible odd cycle (triangle among 3 mutually-coupled levels) needs >= 4 layers.
- A 3-way "triangle" among the three LAYER perturbations (a,b,c of A,B,C with ABC=0) gives pairwise terms
  abC, aBc, Abc, BUT the middle-layer linear term  b -> A.b.C  (the "sandwich", nonzero whenever A,C != 0)
  supplies a Morse direction that SPLITS OFF b -- so the triangle is obstructed unless rank-deficiency of
  A,C opens a kernel subspace of b on which A.b.C = 0.

THE QUESTION (decide):
  Is the DLN seam-incidence hypergraph H ALWAYS BALANCED (tau=tau*), so the fractional gate q+tau* >=
  minAdm-ab reduces to the already-proven integer gate q+tau >= minAdm-ab and the RLCT lower bound is native?
  OR can a >=4-layer DLN chart realize a genuine ODD CYCLE in H (tau>tau*)? If yes, does the DLN structure
  bound the integrality gap (tau-tau*) by the codim slack (C_chart - (minAdm-ab)), so q+tau* >= minAdm-ab
  still holds?

SUBQUESTIONS:
Q1. In the telescoping incidence, coupling edges join a level to strictly-deeper levels. Does this partial
    order (a DAG / interval structure) force H to be balanced? (Interval hypergraphs and their duals are
    balanced; is the DLN seam incidence an interval hypergraph, or a "laminar"/nested family?) Give the
    precise combinatorial class of H and whether that class is balanced.
Q2. Extend the sandwich obstruction: in a >=4-layer chain, to realize a triangle {E_a,E_b,E_c} (levels
    a<b<c) as LEADING transverse terms, the coupling coefficients (products of the intervening generic
    layers) must vanish. Do these vanishings force extra Morse directions (as in the 3-layer sandwich) that
    destroy the odd cycle, or can staggered rank-deficiencies realize a genuine triangle? Construct the
    smallest explicit DLN chain + fiber point realizing a triangle, or prove none exists.
Q3. If a triangle can form, is the integrality gap (tau-tau*) always <= the codim slack? The deep strata
    have codim ~ growing (kappa_k ~ k^2) while the target minAdm-ab is fixed; but the gap could also grow
    with the number of odd cycles. Bound the WORST gap for a DLN chart and compare to the slack.
Q4. Balanced hypergraphs are exactly those with no "odd hole" in a certain sense (Berge). Is there a clean
    graph/quiver-theoretic reason (type A, equioriented A_n quiver, no oriented cycles) that the DLN seam
    incidence has no odd cycle -- i.e. does the acyclicity of the type-A quiver transfer to balancedness of H?

GROUNDING: real RLCT over R; parameter-space (composite-rank) codim, not determinantal; the corank charge is
coupled but is a bounded factor (does not change H). tau* = LP relaxation of vertex cover = max fractional
matching (LP duality). Mark [FACT] vs [INFERENCE]. Give exact rationals / explicit constructions.
</task>

<output_contract>
- A decisive verdict: [ALWAYS BALANCED / ODD CYCLE POSSIBLE / DEPENDS], with the combinatorial class of H.
- For Q2: an explicit smallest DLN triangle chart (widths + fiber point + the three edges + why no Morse
  direction kills it) OR a proof the sandwich obstruction generalizes (no triangle ever).
- For Q3: the worst integrality gap bound vs slack (does the native fractional gate survive?).
- End with: which of sub-routes (a) balancedness / (b) gap<=slack / (c) triangle-absence is the right native
  closer, and whether any residual genuinely needs cited Aoyagi.
</output_contract>
