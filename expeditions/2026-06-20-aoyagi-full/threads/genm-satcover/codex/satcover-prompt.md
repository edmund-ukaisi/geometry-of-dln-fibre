<task>
I am adjudicating a COVERAGE question in a Lean-formalisation of an RLCT (real-log-canonical-threshold)
finiteness proof for the singular integrals of deep linear networks. The proof is an induction over the
number of layers of a matrix chain. I want you to argue, from exact algebra, which of three outcomes is
correct. WITHHOLD nothing; argue whichever way the algebra points. Do not assume I have a preferred answer.

SETUP (all exact / combinatorial; no floats needed).

- A chain of widths M = (M0, M1, M2, ..., M_L), L+1 layers (>= 3 widths). A "cut" at value u peels the
  first two widths into a single reduced layer:  redChain(u, M) = (u, M2, M3, ..., M_L)  (ONE fewer layer).
- minAdm(M) is the Aoyagi minimal-codim, computed by the layer-peel recursion:
      minAdm(M) = min over t in 0..min(M0,M1) of [ (M0-t)(M1-t) + minAdm(redChain(t,M)) ],
  base cases: 1-width -> 0, 2-width -> M0*M1.  The target threshold is T1 = minAdm(M)/2.
- The binding cut is u = t* + j, where t* = argmin above and j is a "shell index" ranging over 0..r,
  r = min(M0 - t*, M1 - t*). Define a = M0 - u, b = M1 - u, and peelCharge(M,u) = (M0-u)(M1-u) = a*b.
- For a shell at cut u, the "per-shell spine integrand" G(shell) must be shown finite for T1's exponent
  range c' < T1. Two mechanisms exist in the codebase:

  (1) INCIDENCE RESOLUTION ("Brick D"), used for STRICT shells 1 <= j < r. The object after a head-split is
        G = INT_z INT_{Qb} det(Qb Qb^T)^{-a/2} * [ INT_{front P,B,C} ( ||[P|B]·hsQ||^2 + ||C·Qp·(I-Pi_b)||^2 )^{-q} ]
      with q = c' - ab/2. Here Qp = prod(redChain(u,M))·z is u x M2 (the reduced product), Qb = A_cor is a
      FREE b x M2 corank block, hsQ = (Qp ; Qb), Pi_b = projection onto row(Qb), and C has 'a' rows
      (the "transverse Schur"). The resolution blows up along "incidence" strata rank(W) = l, W = Qp·N
      (N spans ker Qb), with normal codimensions
        C_{l,s} = u*b + M0*l + (M0-s)(u-l-s) + s*(M2-b-l),   which algebraically equals  (M0-s)(M1-s)+s*M2 - a*b.
      It requires a scope hypothesis a+b <= M2 (else the corank-Gram det(Qb Qb^T)^{-a/2} integral diverges),
      and it bounds  G(shell) <= C * comparator(redChain(u,M)).integral(c' - peelCharge/2)  with C < infinity.
      The comparator on redChain(u,M) is finite for c' < minAdm(redChain(u,M))/2, closed by the induction
      hypothesis at the lower arity.

  (2) A "SUBSET" bound (j-agnostic):  G(shell) <= (undecorated full-chain box at level M).  This is finite iff
      the level-M box is finite. At the leaf (3 widths) the level-M box finiteness is a banked base case
      (unconditional). For L >= 1 the level-M box finiteness is the SAME analytic gap as the induction's own
      goal, so this bound is CIRCULAR for the induction (it bounds a piece of the level-M object by the
      level-M object itself).

THE SATURATED SHELL j = r. Here u = t* + r = min(M0, M1), so exactly one of a = M0-u, b = M1-u is 0
(min(a,b) = 0, ab = 0, peelCharge = 0). I verified by exhaustive integer sweep (arities 3-5, widths 1-6):
at j=r ALWAYS min(a,b)=0 and peelCharge=0 (0 exceptions in 2925 saturated cuts); and peelCharge=0 forces
minAdm(M) <= minAdm(redChain(u,M)) (0 exceptions) so the reduced-chain threshold >= T1.

Consequences of ab = 0 on mechanism (1):
- If b = 0 (M1 <= M0): the corank block Qb has ZERO rows -> no minor chart, det(Qb Qb^T) is the empty 0x0
  determinant = 1 (no divisor), Pi_b = 0 so I - Pi_b = I, and the incidence coordinate W = Qp·N collapses
  to W = Qp (N = identity). The output shear H = P·U + B·D that decouples the pivot block is vacuous
  (B in R^{M0 x 0}).
- If a = 0 (M0 <= M1): the 'a' transverse-Schur C-rows vanish, and det(Qb Qb^T)^{-a/2} = det^0 = 1 (unit).
- The incidence-scope hyp a+b <= M2 is NOT guaranteed at j=r: on my sweep it FAILS for 631 of 2925 saturated
  cuts (e.g. M=(2,1,2): a+b = 1 but the codebase's coverage bound min(M1, M_last) - r = 0).

QUESTION. Which is correct, and why (exact algebra)?

  (A) Mechanism (1) COVERS j = r: its statement/proof specialises validly to ab = 0, so the saturated shell
      is just the ab=0 instance of the incidence resolution, needing no separate lemma.
  (B) j = r needs a SEPARATE reduction (distinct from mechanism (1)): the incidence blow-up has nothing to
      resolve when a block vanishes, so the saturated shell is bounded directly (drop the empty corank
      energy; a single pivot-radial blow-up onto the reduced product) and closed by the SAME lower-arity
      induction hypothesis on redChain(u,M) at the UNSHIFTED exponent c' (peelCharge=0). Specify the exact
      reduced-chain bound this needs.
  (C) j = r is a BASE-LIKE case needing NO descent: the subset bound (2) suffices non-circularly because at
      j=r the shell object already IS the terminal/reduced object.

Sub-question, decisive: at ab = 0 does the incidence chart retain BOTH blocks (pivot Q_p AND corank Q_b),
or does one block structurally vanish, and does that vanishing make the incidence blow-up (the rank(W)=l
stratification and the det-Gram) vacuous / content-free?
</task>

<output_contract>
1. VERDICT: (A), (B), or (C). One line.
2. The decisive exact-algebra reason (the block-vanishing analysis at ab=0; whether the rank(W)=l blow-up and
   det-Gram have any content when a=0 or b=0).
3. If (B): write the exact reduced-chain bound the saturated shell needs (LHS, RHS comparator on which chain,
   which exponent, which induction hypothesis closes it), and say explicitly whether it is the SAME lemma as
   mechanism (1) or a genuinely separate one.
4. Whether the subset bound (2) can substitute at j=r for L >= 1 (circularity check).
5. Anything I have mis-stated.
Be terse. Exact algebra over prose.
</output_contract>

<grounding_rules>
- Integer/exact reasoning only; no numerics needed.
- Treat "the level-M box finiteness for L>=1 is the induction's own goal" as given (it is a code fact).
- Do not defer to me; if the algebra contradicts one of my framing statements, say so.
</grounding_rules>
