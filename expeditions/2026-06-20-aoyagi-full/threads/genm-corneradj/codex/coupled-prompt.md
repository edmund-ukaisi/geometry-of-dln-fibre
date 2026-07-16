<task>
Two exact real-analysis / RLCT convergence questions about a COUPLED integral. Derive from first
principles (codimension of the zero-locus of the loss, transverse vanishing order, and how a positive
additive term regularizes). Exact algebra decides; numerics only guide.

SETUP. Fixed integers a,b >= 1, and a fixed real matrix Zf (M2 x n) of rank rho. Boxes are cubes
[-1,1]. frobSq(X) = sum of squares of entries.

QUESTION A (the coupled inner integral, "edge" case a+b = rho+1). Concrete: a=b=2, rho=3, Zf a
generic 3x3 rank-3 matrix, Ccross a generic 2x3 matrix, w>0 a scalar. Define
    H(w) = int_{A_cor in [-1,1]^{2x3}} int_{Gamma in [-1,1]^{2x2}}
             ( w + frobSq( Ccross + Gamma * (A_cor * Zf) ) )^{-c'}  dGamma dA_cor.
(Here A_cor is 2x3, Gamma is 2x2, A_cor*Zf is 2x3, Gamma*(A_cor*Zf) is 2x3.)
(i) Is H(w) finite for each fixed w>0? (ii) As w -> 0+, find the exponent beta with H(w) ~ w^{-beta}
(up to constants/logs), for c' in a range around 3.5-4.5. Give beta exactly via the codimension kappa
of the locus N = { (Gamma, A_cor) : Ccross + Gamma*A_cor*Zf = 0 } inside the 10-dim (Gamma,A_cor) space
(4 + 6 dims), i.e. beta = c' - kappa/2 if N is smooth and c' > kappa/2. Compute kappa: is the map
Phi(Gamma,A_cor) = Gamma*A_cor*Zf a submersion onto the 2x3 = 6-dim target at generic points of N?
Watch the subtlety: for FIXED A_cor, the equation Gamma*(A_cor*Zf) = -Ccross is solvable in Gamma ONLY
if the rows of Ccross lie in rowspace(A_cor*Zf) (a 2-dim subspace of R^3) — so the w-blowup is confined
to a sub-locus of A_cor-space; quantify its codimension and add it to the Gamma-reduction ab/2.

QUESTION B (does an additive positive term rescue a divergent "front charge"). Separately, the
"front charge" Ch = int_{A_cor in [-1,1]^{2x3}} det((A_cor*Zf)(A_cor*Zf)^T)^{-a/2} dA_cor is known to
DIVERGE at a=b=2, rho=3 (logarithmically). The coupled H(w) above replaces det(...)^{-a/2} implicitly
by a Gamma-integral WITH the additive w and the additive cross-term Ccross. Question: do the additive
terms (w>0 from a pivot energy, and the residual dist(Ccross, rowspace(A_cor*Zf))^2 from the cross term)
CAP the front-charge singularity so that H(w) stays finite (and scales as a clean power w^{-beta})
EVEN THOUGH Ch = +infinity? Name the mechanism precisely. Is the reduction (c' - beta) at least 1
(which would lift a baseline threshold of 3.5 to >= 4.5)? Is it exactly ab/2 = 2, or more?
</task>

<output_contract>
1. Q-A(i): H(w) finite for w>0? one line + reason.
2. Q-A(ii): kappa (codim of N) with the submersion check; beta = c' - kappa/2; the split
   (Gamma-reduction ab/2 = 2) + (A_cor-sublocus codim ν)/2. State beta numerically for c'=4.0, 4.49.
   Check: is det((A_cor Zf)(A_cor Zf)^T) bounded away from 0 on the relevant sublocus {rows Ccross in
   rowspace(A_cor Zf)} (i.e. is A_cor Zf full rank b there)?
3. Q-B: finite (rescue) or +infinity; the exact regularizer(s) named; reduction (c'-beta) vs 1 and vs 2.
4. Flag each statement as exact derivation vs heuristic/genericity assumption.
Tight. A 3-line transverse-model sketch is fine.
</output_contract>

<grounding_rules>
Do not assume my conclusion; I am withholding it. Derive independently. If a genericity/density-
boundedness assumption is used, say so and state what would make it rigorous. Distinguish the fixed-w
question from the w->0 scaling. Be careful: a positive additive term inside (w + frobSq(...))^{-c'} can
only HELP (bound the base below), never hurt; the question is the exact exponent it yields.
</grounding_rules>
