<task>
You are stress-testing an ARCHITECTURE decision for a Lean formalisation (Lehalleur–Rimanyi DLN geometry).
I need an independent judgement; I am WITHHOLDING my leaning. WITHHOLD nothing about the math.

CONTEXT (exact objects).
A "chain" is a width vector M = (M0,...,M_last). "prod M A" is the product of layer matrices (A_i is
M_i x M_{i+1}); frobSq = sum of squared entries. Target (proved by strong induction on #layers, given the
"plain IH" hIH = RouteMBoxThresholdFinite of every SHORTER chain):
  RouteMBoxThresholdFinite(M):  for c' < minAdm(M)/2,  INT_{A in box} frobSq(prod M A)^(-c') < inf.
minAdm recursion:  minAdm(M) = min_{t in 0..min(M0,M1)} (M0-t)(M1-t) + minAdm(redChain t M),
  redChain t M = (t, M2, ..., M_last)  (collapses the FIRST TWO widths into one width-t layer).
Cut-soundness (proved): minAdm(M) <= (M0-t)(M1-t) + minAdm(redChain t M).

We reached this design point (all PROVEN by an exact-integer census + a prior decorrelated review):
- The d>=2 corank cut is CITED (Aoyagi product-corank). The d = min(M0-t,M1-t) <= 1 cut is NATIVE.
- The NATIVE d<=1 arm funnels, after handling the (rank<=1) corank block, to ONE object: the boxed
  two-matrix product reduction of the FRONT. Concretely, the pivot-energy term is
     frobSq(P*Qtil) = frobSq(X*Q),  X = [P|B12] (t x M1, P invertible => full row rank t),  Q = A1*Zdeep,
  A1 = first tail layer (M1 x M2), Zdeep = prod(M2,...,M_last).  The reduction recombines (X, A1) |-> W = X*A1
  (a t x M2 matrix), collapsing (t, M1, M2) -> (t, M2), i.e. reducing to redChain t M = (t, M2, ...),
  handled by hIH.  The two WINGS are the special cases:
     a=0 wide  (M0<=M1, t=M0): front X = [P|B12] is M0 x M1 (WIDE, full row rank M0), corank EMPTY.
     b=0 tall  (M1<=M0, t=M1): front [P;C] is M0 x M1 (TALL, full col rank M1), corank EMPTY.
  Both recombine (front)*(A1) -> M0 x M2, reducing to (M0, M2, ...).
- The pushforward density rho(W) of (X,A1)|->W=X*A1 is SINGULAR at rank-drops of W (order A>0 in general).
- KNOWN (proved earlier this session): the naive POINTWISE fold rho(W) <= K*frobSq(W*Zdeep)^(-A/2) is UNSOUND
  (rho blows up at a rank-deficient W0 while ||W0*Zdeep|| stays nonzero for generic deep Zdeep). So the
  reduction must use a determinantal RANK-SECTOR blow-up of {rank W = r}, NOT the fold.
- KNOWN (exact-integer, 0 fails): min_{s} [ (M0-s)(M1-s) + minAdm(redChain s M) ] = minAdm(M).  Each rank
  stratum r of W maps to a deepened cut s and reduces to redChain s M with charge (M0-s)(M1-s)/2.
- KNOWN: the d<=1 incidence is SINGLE-FACTOR native (P invertible => rank X = t always => the d>=2 joint
  product-corank tubes {rank X = s<t} are EMPTY); so this is NOT the Aoyagi cite.

BANKED Lean atoms available: gammaAtom (INT_Gamma (w+frobSq(Gamma R + S))^-c' = det(RR^T)^-p/2 * Cresid *
(w+frobSq(S(I-P_R)))^-(c'-pq/2), R full row rank, w>0, c'>pq/2); qbox (INT over a FREE box of b rows in R^q
of det(gram Q)^(-a/2) < inf iff b<=q and a<q-b+1); corner_block (INT_sphere g^-c' < inf for g deg-2-homog
bounded-below-on-sphere, c'<N/2 — incl. the "corner sum" of two blocks sharing a deep factor, threshold
(N1+N2)/2); scaledRadialEuclid (INT_{R^a}(w+||x||^2)^-p, a<2p); sumSqND box radial; plus the plain hIH.

The ARCHITECTURE decision: two options to close the native d<=1 arm.
  (OPT-STANDALONE) Build the front RANK-SECTOR reduction as a STANDALONE atom whose per-stratum blow-up
     produces a MONOMIAL Jacobian |det J| (the stratum codim) times a PLAIN reduced-chain integral
     (redChain s M), closed by PLAIN hIH.  No Gram-weight ever rides on the reduced box; no decorated IH.
  (OPT-DECORATED) Introduce a mild "Gram-decorated RouteMBoxThresholdFinite" IH (carry a qbox/gammaAtom-family
     Gram weight det(leadingGram)^(-w) through the recursion) and prove a decorated peel.  More moving parts;
     the operator prefers to AVOID decorations unless necessary.

===================================================================================================
Q1 (the wings — is OPT-STANDALONE achievable?).  For a=0 wide and b=0 tall (corank EMPTY), does the
determinantal rank-sector blow-up of {rank(X*A1) = r} genuinely produce, per stratum, a MONOMIAL Jacobian
times a PLAIN reduced-chain integral over redChain s M (closed by plain hIH) — i.e. NO residual Gram weight
survives onto the reduced box?  Or does the blow-up of a PRODUCT X*A1 (X and A1 both boxed, the singular
locus is a determinantal variety of a product) leave a residual determinant/Gram weight that plain hIH
cannot absorb?  Distinguish the wide (X full row rank, submersive) and tall (front injective) cases.

Q2 (the d=1 a>=u corank-one dressing — does it force OPT-DECORATED?).  For d=1 (corank block rank <=1, say
b=1 so Q_b is one row) with a >= u: dropping the transverse term diverges, so one keeps it and integrates the
coupling block C (a x u).  Integrating C via gammaAtom leaves the PIVOT-GRAM det(Qtil Qtil^T)^(-a/2), Qtil =
W*Zdeep a PRODUCT (t x q).  QUESTION: is there a route that disposes this pivot-Gram WITHOUT a decorated IH —
e.g. (i) does it COMBINE with the front rank-sector's own monomial Jacobian (cancel/merge, so the net is a
plain reduced integral), or (ii) can it be disposed by a qbox on the LAST FREE layer A_last (Qtil = D*A_last,
D full row rank; INT_{A_last box} det(D A_last A_last^T D^T)^(-a/2) * [loss] via a qbox-with-extra-loss)?  Or
(iii) is the pivot-Gram genuinely non-absorbable, forcing OPT-DECORATED for the a>=u corank-one cut?

Q3 (exact statement).  Write the MINIMAL Lean-friendly statement of the standalone front-rank-sector atom (if
OPT-STANDALONE is viable), with exact widths and the reduction to hIH.  State it as a finiteness
(INT ... < inf).  Name which banked atoms it consumes and which NEW sub-lemmas it needs (the per-stratum
determinantal blow-up CoV, its Jacobian identity, the sound sector replacement for the fold, the
min-over-strata sum).

===================================================================================================
For EACH: PROVEN / ARGUED / GUESS, and a one-line RECOMMENDATION between OPT-STANDALONE and OPT-DECORATED.
If OPT-STANDALONE works for the wings but OPT-DECORATED is forced for d=1 a>=u, say so precisely (that is a
possible mixed outcome). End with the single cheapest computation that would settle Q2.
</task>

<output_contract>
  Three sections Q1, Q2, Q3. Terse. For Q1/Q2 give PROVEN/ARGUED/GUESS + the recommendation tag
  {OPT-STANDALONE, OPT-DECORATED} for that arm. Q3: the exact statement (widths, integrand, threshold,
  reduction target) + a bulleted list of consumed-banked vs new-sub-lemmas. End with the cheapest
  discriminating computation for Q2. Be concrete about dims, charges, Jacobians. No hedging prose.
</output_contract>

<grounding_rules>
  Reason from the exact objects. The pointwise fold is UNSOUND (do not resurrect it). "det(product-Gram) on
  the reduced box" is absorbable by plain hIH ONLY if it provably cancels/merges into a monomial Jacobian or
  disposes at a free layer via qbox; otherwise it forces a decorated IH. A blow-up produces a plain reduced
  integral ONLY if its exceptional Jacobian is a pure monomial with no leftover determinant of a product.
  State inference vs fact; do not rubber-stamp OPT-STANDALONE if a Gram weight genuinely survives.
</grounding_rules>
