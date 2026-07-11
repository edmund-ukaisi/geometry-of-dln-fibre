<task>
Assess a proposed geometric RECURSION lemma about deep-linear-network zero-product loci: is it TRUE in
general (with a clean recursion argument), or is there a width where it FAILS? Reason in exact algebra.
Self-contained.

SETUP. Chain M=(M0,M1,...,ML) of positive integers. The layer-peel minimum
  minAdm(M)=min_{0<=t<=min(M0,M1)}[(M0-t)(M1-t)+minAdm(redChain(t,M))],
  redChain(t,M)=(t,M2,...,ML), base minAdm(a)=0, minAdm(a,b)=a*b.
A binding cut t* achieves minAdm(M)=peelCharge(t*)+minAdm(redChain(t*,M)), peelCharge=(M0-t*)(M1-t*)=a*b.
minAdm(M) = codim of the zero-product locus (Aoyagi/Lehalleur-Rimanyi); it has theta top-dimensional
components (theta the paper's component count).

The product is Qtil = A1 * Zdeep, A1 is M1 x M2, Zdeep = A2*...*A_L is the SHARED M2 x ML deeper product.
Cut t*: A1 splits into A1_piv (t* rows) and A1_cor (b rows). Corank rows q_1..q_b = rows of A1_cor * Zdeep
(they SHARE Zdeep with the pivot rows). Reduced chain redChain=(t*,M2,...,ML): its zero-product locus
Z_red has codim minAdm(redChain), theta_red top-dim components; its product involves A1_piv and Zdeep.

THE PROPOSED LEMMA (transversality recursion).
 (i) Each TOP-DIMENSIONAL component of Z_red (codim = minAdm(redChain)) is a "pivot-side" degeneration:
     the reduced FRONT block vanishes (rank-drops minimally) while the SHARED deeper product Zdeep is
     GENERIC (full rank, min(M2,ML)). It is NOT a Zdeep-rank-drop stratum.
 (ii) Consequently, on each such top-dim component, the CURRENT corank rows q_1..q_b = A1_cor*Zdeep
     (A1_cor free, Zdeep generic full-rank) are GENERIC UNITS: the corank block has full row rank b there,
     so the collapsing direction H1=|q1+s q2| (etc.) does not vanish (valuation p=0).
 (iii) The strata where Zdeep DOES rank-drop (forcing corank rows to vanish, p>0) are STRICTLY HIGHER
     codim than minAdm(redChain), hence NON-critical for the reduced RLCT.
 (iv) This PROPAGATES: the reduced front-block-vanishing condition is itself resolved by the SAME peel
     applied to redChain (arity drops by 1 each level), whose top-dim components are (by the lemma one
     level down) redChain-pivot-side with the redChain-deeper generic; terminating at the arity-2 base
     (a free block). So p=0 holds at EVERY peel level of the recursion.

ANCHOR I VERIFIED (take as a data point, do not just trust): M=(3,3,3,4), binding t*=1, redChain=(1,3,4),
minAdm(redChain)=3. The reduced product is A1_piv (1 x 3, the single pivot row) times Zdeep (3 x 4). The
locus {A1_piv * Zdeep = 0}: MAIN component {A1_piv=0, Zdeep generic rank 3} has codim 3 = minAdm(1,3,4);
there Zdeep is injective, so the corank rows A1_cor*Zdeep (A1_cor 2x3 free) are generic units (p=0). The
co-vanishing stratum {rank Zdeep <= 2 with A1_piv in its left-kernel} has codim 4 > 3 (non-critical).

WHAT TO ASSESS.
 Q1. Is (i) TRUE in general — is the minAdm(redChain)-achieving degeneration always pivot-side
     (front-block-vanish, Zdeep generic), never a Zdeep-rank-drop? Give the general codim argument, OR a
     width where the minAdm achiever REQUIRES Zdeep to rank-drop (which would force p>0 = an obstruction).
     Consider narrow vs wide pivots (t* small vs large) and contracting vs expanding layers (M2<ML etc.).
 Q2. Does the theta-multiplicity break it? If Z_red has several top-dim components, must the corank rows
     be units on ALL of them (p=0 on every critical divisor), or can one component be a Zdeep-rank-drop
     (p>0)? 
 Q3. Does (iv) recurse cleanly (arity descent, terminating at the base), and is the base case (arity 2,
     free block) consistent with p=0?
 Q4. State the CLEANEST sufficient geometric condition on M under which the lemma holds at all levels
     (e.g. a monotonicity / width condition), and whether the DLN chains of interest satisfy it.
</task>

<output_contract>
For Q1-Q4: a one-word verdict (TRUE / FALSE / CONDITIONAL / UNPROVEN) then the derivation. Mark bullets
[DERIVED]/[INFERRED]/[ASSUMED]. If FALSE or CONDITIONAL, give the explicit failing width or the exact
extra hypothesis needed. End with: the cleanest lemma statement you would certify, and the single cheapest
computation that would confirm or break the general claim.
</output_contract>

<grounding_rules>
Do not assume the lemma is true; try to break it with a specific width (narrow vs wide pivot, contracting
layers, high theta). Distinguish a genuine failure (an achiever that forces Zdeep rank-drop -> p>0) from a
labour gap. Use exact codim computations (rank-variety codims (m-r)(n-r); the QIP minAdm). Do not paste code.
</grounding_rules>
