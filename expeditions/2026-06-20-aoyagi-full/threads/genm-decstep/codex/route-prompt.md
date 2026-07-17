<task>
A resolution-of-singularities / RLCT bookkeeping question: does a layer-peel recursion close with the
PLAIN (unweighted) box-finiteness induction hypothesis, or must it carry a negative-power weight as a
decoration? Deep-linear-network Frobenius loss.

SETUP. Square chain (n,n,n,n): P, Z0, W independent n x n matrices in [-1,1]. Goal: prove the box integral
I(c) = ∫ frobSq(P Z0 W)^{-c} dP dZ0 dW < ∞ for c < c* = (1/2)minAdm(n,n,n,n) (c*=3 for n=3, 11/2 for n=4),
by INDUCTION ON CHAIN ARITY. minAdm(M) = min_t [(M0-t)(M1-t) + minAdm(t,M2,...)] (2-width leaf M0*M1).

ONE PEEL. Cover {P} by the dominant-t*×t* invertible-minor charts. On a chart, Schur-weld the pivot; the
loss becomes freedSchurLoss = frobSq(P·Q̃ₚ) + frobSq(C·Q̃ₚ + Γ·Q_b), where the c×c corank block Γ is FREE
(c=n-t*), Q_b (c×q) is the corank tail, both built from the deeper layer variables. Equivalently
freedSchurLoss = frobSq(F·Q), F=[[P,0],[C,Γ]] block-lower-triangular (P invertible), Q=[Q̃ₚ;Q_b] the tail.

TWO CANDIDATE ROUTES to reduce this peel to a shorter chain redChain(t',M)=(t', n, n) (one arity lower):

ROUTE-D (domain blow-up + PLAIN IH). Stratify the JOINT rank of the deeper factor K=A_cor·Zf (the corank
tail as a product) by rank(K)=r. Blow up each rank-r determinantal stratum (a proper birational CoV; the
exceptional divisor contributes a POSITIVE-power monomial Jacobian |det J|, which is BOUNDED on the box).
Attribute the rank drop to the corank matrix so the deep tail stays FRESH (untouched), and reduce stratum
r to the PLAIN box integral of the fresh chain redChain(u+(b-r), M) at the shifted exponent
c - peelCharge(u+(b-r))/2. The reduction is closed by the PLAIN box-finiteness IH RMBTF(redChain) (i.e.
∫ frobSq(prod(redChain))^{-c''} < ∞, NO weight). The min over strata of [peelCharge(u') +
minAdm(redChain u' M)] = minAdm(M) EXACTLY (verified). Claim: no residual negative weight survives — the
blow-up Jacobian is positive/bounded, and the fresh reduced chain's OWN singularity is deferred to its own
arity recursion. (Arity induction, NOT length induction — no decoration compounds across levels.)

ROUTE-DEC (integrate Γ first → NEGATIVE Gram weight → DECORATED IH). Integrate the free corank block Γ
FIRST. On {Q_b full rank} this yields det(Q_bQ_bᵀ)^{-a/2} (a=c) — a NEGATIVE-power Gram weight on the
deeper tail — times the reduced loss at c-ab/2. This weight blows up on {rank Q_b < c}; the plain box-IH
has "no budget" for it (Hölder-splitting it loses: the product pushforward density near a corank-2 point is
~dist^{-1} on codim 4, ∉ L^4). So one carries the weight as a DECORATION and uses a weighted/decorated IH.

  Q1. Are ROUTE-D and ROUTE-DEC both sound, and do they reach the SAME threshold c*? Or does one of them
      have a genuine gap? Specifically: in ROUTE-D, is the claim correct that blowing up the determinantal
      stratum leaves only a POSITIVE-power (bounded) Jacobian and reduces to the PLAIN box integral of a
      FRESH shorter chain — with NO residual negative-power weight — so that the plain box-finiteness IH
      closes it? Or does a negative-power weight necessarily survive the domain blow-up (making the plain
      IH insufficient and the decoration unavoidable)?

  Q2. The apparent paradox: ROUTE-DEC's "integrate Γ first" produces a negative Gram weight that the plain
      IH cannot absorb (real: ρ∉L^4). ROUTE-D's "blow up the domain first" claims the plain IH suffices.
      Reconcile: is the difference merely the ORDER of operations (resolve the singularity BEFORE
      integrating the transverse block, vs integrate first and inherit a weight) — so ROUTE-D genuinely
      avoids the weight — or is there a substantive obstruction that makes the plain IH fail regardless of
      order?

  Q3. If ROUTE-D is sound (plain IH suffices via the determinantal domain blow-up), is the DECORATED
      machinery (carrying the resolution normal form through the recursion) UNNECESSARY for this problem —
      i.e. is arity-induction with the plain box-finiteness IH + per-peel determinantal blow-up a complete
      route? Or is there a reason (e.g. the blow-up CoV cannot be organized as a clean per-peel reduction
      to a fresh chain, forcing the accumulated normal form / decoration)?

  Q4. Net: which route is the sound + simpler proof organization, and is the decoration necessary or
      avoidable? If ROUTE-D avoids it, state the one genuinely-new analytic atom ROUTE-D still needs.
</task>

<output_contract>
Answer Q1-Q4 in order, short paragraphs. For each, flag PROVEN (standard resolution-of-singularities /
determinantal-integral fact you can state) vs INFERENCE. The crux is Q1/Q2: the SIGN and role of the
blow-up Jacobian, and whether resolving the domain before integrating the transverse block genuinely
avoids the negative Gram weight. State the standard fact you use about the Jacobian of a determinantal
(rank-stratum) blow-up and whether the resolved integrand is a clean monomial×unit. End with a one-line
verdict: PLAIN-IH-SUFFICES (decoration avoidable) / DECORATION-NECESSARY / BOTH-SOUND-SAME-THRESHOLD.
I have deliberately withheld my own tentative verdict; do not assume it.
</output_contract>

<grounding_rules>
Distinguish the exact-arithmetic budget (min over strata = minAdm, given) from the analytic claim about
whether the blow-up leaves a positive vs negative weight. The load-bearing question is the SIGN/boundedness
of the determinantal-stratum blow-up Jacobian and whether "resolve before integrating" avoids the Gram
weight. State precisely the resolution fact (e.g. for the generic determinantal variety {rank ≤ r}, the
blow-up / Grassmannian-bundle resolution has Jacobian = exceptional divisor to a POSITIVE power). Do not
paste Lean or long code.
</grounding_rules>
