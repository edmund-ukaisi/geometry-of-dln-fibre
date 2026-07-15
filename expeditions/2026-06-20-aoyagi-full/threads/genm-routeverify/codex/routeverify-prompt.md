<task>
You are a decorrelated second opinion on a measure-theoretic RLCT-domination proof route. Adjudicate
three sharp questions with EXACT algebra. Argue whichever direction the math supports; do not assume the
route works or fails. Give FACT vs INFERENCE labels.
</task>

<grounding_rules>
Exact algebra only for load-bearing claims. Matrix/frobenius-norm reasoning, singular-value structure,
codimension counts. Numerics only as a guide. If you need a counterexample, construct it explicitly.
</grounding_rules>

<setup>
Fix a "deep linear network" layer-width chain M and a cut u. Relevant blocks (real matrices):
- Q_p  (u x n)      = "pivot rows"  (a fixed function of reduced params z; nonzero a.e.)
- Z     (M2 x n)    = "deep factor"  (fixed, full row rank M2 generically, M2 <= n)
- A_cor (b x M2)    = "corank rows selector", ranges over a box matBox (entries in [-1,1]); b = M1-u
- Q_b  (b x n)      = A_cor * Z      = "corank rows"
- hsQ  ((u+b) x n)  = [ Q_p ; Q_b ]  (stack); note M1 = u+b
- W = [P | B12]     (u x M1)         = a "front block", P is u x u, B12 is u x b
- a = M0 - u,  b = M1 - u.

A radial-polar change of variables ("pivotBlock_radial_blowup") is available as an EXACT identity: for any
Q (M1 x n), any measurable phi,
   integral over W (u x M1) of  phi( frobSq( W * Q ) )
     =  integral over unit-sphere direction Phat, integral over r>0 of  r^(u*M1 - 1) * phi( r^2 * frobSq( Phat * Q ) ).
Here frobSq(X)=sum of squares of entries. Phat is a u x M1 unit-sphere matrix; write Phat = [Phat_p | Phat_b]
(u x u and u x b blocks).

A separately-proven "corank" lemma ("shell_corankOffSector_le_unif") states: for a FIXED SCALAR w>0 (a free
parameter, constant across the A_cor and Gamma integrations), and a1*b/2 < c',
   integral over A_cor in matBox, integral over Gamma of ( w + frobSq( Ccross + Gamma*(A_cor*Z) ) )^(-c')
     <=  Cunif * w^(-(c' - a*b/2)),      Cunif independent of A_cor, w, Ccross.
Crucially w must be a constant (it is a real-number hypothesis, not a function of A_cor).

There is a "minAdm" integer functional on chains with the exact recursion
   minAdm(M) = min over t in [0..min(M0,M1)] of [ (M0-t)(M1-t) + minAdm(redChain t M) ],
where redChain t M = (t, M2, M3, ..., M_last) has ONE FEWER layer than M.
Define carrierThreshold(M) = minAdm(M)/2 and peelCharge = a*b = (M0-u)(M1-u).
</setup>

<questions>
Q1 (composition validity). A proposed proof ("route B") does, in order:
   (i) apply pivotBlock_radial_blowup to the front block W=[P|B12] with Q = hsQ (the FULL stack [Q_p;Q_b]);
   (ii) treat the resulting pivot energy as the scalar "w" of shell_corankOffSector_le_unif and integrate
        out A_cor and Gamma using that lemma.
   Is step (ii) a valid application of shell_corankOffSector_le_unif? Compute the pivot energy produced by
   step (i) explicitly in terms of Phat_p, Phat_b, Q_p, A_cor, Z. Does it depend on A_cor? Is there any
   A_cor-free lower bound  frobSq(Phat*hsQ) >= w0 > 0  that holds uniformly as A_cor ranges over the full
   box (w0 depending only on Phat, Q_p, Z, not on A_cor)? Construct an explicit minimal instance
   (e.g. u=1,b=1,Z=I,n=M2) and determine inf over A_cor of the pivot energy for fixed generic Phat.

Q2 (rank-drop locus). At the A_cor achieving that infimum, what is the rank of hsQ=[Q_p;Q_b]? Relate the
   infimum being 0 to hsQ dropping rank. If one restricts A_cor to the "shell" {sigma_min(hsQ) >= eps>0}
   (excludes rank-drop), is the pivot energy then bounded below uniformly in A_cor? Does that help apply
   shell_corankOffSector_le_unif, whose integration domain is the FULL box (not the shell)?

Q3 (descent vs circularity). A target reduction ("descent") claims: the shell integrand on chain M at cut u
   is  <=  C * ( comparator on redChain u M ).integral( c' - peelCharge/2 ),  where redChain u M has one
   fewer layer. The comparator on redChain u M is finite for exponent < carrierThreshold(redChain u M) =
   minAdm(redChain u M)/2. Question: for c' < carrierThreshold(M), is the reduced comparator's integral at
   exponent (c' - peelCharge/2) finite? i.e. is  c' - a*b/2 < minAdm(redChain u M)/2  guaranteed by
   c' < minAdm(M)/2? Prove or refute using the minAdm recursion. Is this a genuine reduction to a smaller
   chain (an induction that terminates), or is it secretly bounding chain M by minAdm(M)/2 on the SAME chain
   (which would be circular)? Distinguish clearly.
</questions>

<output_contract>
For each of Q1,Q2,Q3: a definitive verdict with the explicit algebra (the pivot-energy formula, the
infimum/lower-bound computation with a concrete instance, the recursion inequality). Label FACT vs
INFERENCE. If route B's composition is invalid, state precisely at which interface and why, and whether any
reordering rescues it. For Q3 state whether the descent is non-circular.
</output_contract>
