import sympy as sp
# THE HEART: is the (2,2,2) tree's codim sequence = the Mval's of the rank-descent path?
# (2,2,2) r=0: ranks descend 2 (=M_0) -> 1 -> 0 (the achiever path t=(1,0): rank after layer1 =1, after layer2=0).
# Wait — t=(t_1,...,t_L) are the partial-product ranks. For (2,2,2), L=2: t=(t_1,t_2), t_2=0.
# Achiever t=(1,0): rank(C1)=... no, t_1 = rank(C1) on the prefix? t_1=rank after 1 layer.
# The CHART resolves by blowing up rank defects. step-1 (A-pivot, card 4) and step-2 (card 3).
#
# Let me reconcile the CARDS (4,3) with the Mval's. (2,2,2): Mval(2,0)=4, Mval(1,0)=3, Mval(0,0)=4.
# step-1 card 4 = blow up the A-block (4 coords {a00,a01,a10,a11}). Is 4 = Mval of some stratum? Mval(2,0)=4 and Mval(0,0)=4.
# step-2 card 3 = blow up the resolved-form vertex {E,F0,δ} (3 coords). 3 = Mval(1,0)=3 (the achiever).
# So the BINDING divisor (codim 3 = step-2) = Mval(1,0) = minAdm. ✓
# The step-1 codim 4: this is the FIRST blow-up (full A-block), codim = M_0·M_1/... = 4 = the generic-stratum Mval(0,0)? 
# Mval(0,0)=4 (t_1=0: the whole product is 0 via rank-0, block (M0)(M1)=2·2=4... wait (M0-0)(M1-0)+(t1-t2)(M2-t2)= 2·2 + 0 = 4). Yes.
print("(2,2,2) tree codims vs Mval strata:")
print("  step-1 A-pivot: card 4. Mval(t=(0,0))=4 [the rank-0/full-collapse stratum].")
print("  step-2 pivot:   card 3. Mval(t=(1,0))=3 [the rank-1 incidence = ACHIEVER, minAdm].")
print("  binding = min(4,3) = 3 = minAdm Mval ✓. The step-2 divisor IS the achiever's binding center.")
print()
print("RECIPE READING: the dispatcher resolves the rank pattern by ITERATED rank-defect blow-ups;")
print("each node's codim = the geometric codim (= Mval(T), the C1-condition) of the rank stratum it")
print("crosses. The path codims trace a rank-descent t_root -> ... -> 0; the MIN codim on the achiever")
print("path = minAdm Mval. ALL paths have min-codim >= minAdm (C≥); the achiever reaches = minAdm (C=∃).")
print()
# CONFOUND CHECK: is the step-1 card (4) really a Mval, or just the ambient block dim (could be a coincidence)?
# The C1-condition (#138) is the load-bearing claim: codim read = GEOMETRIC codim of the strict transform
# stratum, = Mval. The Jacobian-rank/Hessian-rank reading would be WRONG (the (4,3,2) thin-product trap).
# For (2,2,2) step-1: the A-block blow-up center {a00=a01=a10=a11=0} has codim 4 in the 8-dim space — but
# is that the right "codim" for the divisor's (k,h)? The divisor's ratio is card/2 = 4/2 = 2 (h=3,k=1: ratio (h+1)/2k=4/2=2). 
print("CONFOUND (the C1-condition): the divisor's codim for (k,h) must be the GEOMETRIC codim (=Mval),")
print("NOT raw Jacobian rank. (2,2,2) step-1: ratio (h+1)/(2k)=(3+1)/2=2=card/2=4/2 ✓ (card=geometric codim).")
print("step-2: (h+1)/2k=(2+1)/2=3/2=card/2=3/2 ✓. So card=codim, ratio=card/2, consistent w/ Mval reading.")
print("The (4,3,2) trap (#138): there raw-Jacobian ≠ geometric codim; the recipe MUST use geometric codim=Mval.")
