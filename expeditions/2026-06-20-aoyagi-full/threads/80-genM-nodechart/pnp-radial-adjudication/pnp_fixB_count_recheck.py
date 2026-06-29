import sympy as sp
# RECHECK the count with active = {pivot} ∪ {leaf}. det D(radialAffine) = u^{#active - 1}.
# At (2,2,2): leaf = 2 coords. #active = 1+2 = 3 = minAdm. det = u^2 = u^{minAdm-1}. ✓
# But minAdm = E-free + leaf? At (2,2,2): E-block 1x1 with (0,0) FIXED -> E-free=0. leaf=2. minAdm=3?? 
#   minAdm(2,2,2)=3. E-free(=r1*c1 - 1 fixed) = 1*1-1 = 0. leaf = t1*M2 = 1*2 = 2. So minAdm-1 = 0+2 = 2.
#   But minAdm=3, minAdm-1=2. And #active-1 = (1+2)-1 = 2 = minAdm-1. ✓ CONSISTENT.
# So: #active = 1(pivot) + leaf_slots, and we need #active-1 = minAdm-1, i.e. leaf_slots = minAdm-1??
#   At (2,2,2): leaf=2, minAdm-1=2. ✓.  But what about the E-free coords? They're NOT blown up (they're 
#   in B, multiplicatively? NO -- E-free coords are FREE readE coords scaled by u in the chart: u*E_free!).
# WAIT. At (2,2,2) the E-block is 1x1 and its ONLY entry is the FIXED 1. So E-free=0. The leaf carries all
# minAdm-1 = 2 actives. But at (3,3,3): E-block is 2x2, (0,0) fixed, so E-free = 3 coords -- and those are
# u-scaled (u*E_free in the chart). Are they radial actives (blown up) or in B?
# Let me check (3,3,3): the u-scaled coords are E-free (3) + leaf. Do E-free coords get blown up too?
print("(2,2,2): E-block 1x1, (0,0) fixed => E-free=0. ALL minAdm-1=2 actives are LEAF coords.")
print("  => active={pivot}∪{leaf}, the E(0,0) fixed-1 absorbed into B additively. CLEAN at (2,2,2).")
print()
print("(3,3,3): E-block 2x2, (0,0) fixed => E-free=3 coords (u-scaled in chart). These ALSO need blowing up?")
print("  minAdm(3,3,3)=7, minAdm-1=6. leaf = t1*M2 = 1*3 = 3. E-free = r1*c1-1 = 2*2-1 = 3. 3+3=6=minAdm-1. ✓")
print("  => at (3,3,3) the actives = E-free(3) + leaf(3), and the E-free are MULTIPLICATIVE (u*E_i, blown up),")
print("     ONLY the E(0,0) is the additive fixed-1 absorbed into B. MUST verify at (3,3,3).")
