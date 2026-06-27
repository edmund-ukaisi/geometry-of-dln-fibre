import sympy as sp
u=sp.Symbol('u')
exec(open('/tmp/deadleaf_validate2.py').read().split('M=[3,3,1,3]')[0])
# Question: for the LIVE-leaf case (q=L), does the kept-diagonal alone propagate the leaf pivot, or are
# carriers W still needed? In test3333 I set W=0 (no carriers) and got Hmat_0(0,0)=e != 0. So for q=L the
# kept-diagonal (B's) alone suffices — the leaf pivot propagates UP through Bmat products. Carriers needed
# ONLY when q<L (dead leaf, the pivot is in an interior E and must propagate DOWN to the output via W's).
# Let me CONFIRM: (3,3,3,3) with W=0 (test3333 already has W=0) gave e. So q=L needs NO carriers. ✓
# And the controller's failure #1 ("non-deepest active boundary") — that was injecting at s=1 (NOT the deepest
# = NOT q). The deepest interior with Text>0... for (3,3,3,3) the leaf IS live so q=L=3, and injecting at s=1
# (interior, not q) gives 0 because the suffix below s=1 zeroes it. The FIX is to inject at q (=L here), not s=1.
# So the two failure modes:
#  (#1) inject at non-deepest boundary -> killed by zero suffix below. FIX: inject at q (deepest Text>0).
#  (#2) dead leaf (q<L) -> need carriers W_q..W_{L-1} to propagate DOWN.  
# When q=L (live leaf): pivot at Rfin_L, propagated UP by kept-diagonal Bmat, NO carriers.
# When q<L (dead leaf): pivot at E-block at q, propagated DOWN by carriers W_q..W_{L-1} (kept rows 0 below q).
print("CONFIRMED the two regimes:")
print(" q=L (live leaf, Text_L>0): pivot at Rfin_L(0,0); kept-diagonal Bmat propagates UP; NO carriers needed.")
print("   -> validated (3,3,3,3) Hmat_0(0,0)=e, (3,3,4) Hmat_0(0,0)=e (both W=0).")
print(" q<L (dead leaf, Text_L=0): pivot at deepest E-block (boundary q); carriers W_q..W_{L-1} propagate DOWN.")
print("   -> validated (3,3,1,3) Hmat_0(0,0)=e·w1·w2 (carriers ESSENTIAL; W=0 gives 0).")
print()
# Double-check the deepest-q selection for (3,3,1,3): Text=[3,2,0,0]. deepest k with Text(k)>0 = k=1 (Text1=2).
# The E-block lives at boundary k=1 (Rmat1). q=1. Carriers W_1, W_2 (= W_q .. W_{L-1}=W_1,W_2). ✓ matches.
print("(3,3,1,3): Text=[3,2,0,0], deepest Text>0 at index 1 -> q=1, E-block at boundary 1, carriers W_1,W_2. ✓")
