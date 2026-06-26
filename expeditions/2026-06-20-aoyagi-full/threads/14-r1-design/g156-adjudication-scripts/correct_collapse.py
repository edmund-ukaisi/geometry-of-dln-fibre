print("="*78)
print("CORRECT general-M box-collapse: how does K=core's box-integ close?")
print("="*78)
print("""
K = core ≍ Phi = sum_j Erow_j^2 + ||S·Bred||^2  near the deepest point (PROVEN squeeze, b->0).
The squeeze is LOCAL (near b=0).  Over the FULL ratio box Vz, K and Phi need not be comparable
everywhere -- the squeeze constants degrade as b grows.  So the box-integ of K over Vz is NOT
simply the box-integ of Phi.

TWO sub-questions for the general box-collapse of K over Vz:
 (Q-near) near the deepest point: K ≍ Phi = sum Erow^2 + ||S Bred||^2; integ governed by the Erow
          Morse block (clean, n/2) + the CHILD ||S Bred||^2 box-integ.
 (Q-far)  away from the deepest point but still in Vz∩{K=0}: K's other singular strata.

The ORDERING that the collapse needs: for every w in Vz, c' < rlctAtOn(K, w), given c' < rlctAtOn(K, 0).
i.e. rlctAtOn(K, 0) <= rlctAtOn(K, w) for all w in Vz.  Is 0 the min-rlct point of K over Vz?

K = ||Ahat·B||^2, Ahat=[[1,u],[v,W]] unit pivot.  {K=0} = {Ahat·B = 0}.  Since Ahat has a UNIT
pivot (rank >= 1 always), Ahat is NEVER zero.  So {Ahat B=0} requires B in the right-kernel of Ahat.
The deepest point of K is (u,v,W,B)=0: there Ahat=[[1,0],[0,0]] (rank 1), B=0.  K's singularity at 0
is governed by the Erow Morse + child.  At a FAR point w in Vz∩{K=0} (Ahat full unit-pivot, B in ker):
the local rlct -- is it >= rlct(K,0)?
""")
# Test: is 0 the min-rlct point of K over the box? K's deepest = (all ratios 0, B=0). 
# Compare to a far point: u,v,W generic small (in box), B in ker(Ahat).
# At the far point, Ahat is rank min(m,k) generically (unit pivot + generic off-diag), so {Ahat B=0}
# forces B in a SMALLER kernel => FEWER free B directions vanishing => the loss is LESS degenerate in B
# but the Ahat directions are regular (Ahat != 0). Net: the far point has FEWER vanishing directions.
print("STRUCTURAL: at 0, Ahat is rank-1 (only the unit pivot), so {Ahat B=0} kills a LARGE B-kernel")
print(" (k-1 of k rows of B free to vanish) AND the (u,v,W) are all at their most degenerate.")
print(" At a far point (Ahat higher rank), {Ahat B=0} kills a SMALLER B-kernel => fewer vanishing")
print(" dirs => LARGER local rlct.  So 0 is plausibly the min-rlct point of K over Vz too.")
print()
print("BUT this is NOT the proven deepest_le (K not homogeneous).  It is a SEPARATE ordering claim")
print("for K.  HONEST STATUS: this K-ordering over Vz is the REAL general-M open piece -- it is")
print("structural + small-case, NOT closed.  My earlier 'homogeneity ray' shortcut was WRONG.")
print()
print("THE CLEAN WAY OUT (recursion, not direct K-ordering): the GE leg does NOT need K's ordering")
print("directly. chart_pullback's hKint = IntegrableOn |K|^{-c'} Vz is discharged by the INNER squeeze")
print("K ≍ Phi over Vz (if the squeeze holds on the WHOLE box, not just near 0) + Phi's box-integ.")
print("Phi = sum Erow^2 (Morse, clean) + ||S Bred||^2 (CHILD). ||S Bred||^2 box-integ = the CHILD's")
print("hKint at the next level => RECURSION. The recursion bottoms at the leaf (monomial, explicit).")
print("=> the load-bearing general-M question is: does the squeeze K ≍ Phi hold over the WHOLE Vz")
print("   (uniform constants on the box), or only near 0?  If only near 0, the far strata need the")
print("   K-ordering (the open structural piece). THAT is the precise consult question for deriv-finish.")
