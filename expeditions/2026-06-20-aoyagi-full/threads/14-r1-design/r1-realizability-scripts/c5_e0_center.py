import numpy as np
# RECONCILE: my earlier check said e=Cnext·v ≠ 0 generically (0/5000 RANDOM Cnext). pp2 says at the
# CASCADE CENTER (the deepest point), e=0 because the downstream cascade factors annihilate the complement.
# These are NOT contradictory: RANDOM Cnext gives e≠0, but the CASCADE's SPECIFIC downstream is degenerate
# (it's the most-degenerate point). Verify pp2's g222 claim at t=(3,3,2,2,2,0).
#
# Cascade: C_s = diag(1^{t_{s+1}}, 0). t = (3,3,2,2,2,0), t_0=M^1=3. tt = [3,3,3,2,2,2,0].
# The C5 node is the step 3->2. Which layer? t_2=3 -> t_3=2 (node s=3 in 1-indexed, the 3rd layer).
# At node s=3: complement = the dropped direction (the 3rd coord, since t_3=2 keeps coords 1,2).
# Downstream = C_4 C_5 C_6 (the layers after s=3). e = (C_4 C_5 C_6) applied to the complement direction.
tt = [3,3,3,2,2,2,0]   # t_0..t_6
L = 6
# Build cascade factors C_1..C_6 (each diag(1^{t_s}, 0), C_s : determined by t_s = rank after s layers)
# C_s has rank t_s on the running product: C_s = diag(1^{t_s}, 0) as a square matrix (widths all 3 here).
W = 3
Cs = []
for s in range(1, L+1):
    C = np.zeros((W, W))
    for i in range(tt[s]):  # t_s ones
        C[i,i] = 1.0
    Cs.append(C)
# complement at node s=3 (0-indexed layer 2): the direction dropped going t_2=3 -> t_3=2 = coord index 2 (3rd).
complement = np.zeros(W); complement[2] = 1.0   # the 3rd coord (dropped at layer 3)
# downstream = C_4 C_5 C_6 (layers s=4,5,6 = Cs[3],Cs[4],Cs[5]); applied as product to complement.
# product order: the chain is C_6 C_5 ... C_1 (composition); downstream of node 3 = C_6 C_5 C_4.
downstream = Cs[5] @ Cs[4] @ Cs[3]   # C_6 C_5 C_4
e = downstream @ complement
print(f"cascade downstream C_6 C_5 C_4 (t_4,t_5,t_6 = {tt[4]},{tt[5]},{tt[6]}):")
print(f"  C_6=diag(1^{tt[6]},0)=diag(0,0,0) [t_6=0 kills all]")
print(f"  e = (C_6 C_5 C_4)·complement = {e}, ‖e‖² = {np.dot(e,e)}")
print(f"  ⟹ e=0 at the cascade center: {np.allclose(e,0)}  (pp2's g222 claim CONFIRMED)")
print()
print("RECONCILIATION with my earlier 0/5000 (random Cnext gave e≠0):")
print("  Random downstream ⟹ e≠0 generically (TRUE). But the CASCADE's downstream is the MOST DEGENERATE")
print("  point (C_6=diag(0,0,0) since t_6=0) ⟹ e=0 AT THE CASCADE CENTER. Both true: e≠0 on an open")
print("  neighborhood AWAY from the center, e=0 AT the center (the deepest point). My cert's 'e=0 is null'")
print("  was WRONG at the center — the deepest point sits ON e=0. pp2's correction is right.")
print()
print("BUT — does this break termination? pp2's resolution: e=0 = a DEEPER node (recurse on complement).")
print("  At e=0 the complement's downstream vanishes ⟹ a FURTHER rank-defect on the complement sub-chain.")
print("  The complement is a rank-(t_{s-1}-t_s) STRICT sub-block ⟹ ΣM_complement < ΣM_parent ⟹ lex drops.")
print("  So the C5 cover = {e≠0: shear} ∪ {e=0: deeper recursion}, BOTH lex-terminating. #98 CLOSES.")
