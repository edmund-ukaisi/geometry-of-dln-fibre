# Hypothesis: per-layer codim term_j = r_j * c_j where r_j = t^{j-1} - t^j, c_j = M_j - t^j.
# But Mval term is (t^{j-1}-t^j)(M_{j.succ} - t^j). In 0-indexed M (M_0..M_L), M_{j.succ} for the j-th exponent
# (j=1..L) is M_j (the width AFTER the j-th matrix... let me match the Lean: Mval = sum_j (tPrev - T_j)(M_{j.succ} - T_j),
# j:Fin L (0-indexed 0..L-1), M_{j.succ} = M_{j+1}. T_j = t^{j+1} (the (j+1)-th exponent). tPrev_0 = M_0.
# So term at Lean-index j (0-indexed): (t^{(j)} - t^{(j+1)}) * (M_{j+1} - t^{(j+1)}) with t^{(0)}=M_0.
# Let me just recompute with the EXACT Lean indexing and propose r,c.
def terms_rc(M, T):
    # T: Aoyagi exponents t^1..t^L (1-indexed), but stored as tuple index 0..L-1 = t^1..t^L
    L=len(T)
    out=[]
    for j in range(L):  # Lean j:Fin L, 0-indexed
        tprev = M[0] if j==0 else T[j-1]   # t^{(j)} with t^0=M_0; T[j-1]=t^j
        tj = T[j]                          # t^{(j+1)}
        Mnext = M[j+1]                     # M_{j.succ}
        r = tprev - tj      # rows dropped at this boundary
        c = Mnext - tj      # residual cols
        out.append((r,c,r*c))
    return out

for M,Ts in [((4,4,2,2),[(4,2,0)]),((3,3,4),[(1,0)]),((2,2,1),[(1,0),(2,0)]),((2,2,2),[(1,0)])]:
    for T in Ts:
        rc=terms_rc(M,T)
        print(f"M={M}, T={T}: (r_j,c_j,r*c) = {rc}, sum r*c = {sum(x[2] for x in rc)}")
