import itertools
print("="*78)
print("CLARIFY: what does 'deepest = global-min-rlct' actually mean? T=0 vs minimizer.")
print("="*78)
def admBound(M,j,L):
    return min(M[0],M[1]) if j==0 else M[j+1]
def adm(M):
    L=len(M)-1
    rngs=[range(admBound(M,j,L)+1) for j in range(L)]
    for T in itertools.product(*rngs):
        if all(T[i]>=T[j] for i in range(L) for j in range(L) if i<=j) and (L==0 or T[L-1]==0):
            yield T
def Mval(M,T):
    L=len(M)-1
    tot=0
    for j in range(L):
        tprev = M[0] if j==0 else T[j-1]
        tot += (tprev - T[j])*(M[j+1]-T[j])
    return tot
def minAdm(M): return min(Mval(M,T) for T in adm(M))

print("\nThe CONFUSION deriv-finish flagged, resolved:")
print(" - T is an EXPONENT/rank-profile vector (Aoyagi t^(j)), NOT a parameter point.")
print(" - lambdaCore = 1/2 min_T Mval(M,T) over admissible T.")
print(" - The DEEPEST PARAMETER point (all A_s=0) is ONE point; its local RLCT is NOT Mval(T=0).")
print("   Its RLCT = 1/2 minAdm = the min over the WHOLE admissible cone (Aoyagi resolution:")
print("   the deepest point sits under ALL the blow-up centers; the BINDING divisor is the min-T).")
print()
for M in [[1,1,2],[2,2,1],[2,2,2],[3,3,3],[2,2,4],[3,2,5]]:
    T0 = tuple([0]*(len(M)-1))
    mv0 = Mval(M,T0)
    mA = minAdm(M)
    argmin = [T for T in adm(M) if Mval(M,T)==mA]
    print(f"M={M}: Mval(T=0)={mv0}  minAdm={mA}  argmin profiles={argmin}")
print()
print("=> T=0 (Mval=M0·M1) is the TRIVIAL stratum's codim, the LARGEST top divisor, NOT the min.")
print("   The min-T is the BINDING divisor along the descent. They differ whenever the tail binds.")
print()
print("THE HONEST CLAIM (corrected): the deepest PARAMETER point's RLCT = 1/2 minAdm. This is NOT")
print("'T=0 achieves minAdm' (FALSE). It is the Aoyagi resolution FACT that the all-zero param point's")
print("local rlct equals the FULL minimisation 1/2 min_T Mval. That IS the cited resolution structure.")
print()
print("WHAT global_min NEEDS (the box-collapse), restated to AVOID this trap:")
print(" global_min is about the ORDERING among PARAMETER points p in {prod=0}, NOT exponent vectors:")
print("   forall p, rlctAtOn(F,p) >= rlctAtOn(F, deepest_param_point).")
print(" The deepest PARAM point is the most singular (max simultaneous vanishing) => smallest rlct.")
print(" This ordering does NOT require identifying minAdm with any particular T -- it is a pure")
print(" 'most-degenerate point has smallest rlct' statement, which is exactly what the VALUE-FREE")
print(" deepest_le_of_homogeneous_core proves (homogeneity+lsc), NO Mval/minAdm at all.")
