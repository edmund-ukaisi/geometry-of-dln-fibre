import itertools
# Verify the load-bearing accounting fact: for the decorated induction I_π(s)<∞ for s<Θ(M,π),
# Θ(M,π)=½(min_{T⪰π} Mval(T) − A(π)), the peel step s<Θ(M,π) ⟹ s−a/2<Θ(M,(π,u)) holds for EVERY
# legal next cut u (not just the binding one). Equivalent to: min_{T⪰(π,u)} Mval(T) ≥ min_{T⪰π} Mval(T).
# Here a partial profile π=(t_1,...,t_k) is weakly-decreasing with t_j ≤ admBound(j); T⪰π means T
# extends π (same first k entries) and is admissible (weakly-decr, t_j≤admBound(j), last=0).
def admBound(M,j): return min(M[0],M[1]) if j==0 else M[j+1]
def Mval(M,T):
    L=len(T); s=0
    for j in range(L):
        tprev=M[0] if j==0 else T[j-1]
        s+=(tprev-T[j])*(M[j+1]-T[j])
    return s
def admissible(M,T):
    L=len(T)
    for j in range(L):
        if T[j]>admBound(M,j): return False
        if j>0 and T[j]>T[j-1]: return False
    return T[L-1]==0
def A_charge(M,pi):
    s=0
    for j in range(len(pi)):
        tprev=M[0] if j==0 else pi[j-1]
        s+=(tprev-pi[j])*(M[j+1]-pi[j])
    return s
def completions_min(M,pi):
    L=len(M)-1
    if len(pi)>L: return None
    best=None
    ranges=[range(admBound(M,j)+1) for j in range(len(pi),L)]
    for tail in itertools.product(*ranges):
        T=tuple(pi)+tail
        if admissible(M,T):
            v=Mval(M,T)
            best=v if best is None else min(best,v)
    return best
bad=0; tot=0
for M in [(3,3,3,3),(3,3,4),(2,2,2,2),(4,4,4,4),(3,3,3,3,3),(2,4,1),(4,4,2,2)]:
    L=len(M)-1
    # enumerate all legal partial profiles π and all legal next cuts u
    def gen_partial(pi):
        yield tuple(pi)
        k=len(pi)
        if k<L:
            ub=min(admBound(M,k), (pi[-1] if pi else admBound(M,0)))
            for u in range(ub+1):
                yield from gen_partial(pi+[u])
    for pi in gen_partial([]):
        k=len(pi)
        if k>=L: continue
        base=completions_min(M,pi)
        if base is None: continue
        ub=min(admBound(M,k), (pi[-1] if pi else admBound(M,0)))
        for u in range(ub+1):
            child=completions_min(M,pi+(u,))
            if child is None: continue
            tot+=1
            # need min_{T⪰(π,u)} ≥ min_{T⪰π}
            if child < base: bad+=1
            # ALSO the exact accounting: A(π,u) = A(π) + charge(u); and Θ child consistent
    print(f"  M={M}: checked partial-profile/next-cut pairs; running bad={bad}/{tot}")
print(f"\n  THRESHOLD MONOTONICITY min_(T⪰π,u) ≥ min_(T⪰π): violations = {bad}/{tot}")
print("  (0 => the decorated induction closes for EVERY chart at EVERY cut, not just the binding branch)")
