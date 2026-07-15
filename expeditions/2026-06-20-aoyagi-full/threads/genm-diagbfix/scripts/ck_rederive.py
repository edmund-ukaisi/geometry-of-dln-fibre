# Independent re-derivation of deepgate's deep-stratum codim-with-charge gate:
#   C_k = min( u*rho , u*(rho-k) + kappa_k - gamma_{rho-k} )  >=  minAdm(M) - a*b  =  2*T1_q
# for every binding strict-shell cut, every deep rank-drop k.  Exact NAT arithmetic.
from itertools import product
from functools import lru_cache

def minAdmRec(M):
    M = tuple(M)
    if len(M) == 2:
        return M[0]*M[1]
    # minAdmRec cons: min over cut t of t*M[1] + ... ; use the QIP def via layer split
    # Use the Adm/Mval recursion: minAdm = min over "trusted spine" T.  Simplest: DP over cuts.
    # minAdmRec(M) = min_{0<=t<=min(M0,M1)} (M0-t)(M1-t) + minAdmRec((t,M2,...))   with leaf = M0*M1
    n=len(M)
    best=None
    for t in range(0, min(M[0],M[1])+1):
        red=(t,)+tuple(M[2:])
        val=(M[0]-t)*(M[1]-t)+minAdmRec(red)
        best=val if best is None else min(best,val)
    return best

@lru_cache(maxsize=None)
def CR(widths, s):
    # composite-rank-locus codim: codim of {rank(prod widths) <= s}
    widths=tuple(widths)
    if len(widths)==2:
        v0,v1=widths
        return max(0,(v0-s))*max(0,(v1-s))
    # stratify by rank of last layer = r
    vlast=widths[-1]; vprev=widths[-2]
    best=None
    for r in range(0, min(vprev,vlast)+1):
        inner = 0 if r<=s else CR(widths[:-2]+(r,), s)
        val=(vprev-r)*(vlast-r)+inner
        best=val if best is None else min(best,val)
    return best

def gamma(a,b,s):
    # gamma_s = max_{max(0,b-s)<=h<=b} h*(a+b-s-h)
    lo=max(0,b-s)
    return max((h*(a+b-s-h) for h in range(lo,b+1)), default=0)

def deepTailMin(M):
    return min(M[2:])  # min(M2,...,M_last)

def tstar(M):
    # argmin cut for the FIRST peel (the binding t*): the t minimizing (M0-t)(M1-t)+minAdmRec((t,M2..))
    best=None; arg=None
    for t in range(0,min(M[0],M[1])+1):
        red=(t,)+tuple(M[2:])
        val=(M[0]-t)*(M[1]-t)+minAdmRec(red)
        if best is None or val<best:
            best=val; arg=t
    return arg

violations=0; tight=0; checked=0
worst_slack=99
for arity in (4,5,6):
    for M in product(range(1,7),repeat=arity):
        # good branch: weakly reasonable; require deepTailMin>=1 etc. Use all; skip degenerate
        mm=minAdmRec(M)
        rho=deepTailMin(M)
        n=M[-1]
        ts=tstar(M)
        r=min(M[0]-ts,M[1]-ts)
        for j in range(1,r):            # strict shell 1<=j<r
            u=ts+j
            a=M[0]-u; b=M[1]-u
            if a<1 or b<1: continue
            # binding strict-shell scope: rankgen a+b<=rho-1
            if a+b>rho-1: continue
            target=mm-a*b
            for k in range(1,rho+1):
                s=rho-k
                kappa=CR(tuple(M[2:]),s)
                g=gamma(a,b,s)
                Ck=min(u*rho, u*(rho-k)+kappa-g)
                checked+=1
                slack=Ck-target
                worst_slack=min(worst_slack,slack)
                if Ck<target:
                    violations+=1
                    if violations<=5: print("VIOL",M,"u",u,"k",k,"Ck",Ck,"target",target)
                if slack==0: tight+=1
print(f"arities 4-6, widths 1..6: checked={checked}  violations={violations}  tight(slack=0)={tight}  worst_slack={worst_slack}")
# spotlight uniform (4,4,4,4)@u=3
M=(4,4,4,4); u=3; a=b=1; rho=4; mm=minAdmRec(M); target=mm-1
print(f"\n(4,4,4,4)@u=3: minAdm={mm} target(2T1_q)={target} uRho={u*rho}")
for k in range(1,5):
    s=rho-k; print(f"  k={k} s={s}: kappa={CR((4,4),s)} gamma={gamma(1,1,s)} Ck={min(u*rho,u*(rho-k)+CR((4,4),s)-gamma(1,1,s))}")
