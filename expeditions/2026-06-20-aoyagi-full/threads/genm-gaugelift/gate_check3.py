import itertools
from functools import lru_cache

@lru_cache(maxsize=None)
def minAdm(M):
    M=tuple(M); n=len(M)
    if n==1: return 0
    if n==2: return M[0]*M[1]
    return min((M[0]-t)*(M[1]-t)+minAdm((t,)+M[2:]) for t in range(0,min(M[0],M[1])+1))

def clsCodim(M0,M1,M2,u,l,s):
    # exactly the Lean def, reading only M0,M1,M2 (arity-3 head), nat subtraction
    def sub(a,b): return max(a-b,0)
    return u*sub(M1,u) + M0*l + sub(M0,s)*sub(sub(u,l),s) + s*sub(sub(M2,sub(M1,u)),l)

def deepTailMin(M):  # min(M2,...,M_last)  (indices >=2)
    return min(M[2:])

# Full gate: for every general-L chain, every cut u<=min(M0,M1), every feasible (l,s)
#  (s<=u, l+s<=u, (M1-u)+l<=M2),  check  minAdm(M) <= clsCodim + ab  (ab=(M0-u)(M1-u)).
# Also check the two-step banked reduction numerically:
#   minAdm(M) <= (M0-s)(M1-s)+minAdm(redChain s M)   [banked at s]
#   minAdm(redChain s M) <= s*deepTailMin(M) <= s*M2  [banked tailmin + deepTailMin<=M2]
gate_fail=0; step1_fail=0; step2_fail=0; dtm_fail=0
# also: identity clsCodim + ab == (M0-s)(M1-s)+s*M2  (Fin3 ring, must hold with nat-sub under feasibility)
id_fail=0
checked=0
for arity in (3,4,5):
    for M in itertools.product(range(1,7), repeat=arity):
        M=tuple(M); mm=minAdm(M); M0,M1,M2=M[0],M[1],M[2]
        dtm=deepTailMin(M)
        if dtm>M2: dtm_fail+=1
        for u in range(0,min(M0,M1)+1):
            a=M0-u; b=M1-u; ab=a*b
            for l in range(0,u+1):
                for s in range(0,u+1):
                    if l+s>u: continue
                    if (M1-u)+l>M2: continue
                    C=clsCodim(M0,M1,M2,u,l,s)
                    checked+=1
                    # identity
                    if C+ab != (M0-s)*(M1-s)+s*M2: id_fail+=1
                    # gate
                    if mm > C+ab: gate_fail+=1
                    # step1 banked-at-s
                    red=(s,)+M[2:]
                    if mm > (M0-s)*(M1-s)+minAdm(red): step1_fail+=1
                    # step2 minAdm(red) <= s*deepTailMin <= s*M2
                    if minAdm(red) > s*dtm: step2_fail+=1
print(f"checked feasible (M,u,l,s) strata: {checked}")
print(f"identity  clsCodim+ab == (M0-s)(M1-s)+s*M2   fails: {id_fail}")
print(f"GATE      minAdm(M) <= clsCodim + ab          fails: {gate_fail}")
print(f"step1     minAdm(M) <= (M0-s)(M1-s)+minAdm(red s)  fails: {step1_fail}")
print(f"step2     minAdm(red s) <= s*deepTailMin(M)   fails: {step2_fail}")
print(f"deepTailMin(M) <= M2                          fails: {dtm_fail}")
