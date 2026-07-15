import itertools
from functools import lru_cache
@lru_cache(maxsize=None)
def minAdm(M):
    if len(M)==2: return M[0]*M[1]
    M0,M1=M[0],M[1]
    return min((M0-t)*(M1-t)+minAdm((t,)+M[2:]) for t in range(0,min(M0,M1)+1))
def tstars(M):
    M0,M1=M[0],M[1]
    vals=[((M0-t)*(M1-t)+minAdm((t,)+M[2:]),t) for t in range(0,min(M0,M1)+1)]
    m=min(v for v,_ in vals); return set(t for v,t in vals if v==m)
def deepTailMin(M): return min(M[2:])
def tailMinWidth(M): return min(M[1:])
def Mlast(M): return M[-1]

# EXACT deeperFlag_shell_le hyps: ht1(t>=1), ht(t<=min(M0,M1)), hj(j<=r), hnd(widths>=1),
#   hpiv: minAdm(redChain u M) <= u*tailMinWidth(M)
#   hcvg: (M0-u)+(M1-u) <= min(M1,Mlast)-j
#   hrange: min(M1,Mlast)-j <= M2
# check: b>deepTailMin ? (FACT fails). Split by arity, strict-shell, binding.
def redChain(u,M): return (u,)+M[2:]
for maxw,arities in [(6,[3]),(6,[4]),(6,[5]),(5,[6]),(5,[3,4,5,6])]:
    total=0; fails=0; fail_binding=0; fail_strict=0; samples=[]
    for arity in arities:
        for M in itertools.product(range(1,maxw+1),repeat=arity):
            M0,M1=M[0],M[1]
            rho=deepTailMin(M); ml=Mlast(M); tmw=tailMinWidth(M)
            for t in range(1,min(M0,M1)+1):            # ht1, ht
                r=min(M0-t,M1-t)
                for j in range(0,r+1):                  # hj: j<=r
                    u=t+j; a=M0-u; b=M1-u
                    if a<0 or b<0: continue
                    # hpiv
                    if not (minAdm(redChain(u,M)) <= u*tmw): continue
                    # hcvg
                    if not (a+b <= min(M1,ml)-j): continue
                    # hrange
                    if not (min(M1,ml)-j <= M[2]): continue
                    total+=1
                    if b>rho:
                        fails+=1
                        strict = (1<=j<r)
                        binding = (t in tstars(M))
                        if strict: fail_strict+=1
                        if binding: fail_binding+=1
                        if len(samples)<6: samples.append((M,t,j,u,a,b,rho,strict,binding))
    lbl=",".join(map(str,arities))
    print(f"arity {lbl} widths 1..{maxw}: {total} cuts satisfying hcvg^hrange^hpiv; b>deepTailMin FAILS: {fails} (strict-shell:{fail_strict}, binding-cut:{fail_binding})")
    for s in samples:
        M,t,j,u,a,b,rho,strict,binding=s
        print(f"    M={M} t={t} j={j} u={u} a={a} b={b} deepTailMin={rho} strict={strict} binding={binding} tstar={sorted(tstars(M))}")
