"""
Exhaustive check: over ALL binding cuts (arity-3 chains, widths 2..8, u=t*+j, 1<=j<r),
does  min_{l,s} C_{l,s}/2 == T1_q  (= T1 - ab/2)  and  is the minimiser s == t* ?
C_{l,s}=u*b + M0*l + (M0-s)(u-l-s) + s*(d-l),  d=M2-b.
Scope filter a+b<=M2 (hcvg/hmM).  Report any failure.
"""
import itertools
def minAdm3(M0,M1,M2):
    vals=[(s,(M0-s)*(M1-s)+s*M2) for s in range(0,min(M0,M1)+1)]
    m=min(v for _,v in vals); args=[s for s,v in vals if v==m]
    return m,args
def Cmin(M0,M1,M2,u):
    a=M0-u; b=M1-u; d=M2-b
    best=None
    for l in range(0,u+1):
        for s in range(0,M0+1):
            if u-l-s<0 or d-l<0: continue
            C=u*b+M0*l+(M0-s)*(u-l-s)+s*(d-l)
            if best is None or C<best[0]: best=(C,l,s)
    return best

fails=[]; scope_skips=0; checked=0; s_mismatch=[]
W=range(2,9)
for M0,M1,M2 in itertools.product(W,W,W):
    m,tstars=minAdm3(M0,M1,M2)
    T1=m/2
    r_of=lambda t: min(M0-t,M1-t)
    for tstar in tstars:
        r=r_of(tstar)
        for j in range(1,r):           # 1<=j<r
            u=tstar+j
            a=M0-u; b=M1-u
            if a<0 or b<0: continue
            if a+b> M2:                 # SCOPE hcvg/hmM
                scope_skips+=1; continue
            T1q=T1-a*b/2
            Cm,l,s=Cmin(M0,M1,M2,u)
            checked+=1
            if abs(Cm/2 - T1q)>1e-9:
                fails.append((M0,M1,M2,tstar,j,u,Cm/2,T1q))
            if s!=tstar:
                s_mismatch.append((M0,M1,M2,tstar,j,u,s))

print(f"checked (in-scope binding cuts, widths 2..8): {checked}   scope-skipped(a+b>M2): {scope_skips}")
print(f"min C_ls/2 == T1_q failures: {len(fails)}")
for f in fails[:20]: print("   FAIL",f)
print(f"minimiser s != t* count: {len(s_mismatch)}")
for f in s_mismatch[:20]: print("   s!=t*:",f)
# also verify T1q <= comparator uM2/2 always (needed for domination)
bad=[]
for M0,M1,M2 in itertools.product(W,W,W):
    m,tstars=minAdm3(M0,M1,M2); T1=m/2
    for tstar in tstars:
        r=min(M0-tstar,M1-tstar)
        for j in range(1,r):
            u=tstar+j; a=M0-u;b=M1-u
            if a<0 or b<0 or a+b>M2: continue
            T1q=T1-a*b/2; comp=u*M2/2
            if T1q>comp+1e-9: bad.append((M0,M1,M2,u,T1q,comp))
print(f"T1_q <= comparator uM2/2 violations: {len(bad)}")
for f in bad[:10]: print("   ",f)
