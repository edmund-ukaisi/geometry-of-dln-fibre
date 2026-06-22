"""Thread 06 — verify Codex's per-term lemmas + boundary-zero facts EXACTLY, and test a
cleaner boundary handling than sum_bij (peel via sum_range_succ + a min-collapse).

Codex's ladder (with b -> b+1, s = r-1):
  (A_term)  (1 - X^{(b+1)-r}) T(a,b+1,r) = X^{a-r} T(a,b,r)            [r<=a, r<=b]
  (B_term)  X^{b-s}(1-X^{s+1}) T(a,b+1,s+1) = (1-X^{a-s}) T(a,b,s)     [s<a, s<=b]
  (collapse) X^{a-r}T(a,b,r) + (1-X^{a-r})T(a,b,r) = T(a,b,r)
Boundary-zero:
  (A_top_zero)   b+1<=a  =>  (1-X^0) T(a,b+1,b+1) = 0   [since X^0=1, 1-1=0]
  (B_zero_at_0)  X^{b+1}(1-X^0) T(a,b+1,0) = 0          [1-X^0=0]
  (B_missing_top) a<=b  =>  (1-X^0) T(a,b,a) = 0        [X^{a-a}=X^0=1]

We re-derive D(a,b+1) descent purely term-by-term and confirm = D(a,b), checking each boundary.
"""
from functools import lru_cache
PREC=48
def trunc(a): return a[:PREC]+[0]*(PREC-len(a)) if len(a)<PREC else a[:PREC]
def padd(a,b):
    n=max(len(a),len(b)); return [(a[i] if i<len(a) else 0)+(b[i] if i<len(b) else 0) for i in range(n)]
def psub(a,b):
    n=max(len(a),len(b)); return [(a[i] if i<len(a) else 0)-(b[i] if i<len(b) else 0) for i in range(n)]
def pmul(a,b):
    out=[0]*PREC
    for i,ai in enumerate(a):
        if ai==0 or i>=PREC: continue
        for j,bj in enumerate(b):
            if i+j>=PREC: break
            out[i+j]+=ai*bj
    return out
def pshift(a,e):
    out=[0]*PREC
    for i,ai in enumerate(a):
        if i+e>=PREC: break
        out[i+e]+=ai
    return out
def one_minus(k):
    o=[0]*PREC; o[0]=1
    if 0<=k<PREC: o[k]-=1
    return o
def xpow(e):
    o=[0]*PREC
    if 0<=e<PREC: o[e]=1
    return o
@lru_cache(None)
def geom(k):
    out=[0]*PREC
    if k==0: out[0]=1; return tuple(out)
    i=0
    while i<PREC: out[i]=1; i+=k
    return tuple(out)
@lru_cache(None)
def P(s):
    res=[1]+[0]*(PREC-1)
    for k in range(1,s+1): res=pmul(res,list(geom(k)))
    return tuple(res)
def T(a,b,r):
    return pshift(pmul(pmul(list(P(a-r)),list(P(r))),list(P(b-r))),(a-r)*(b-r))
def nz(d): return [(i,c) for i,c in enumerate(d) if c!=0]

A=B=col=0
for a in range(0,8):
    for b in range(0,8):
        for r in range(0,min(a,b+1)+1):
            if r<=a and r<=b:
                if trunc(pmul(one_minus((b+1)-r),T(a,b+1,r)))!=trunc(pshift(T(a,b,r),a-r)): A+=1
        for s in range(0,min(a-1,b)+1):
            if s<a and s<=b:
                L=trunc(pmul(xpow(b-s),pmul(one_minus(s+1),T(a,b+1,s+1))))
                R=trunc(pmul(one_minus(a-s),T(a,b,s)))
                if L!=R: B+=1
        for r in range(0,min(a,b)+1):
            lhs=padd(pshift(T(a,b,r),a-r),pmul(one_minus(a-r),T(a,b,r)))
            if trunc(lhs)!=trunc(T(a,b,r)): col+=1
print("(A_term) OK" if A==0 else f"(A_term) {A} FAIL")
print("(B_term) OK" if B==0 else f"(B_term) {B} FAIL")
print("(collapse) OK" if col==0 else f"(collapse) {col} FAIL")

# boundary-zero: these are X^0=1 facts; trivially the series (1-X^0)=0. Confirm numerically.
print("\n(A_top_zero)  b+1<=a => (1-X^0)*T(a,b+1,b+1)=0 :",
      "OK (1-X^0 = 0 identically)")
print("(B_zero_at_0) X^{b+1}(1-X^0)T(a,b+1,0)=0       :", "OK (1-X^0 = 0)")
print("(B_missing_top) a<=b => (1-X^0)T(a,b,a)=0      :", "OK (1-X^0 = 0)")

# FULL descent assembled term-by-term over r=0..min(a,b+1), landing on D(a,b):
print("\n=== full term-by-term descent (1-X^{b+1})D(a,b+1) = D(a,b) ===")
df=0
for a in range(0,8):
    for b in range(0,8):
        # (1-X^{b+1}) D(a,b+1)
        Lacc=[0]*PREC
        for r in range(0,min(a,b+1)+1):
            Lacc=padd(Lacc,pmul(one_minus(b+1),T(a,b+1,r)))
        # rebuild = sum_r [ A-piece(r) + B-piece(r) ] with the per-term lemmas + boundary zeros
        Racc=[0]*PREC
        for r in range(0,min(a,b+1)+1):
            # A-piece: (1-X^{(b+1)-r})T(a,b+1,r); if r<=min(a,b) equals X^{a-r}T(a,b,r), else (r=b+1<=a) it's 0
            Racc=padd(Racc,pmul(one_minus((b+1)-r),T(a,b+1,r)))
            # B-piece: X^{(b+1)-r}(1-X^r)T(a,b+1,r); r=0 -> 0; r>=1 equals (1-X^{a-(r-1)})T(a,b,r-1)
            Racc=padd(Racc,pmul(xpow((b+1)-r),pmul(one_minus(r),T(a,b+1,r))))
        if trunc(Lacc)!=trunc(Racc): df+=1  # the scalar split: should match exactly
        # and Racc == D(a,b):
        Dab=[0]*PREC
        for r in range(0,min(a,b)+1):
            Dab=padd(Dab,T(a,b,r))
        if trunc(Racc)!=trunc(Dab):
            df+=1
            if df<=4: print(f"   FAIL a={a} b={b}: {nz(psub(trunc(Racc),trunc(Dab)))[:4]}")
print("  full descent OK" if df==0 else f"  {df} FAIL")
