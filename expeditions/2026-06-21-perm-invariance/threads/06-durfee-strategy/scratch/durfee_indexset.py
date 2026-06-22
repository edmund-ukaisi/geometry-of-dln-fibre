"""Thread 06 — pin the cleanest INDEX SET for the Lean statement, and the boundary closure.

Question: the sum is over r=0..min(a,b). In Lean this is Finset.Icc 0 (min a b) = Finset.range (min a b + 1).
The descent reindex shifts r and changes min(a,b) -> min(a,b-1). Two boundary regimes:
  (i)  b <= a:  min(a,b)=b, the top term r=b. After descent, min(a,b-1)=b-1; the r=b term must
       contribute ONLY through the 'shift piece' (1-q^{a-r+1})T_{r-1}(b-1), landing at index b-1 (valid).
  (ii) b > a:  min(a,b)=a=min(a,b-1); no top-term loss; cleaner.

We test whether REPLACING the sum range by Finset.range (a+1) [r=0..a, ignoring b] still gives the
RHS when we DEFINE P_{negative}:=0 (so terms with b-r<0 vanish). If so, the Lean statement can fix the
range at 0..a (or 0..min) and let out-of-range terms die — pick the cleaner. Test both conventions.

Convention Z: P_n = 0 for n<0 (so T_r=0 when b-r<0 or a-r<0). Sum r over 0..max(a,b) gives same RHS.
"""
from functools import lru_cache
PREC = 48
def trunc(a): return a[:PREC]+[0]*(PREC-len(a)) if len(a)<PREC else a[:PREC]
def padd(a,b):
    n=max(len(a),len(b)); return [(a[i] if i<len(a) else 0)+(b[i] if i<len(b) else 0) for i in range(n)]
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
@lru_cache(None)
def geom(k):
    out=[0]*PREC
    if k==0: out[0]=1; return tuple(out)
    i=0
    while i<PREC: out[i]=1; i+=k
    return tuple(out)
@lru_cache(None)
def P(s):
    if s<0: return tuple([0]*PREC)   # convention Z
    res=[1]+[0]*(PREC-1)
    for k in range(1,s+1): res=pmul(res,list(geom(k)))
    return tuple(res)
def lhs(a,b): return trunc(pmul(list(P(a)),list(P(b))))

def rhs_min(a,b):
    acc=[0]*PREC
    for r in range(0,min(a,b)+1):
        t=pmul(pmul(list(P(a-r)),list(P(r))),list(P(b-r)))
        acc=padd(acc,pshift(t,(a-r)*(b-r)))
    return trunc(acc)

def rhs_range(a,b,top):
    """sum r=0..top, terms with negative-index P die via convention Z."""
    acc=[0]*PREC
    for r in range(0,top+1):
        if a-r<0 or b-r<0 or r<0:  # exponent (a-r)(b-r) could be positive but P=0 kills term anyway
            continue
        t=pmul(pmul(list(P(a-r)),list(P(r))),list(P(b-r)))
        acc=padd(acc,pshift(t,(a-r)*(b-r)))
    return trunc(acc)

if __name__=="__main__":
    print("=== rhs over r=0..a (convention Z, P_neg=0) == rhs over 0..min ? ===")
    f1=0
    for a in range(9):
        for b in range(9):
            if rhs_range(a,b,a)!=rhs_min(a,b): f1+=1
    print("  range 0..a == min:", "OK" if f1==0 else f"{f1} FAIL")
    print("=== rhs over r=0..max(a,b) == rhs over 0..min ? ===")
    f2=0
    for a in range(9):
        for b in range(9):
            if rhs_range(a,b,max(a,b))!=rhs_min(a,b): f2+=1
    print("  range 0..max == min:", "OK" if f2==0 else f"{f2} FAIL")
    print("=== and both == LHS ===")
    f3=0
    for a in range(9):
        for b in range(9):
            if rhs_min(a,b)!=lhs(a,b): f3+=1
    print("  min-range == LHS:", "OK" if f3==0 else f"{f3} FAIL")
    print("\nNote: with range 0..a, the r=a..? terms beyond min(a,b) auto-vanish iff b-r<0, i.e. r>b.")
    print("So fixing range = 0..min(a,b) (Finset.range (min a b+1)) is the honest minimal index set;")
    print("range 0..a works ONLY because P_{b-r}=0 for r>b -- requires a P_neg=0 convention NOT in the")
    print("M1 API (P : Nat -> series). => Lean statement should use Finset.range (min a b + 1) / Icc.")
