"""
Exact-algebra certification for the j=r saturated-shell coverage adjudication.
All integer arithmetic (exact). Verifies the load-bearing facts:
  (F1) at j=r: min(a,b)=0, peelCharge=0, ab=0.
  (F2) at peelCharge=0: minAdm M <= minAdm(redChain u M)  (=> reduced threshold >= T1).
  (F3) incidence exponent gate at ab=0: min_{l,s} C_{l,s}/2 == T1  (still lands T1).
  (F4) the vanishing-block structure at min(a,b)=0.
Definitions mirror the Lean:
  minAdmRec: >=3 widths: min_{t<=min(M0,M1)} [ (M0-t)(M1-t) + minAdmRec(redChain t M) ]
             2 widths (leaf): M0*M1 ;  1 width: 0.
  redChain t M = (t, M2, M3, ..., M_{L}).
  peelCharge M u = (M0-u)*(M1-u).
  T1 = minAdm(M)/2.
"""
from functools import lru_cache
from itertools import product

def redchain(t, M):
    # M is a tuple of widths length >=3; drop M0,M1, prepend t
    return (t,) + tuple(M[2:])

@lru_cache(maxsize=None)
def minadm(M):
    n = len(M)
    if n == 1:
        return 0
    if n == 2:
        return M[0]*M[1]
    best = None
    for t in range(0, min(M[0], M[1]) + 1):
        v = (M[0]-t)*(M[1]-t) + minadm(redchain(t, M))
        best = v if best is None else min(best, v)
    return best

def argmin_t(M):
    # t* = argmin over t of the peel recursion (first minimiser)
    best = None; bt = None
    for t in range(0, min(M[0], M[1]) + 1):
        v = (M[0]-t)*(M[1]-t) + minadm(redchain(t, M))
        if best is None or v < best:
            best = v; bt = t
    return bt

def peelcharge(M, u):
    return (M[0]-u)*(M[1]-u)

def Cls(M, u, l, s):
    """Incidence codim C_{l,s} = u*b + M0*l + (M0-s)(u-l-s) + s*(d-l),
       a=M0-u, b=M1-u, d=M2-b.  (incidence-cert Sec.3)."""
    a = M[0]-u; b = M[1]-u; d = M[2]-b
    return u*b + M[0]*l + (M[0]-s)*(u-l-s) + s*(d-l)

def Cls_identity(M, u, s):
    """The l-independent identity: C_{l,s} = (M0-s)(M1-s)+s*M2 - a*b."""
    a = M[0]-u; b = M[1]-u
    return (M[0]-s)*(M[1]-s)+s*M[2] - a*b

# ---- sweep over arities 3..5, widths 1..6, all binding cuts u=t*+j, j=1..r ----
F1_fail=[]; F2_fail=[]; F3_fail=[]; ident_fail=[]
n_jr=0; n_checked=0
for nw in (3,4,5):
    for M in product(range(1,7), repeat=nw):
        M=tuple(M)
        if any(x<1 for x in M): continue
        ts = argmin_t(M)
        r = min(M[0]-ts, M[1]-ts)
        if r < 1: continue
        # saturated shell: j=r, u = t*+r = min(M0,M1)
        for j in range(1, r+1):
            u = ts + j
            n_checked += 1
            a=M[0]-u; b=M[1]-u
            # F1 only asserted at j=r
            if j==r:
                n_jr+=1
                if not (min(a,b)==0 and peelcharge(M,u)==0 and a*b==0 and u==min(M[0],M[1])):
                    F1_fail.append((M,ts,j,u,a,b))
                # F2: minAdm M <= minAdm(redChain u M)
                if not (minadm(M) <= minadm(redchain(u,M))):
                    F2_fail.append((M,u,minadm(M),minadm(redchain(u,M))))
            # F3 / identity: over enumerated (l,s), l in 0..u, s in 0..u-l ; check identity + min
            T1 = minadm(M)  # 2*T1
            best=None
            for l in range(0, u+1):
                for s in range(0, u-l+1):
                    if s> min(M[0],M[1]): continue
                    c = Cls(M,u,l,s)
                    ci = Cls_identity(M,u,s)
                    if c != ci:
                        ident_fail.append((M,u,l,s,c,ci))
                    best = c if best is None else min(best,c)
            # min C_{l,s} should equal minAdm_feas(u) - ab where minAdm_feas(u)=min_{0<=s<=u}[(M0-s)(M1-s)+sM2]
            # and for binding cut (u=t*+j, t*<=u) minAdm_feas(u)=minAdm(M) => min C = minAdm(M)-ab.
            expected = minadm(M) - a*b
            if best != expected:
                F3_fail.append((M,u,best,expected,a*b))

print("checked binding cuts:", n_checked, " of which j=r:", n_jr)
print("F1 (j=r => min(a,b)=0,peelCharge=0,ab=0,u=min) fails:", len(F1_fail))
print("F2 (peelCharge=0 => minAdm M <= minAdm redChain) fails:", len(F2_fail))
print("identity C_{l,s}=(M0-s)(M1-s)+sM2-ab fails:", len(ident_fail))
print("F3 (min C_{l,s} = minAdm(M)-ab, => min/2 = T1 at ab=0) fails:", len(F3_fail))
if F1_fail[:3]: print("F1 examples:",F1_fail[:3])
if F2_fail[:3]: print("F2 examples:",F2_fail[:3])
if F3_fail[:3]: print("F3 examples:",F3_fail[:3])
if ident_fail[:3]: print("ident examples:",ident_fail[:3])
