from functools import lru_cache
import itertools, random

# minAdmRec (ground truth)
@lru_cache(maxsize=None)
def minAdmRec(M):
    L=len(M)-1
    if L==0: return 0
    if L==1: return M[0]*M[1]
    return min((M[0]-t)*(M[1]-t)+minAdmRec((t,)+M[2:]) for t in range(min(M[0],M[1])+1))

# ---- The ARITY-PEEL threshold, defined via the design's per-step exponent shift ----
# thr(M) = sup{ c' : box integral of ||prod||^{-2c'} finite }, built by the recursion:
#   base L=1 (single free t x M1 matrix): ∫_box ||X||^{-2c'} finite iff 2c' < t*M1 => thr = t*M1/2
#   step  L>=2: cover box by rank-cut charts t=0..min(M0,M1). Chart t:
#       - charge a(t) = (M0-t)(M1-t) at boundary 0 (Jacobian z^{a-1})
#       - EXPONENT SHIFT: tail integrand becomes g^{-2 c''}, c'' = c' - a/2, on tail chain (t,M2,...)
#       - chart-t converges iff  c'' < thr(tail),  i.e.  c' < a/2 + thr(tail) = a(t)/2 + thr(t,M2,..)
#   box finite iff ALL charts finite  => thr(M) = min_t [ a(t)/2 + thr(t,M2,...) ]
@lru_cache(maxsize=None)
def thr(M):
    L=len(M)-1
    if L==0: return 0.0
    if L==1: return M[0]*M[1]/2.0          # free-matrix base case = (1/2)minAdm(t,M1)
    best=None
    for t in range(min(M[0],M[1])+1):
        a=(M[0]-t)*(M[1]-t)
        val = a/2.0 + thr((t,)+M[2:])       # charge/2  +  shifted-tail threshold
        best = val if best is None else min(best,val)
    return best

print("=== arity-peel threshold thr(M) vs (1/2)minAdm(M) ===")
for M in [(2,2,2),(2,1,2),(2,2,2,2),(3,3,3,3),(3,3,4),(4,4,2,2),(2,3,4),(2,2,2,3)]:
    lhs = thr(M); rhs = minAdmRec(M)/2.0
    print(f"  M={M!s:14}  thr={lhs:5.2f}   (1/2)minAdm={rhs:5.2f}   {'OK' if abs(lhs-rhs)<1e-12 else 'MISMATCH'}")

print("\n=== exhaustive: thr == (1/2)minAdm over random chains (widths 0..4, L=2..5) ===")
random.seed(7); mism=0; N=8000
for _ in range(N):
    L=random.randint(2,5); M=tuple(random.randint(0,4) for _ in range(L+1))
    if abs(thr(M)-minAdmRec(M)/2.0)>1e-12:
        mism+=1
        if mism<=5: print("   MISMATCH",M,thr(M),minAdmRec(M)/2.0)
print(f"  mismatches: {mism}/{N}")

# ---- per-chart threshold: >= (1/2)minAdm for all t, tight at binding t ----
def chart_thresholds(M):
    out=[]
    for t in range(min(M[0],M[1])+1):
        a=(M[0]-t)*(M[1]-t)
        tail=(t,)+M[2:]
        ct = a/2.0 + minAdmRec(tail)/2.0
        out.append((t, a, minAdmRec(tail), ct))
    return out

print("\n=== per-chart thresholds (t, charge a, tail minAdm, chart-threshold) ; box thr = MIN ===")
for M in [(2,2,2,2),(3,3,3,3)]:
    print(f"  M={M}   (1/2)minAdm = {minAdmRec(M)/2.0}")
    for t,a,tm,ct in chart_thresholds(M):
        binder = "  <-- BINDING (min)" if abs(ct-minAdmRec(M)/2.0)<1e-12 else ""
        print(f"     t={t}: charge a=(M0-t)(M1-t)={a:2d}, tail minAdm({(t,)+M[2:]})={tm}, chart c'<{ct:.2f}{binder}")
    print(f"     -> every chart c'-threshold >= (1/2)minAdm; box converges up to the MIN = {minAdmRec(M)/2.0}\n")
