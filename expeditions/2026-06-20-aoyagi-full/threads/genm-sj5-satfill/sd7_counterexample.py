"""SD-7 (deeperFlagSaturatedShell_reduce) is FALSE as stated — exact-integer certificate.

Refutes the domination  shellSpineIntegrand ≤ C · (cornerComparator (redChain u M) ![1] ![minAdm-1]).integral c'
for M=(1,1,2,2), t=1, j=0, c' in [1/2, 1). At a=b=0 both sides share the SAME finite box integral J of
frobSq(prod(1,2,2)·)^(-c'); dividing it out reduces the claim to a scalar inequality between a divergent
LHS pivot integral and a finite RHS radial integral.  minAdm matches Lean RouteMLayerSplit.minAdmRec.
"""
from functools import lru_cache

def redChain(t, M):        # (t, M2, M3, ..., Mlast)
    return (t,) + tuple(M[2:])

@lru_cache(None)
def minAdmRec(M):
    M = tuple(M); n = len(M)
    if n == 1: return 0
    if n == 2: return M[0] * M[1]
    return min((M[0]-t)*(M[1]-t) + minAdmRec(redChain(t, M))
               for t in range(0, min(M[0], M[1]) + 1))

M, t, j = (1, 1, 2, 2), 1, 0
u = t + j
r = min(M[0]-t, M[1]-t)
a, b = M[0]-u, M[1]-u
m = minAdmRec(redChain(u, M))          # comparator monomial exponent + 1

assert j == r,            "hjeq (saturated shell) must hold"
assert min(a, b) == 0,    "corner must degenerate at j=r"
assert m == 2 and minAdmRec(M) == 1, "exact minAdm values"

print(f"M={M} t={t} j={j}  u={u} r={r}  a={a} b={b} (min=0, peelCharge=0)")
print(f"redChain u M = {redChain(u,M)}  minAdm={m}  -> RHS monomial |v|^(m-1)=|v|^{m-1}")
print(f"carrierThreshold(M)=minAdm(M)/2={minAdmRec(M)/2}  (caller's hcT window; SD-7 omits it)")
print()
print("Reduced scalar inequality (both sides share the same finite box integral J):")
print("   int_{-1}^{1} |p|^(-2c') dp   <=?   C * int_0^1 v^(m-1-2c') dv")
for cprime in (0.3, 0.5, 0.7, 0.9):
    lhs_conv = 2*cprime < 1                      # LHS pivot integral finite iff 2c'<1
    rhs_conv = (m-1) - 2*cprime > -1             # RHS radial integral finite iff m-2c'>0
    verdict = "OK" if lhs_conv else ("SD-7 FALSE" if rhs_conv else "both diverge")
    print(f"  c'={cprime}:  LHS finite={lhs_conv}  RHS finite={rhs_conv}  -> {verdict}")
print()
print("For c' in [0.5, 1): LHS = +inf, RHS finite  =>  no finite C  =>  SD-7 domination is FALSE.")
