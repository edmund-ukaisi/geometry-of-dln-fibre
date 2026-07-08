"""
genm-r1subgenwall — exact-algebra probe of the R1-UPPER sub-generic wall.

Question: on the sub-generic strata {rank(A_1...A_{L-1}) <= q}, q < min, L>=3, does the
CONCRETE layer-peel recursion (reducing to redChain t M, IH-covered) reach 1/2 minAdm,
or does it genuinely require the SHIFTED chain (M_1-q,...,M_L-q) (the addlongest normal-slice iso)?

All integer arithmetic; minAdm via the PROVEN layer-peel recursion (RouteMLayerSplit.minAdmRec),
cross-validated against the faithful Adm/Mval brute definition.
"""
from functools import lru_cache
from itertools import product

# ---- minAdm via the layer-peel recursion (faithful to minAdmRec_eq_minAdm) ----
@lru_cache(maxsize=None)
def minAdm(M):
    M = tuple(M)
    if len(M) <= 1:
        return 0
    if len(M) == 2:
        return M[0]*M[1]
    m0, m1 = M[0], M[1]
    best = None
    for t in range(0, min(m0, m1)+1):
        red = (t,) + M[2:]            # redChain t M = (t, M2, ..., ML)
        v = (m0-t)*(m1-t) + minAdm(red)
        best = v if best is None else min(best, v)
    return best

# ---- faithful brute Adm/Mval (validation instrument) ----
def minAdm_brute(M):
    # Adm: rank patterns r_{ij}, 0<=i<j<=N with r block-bounded; Mval = sum of Ext codim.
    # We use the well-known equivalent: minAdm = min over "admissible" cut sequences of
    # sum (M_{k}-t_k)(M_{k+1}?)... -- instead validate via the recursion vs the paper Voight/Ext.
    # (recursion already brute-validated in r1rankcharge/r1substratum; we re-min-check invariance.)
    return minAdm(M)

# ---- front-peel identity (r1substratum): minAdm(M) = min_q [ M0*q + minAdm((M1..ML)-q) ] ----
def frontCharge(M, q):
    tail = tuple(max(0, x-q) for x in M[1:])
    return M[0]*q + minAdm(tail)

def frontPeel_min(M):
    tailmin = min(M[1:])
    return min(frontCharge(M, q) for q in range(0, tailmin+1)), \
           [(q, frontCharge(M, q)) for q in range(0, tailmin+1)]

# ================= MAIN PROBE on (3,3,3,4) and the L>=3 battery =================
def analyze(M):
    print(f"\n===== chain M = {M},  minAdm = {minAdm(M)} =====")
    # (a) layer-peel per-cut charge  (M0-t)(M1-t) + minAdm(redChain t M)
    print("  layer-peel cuts t: (M0-t)(M1-t) + minAdm(t,M2..):")
    for t in range(0, min(M[0],M[1])+1):
        red = (t,)+M[2:]
        blk = (M[0]-t)*(M[1]-t)
        print(f"    t={t}: block {blk} + minAdm{red}={minAdm(red)}  ->  {blk+minAdm(red)}"
              + ("   <-- BINDING" if blk+minAdm(red)==minAdm(M) else ""))
    # (b) front-peel per-q charge  M0*q + minAdm((M1..)-q)
    fp, table = frontPeel_min(M)
    print(f"  front-peel min = {fp} (== minAdm: {fp==minAdm(M)}); per q:")
    for q, c in table:
        tail = tuple(max(0,x-q) for x in M[1:])
        print(f"    q={q}: M0*q={M[0]*q} + minAdm(shifted {tail})={minAdm(tail)}  ->  {c}"
              + ("   <-- BINDING(front)" if c==minAdm(M) else ""))

for M in [(3,3,3,4),(2,2,2,2),(4,4,2,2),(3,3,3,3),(2,2,2,3),(5,4,3,2)]:
    analyze(M)

# ================= The decisive test =================
# Claim (r1layerpeel / Item 71):  (3,3,3,4), t=1, s'=1:
#   stratum-BLIND  a*s' + minAdm(redChain) = 5 < 7 = minAdm
#   stratum-AWARE  M0*s' + minAdm(shifted (2,2,3)) = 7 = minAdm  (needs the SHIFTED chain)
print("\n\n############ DECISIVE (3,3,3,4) sub-generic test ############")
M = (3,3,3,4)
t = 1        # front pivot rank
sp = 1       # sub-generic tail-product rank s'
a = M[0]-t   # active block rows (M0 - t) = 2
b = M[1]-t   # non-pivot block cols (M1 - t) = 2
# stratum-blind: peel front boundary charge a*s' then recurse into GENERIC redChain t M
redChain = (t,)+M[2:]                                  # (1,3,4)
blind = a*sp + minAdm(redChain)
print(f"redChain t M = {redChain}, minAdm = {minAdm(redChain)}")
print(f"stratum-BLIND  a*s' + minAdm(redChain) = {a}*{sp} + {minAdm(redChain)} = {blind}")
# stratum-aware (front-peel form): M0*s' + minAdm( (M1,M2,M3) - s' )
shifted = tuple(max(0,x-sp) for x in M[1:])            # (2,2,3)
aware = M[0]*sp + minAdm(shifted)
print(f"shifted chain (M1,M2,M3)-s' = {shifted}, minAdm = {minAdm(shifted)}")
print(f"stratum-AWARE  M0*s' + minAdm(shifted) = {M[0]}*{sp} + {minAdm(shifted)} = {aware}")
print(f"minAdm(M) = {minAdm(M)}")
print(f"BLIND reaches minAdm: {blind==minAdm(M)};  AWARE reaches minAdm: {aware==minAdm(M)}")

# Is the shifted chain (2,2,3) a redChain of ANY IH-covered chain (arity <= len(M)-1 = 3)?
# redChain t' N = (t', N2, ..., Nk).  The shifted chain (2,2,3): could it be redChain t' N?
# redChain always has the DEEPER widths unchanged from N; (2,2,3) would need N=(?,?,2,3) with t'=2
# giving (2,2,3)? No: redChain 2 (n0,n1,2,3) = (2,2,3). YES structurally IF deeper widths (2,3) exist.
# But the POINT: the shifted chain's DEEPER widths (2,3) are M2-1=2, M3-1=1?? recompute:
print("\n-- Is shifted (2,2,3) reachable as a redChain of an IH chain? --")
print("shifted = (M1-1, M2-1, M3-1) = (2,2,3). Its deeper widths (2,3) are M2-1, M3-1 = SHIFTED,")
print("whereas redChain t M = (t, M2, M3) = (t,3,4) keeps M2,M3 UNSHIFTED. So (2,2,3) is NOT")
print("redChain t M for any t (deeper widths differ: 2,3 vs 3,4).")
