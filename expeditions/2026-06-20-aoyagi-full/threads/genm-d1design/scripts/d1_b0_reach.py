"""
b=0 + POWER-interior + d1 a>=u: is the joint source-tail incidence (nested-qbox) recursion REACHABLE
(reaches 1/2 minAdm, terminates), or a second WALL?  minAdmRec from RouteMLayerSplit.lean.
Key checks:
 (1) b=0 cut-soundness at t=M1: minAdm(M) <= peelCharge(M1)+minAdm(redChain M1 M) = 0 + minAdm(redChain M1 M).
     [peelCharge(M1)=(M0-M1)(M1-M1)=0]  => headroom Delta = minAdm(redChain M1 M)-minAdm(M) >= 0.
 (2) Is there a LEAF clean sub-regime for b=0: redChain M1 M is a 2-width leaf (Q_p = a single FREE layer),
     so det(Q_p Q_p^T) is a FREE-box Gram (one qbox, no recursion)?  <=> arity(M)=3 (redChain M1 M = (M1,M2)).
 (3) The nested-qbox termination: the product-Gram det(Q_p Q_p^T)^{-M0/2} disposed by integrating the reduced
     chain's free layers one at a time (qbox per level), terminating at the last free layer. The per-level
     charge bookkeeping = the minAdm recursion of redChain M1 M (reduced-chain recursion) — reaches minAdm.
"""
from functools import lru_cache
from itertools import product
@lru_cache(maxsize=None)
def minAdmRec(M):
    n=len(M)
    if n<=1: return 0
    if n==2: return M[0]*M[1]
    return min((M[0]-t)*(M[1]-t)+minAdmRec((t,)+M[2:]) for t in range(0,min(M[0],M[1])+1))
def redChain(t,M): return (t,)+M[2:]
def gen(ar,w):
    for L in ar:
        for M in product(range(1,w+1),repeat=L): yield M

b0_total=0; b0_cutsound_fail=0; b0_leaf=0; b0_recurse=0; head0=0
for M in gen([4,5],6):
    M0,M1=M[0],M[1]
    if M1>M0: continue          # b=0 wing needs M1<=M0
    b0_total+=1
    mA=minAdmRec(M); rc=redChain(M1,M); mRC=minAdmRec(rc)
    # (1) cut-soundness at t=M1 (peelCharge=0)
    if mA > 0 + mRC: b0_cutsound_fail+=1
    if mRC==mA: head0+=1
    # (2) leaf sub-regime: redChain M1 M is 2-width (arity(M)=3)?  arity(M)=len(M); redChain has len(M)-1 widths.
    if len(rc)==2: b0_leaf+=1
    else: b0_recurse+=1
print("b=0 wing cells:", b0_total)
print("  cut-soundness at t=M1 (peelCharge=0) fails:", b0_cutsound_fail, "(0 => reduction to redChain M1 M valid, headroom>=0)")
print("  zero-headroom (minAdm(redChain M1 M)==minAdm(M)):", head0, "(these have NO slack for the Gram in the reduced threshold)")
print("  LEAF clean sub-regime (redChain M1 M = 2-width, Gram of a FREE layer, one qbox):", b0_leaf)
print("  RECURSE (redChain M1 M >=3-width, Gram of a PRODUCT -> nested-qbox recursion):", b0_recurse)
print()
print("INTERPRETATION: b=0 always yields det(Q_p Q_p^T)^{-M0/2}, Q_p=prod(redChain M1 M).")
print("  LEAF (arity 3): Q_p is a single FREE layer -> free-box qbox, ONE shot (this is waist-pin's 'clean qbox').")
print("  RECURSE (arity>=4): Q_p is a PRODUCT -> the Gram is tail-coupled -> nested-qbox recursion (native,")
print("  terminating at the last free layer) = the joint source-tail incidence = SAME as POWER-interior & d1 a>=u.")
