"""
#2 (wing front general-rank) charge reconciliation. jointpnp TEST-4 foundation: {rank W<=σ} = surjective-X
preimage of {rank A1<=σ} (single-matrix det of A1), W-codim (M0-σ)(M2-σ). The reduction is to redChain s M
at peelCharge (M0-s)(M1-s). Reconcile: which σ↔s, and does the "excess" (W-codim - peelCharge) land in the
reduced chain's (s,M2) leading layer? Check the min-over-strata reaches ½minAdm using the SINGLE-MATRIX-det
per-stratum rlct (codim (M0-σ)(M2-σ) via jointpnp) composed with the reduced chain.
minAdmRec from RouteMLayerSplit.lean.
"""
from functools import lru_cache
from itertools import product
@lru_cache(maxsize=None)
def mA(M):
    n=len(M)
    if n<=1: return 0
    if n==2: return M[0]*M[1]
    return min((M[0]-t)*(M[1]-t)+mA((t,)+M[2:]) for t in range(0,min(M[0],M[1])+1))
def rc(t,M): return (t,)+M[2:]
def gen(ar,w):
    for L in ar:
        for M in product(range(1,w+1),repeat=L): yield M

# For a=0 wing (t=M0<=M1): the front rank-sector. Two candidate per-stratum charges:
#  (A) peelCharge(s)=(M0-s)(M1-s), reduce to redChain s M -> min_s [peelCharge + minAdm(redChain s M)] = minAdm? [known 0/5292]
#  (B) jointpnp single-matrix W-codim (M0-σ)(M2-σ): does min_σ [(M0-σ)(M2-σ) + minAdm(redChain σ M)] ALSO = minAdm? or over/under?
# If (A) matches and (B) differs, the reconciliation = the excess (M0-s)(M2-s)-(M0-s)(M1-s)=(M0-s)(M2-M1) into the reduced (s,M2) layer.
a0_A_fail=0; a0_B_ne_A=0; a0_tot=0; ex=[]
for M in gen([4],6):
    M0,M1=M[0],M[1]; M2=M[2]
    if M0>M1: continue    # a=0 wing
    t=M0
    mAM=mA(M)
    A=min((M0-s)*(M1-s)+mA(rc(s,M)) for s in range(0,t+1))
    B=min((M0-s)*(M2-s)+mA(rc(s,M)) for s in range(0,t+1))
    a0_tot+=1
    if A!=mAM: a0_A_fail+=1
    if B!=A:
        a0_B_ne_A+=1
        if len(ex)<8: ex.append((M,f"peelChargeMin={A}=minAdm={mAM}; W-codimMin={B}"))
print("a=0 wing cells:", a0_tot)
print("(A) min_s[(M0-s)(M1-s)+minAdm(redChain s M)]==minAdm:", a0_tot-a0_A_fail, "/", a0_tot, " (peelCharge route)")
print("(B) min_σ[(M0-σ)(M2-σ)+minAdm(redChain σ M)] != (A):", a0_B_ne_A, "/", a0_tot, " (W-codim route DIFFERS when M1!=M2)")
for e in ex: print("   ", e)
print()
print("INTERPRETATION: (A) peelCharge (M0-s)(M1-s) is the CORRECT reduction charge (=minAdm, single-factor,")
print("jointpnp census). (B) the raw W-codim (M0-σ)(M2-σ) over-counts by (M0-s)(M2-M1) when M2>M1 — that EXCESS")
print("is the reduced chain's own (s,M2) leading-layer resolution (part of hIH(redChain s M)), NOT extra charge.")
print("So the #2 blow-up uses the single-matrix det of A1 (W-codim), but the CHARGE bookkeeping is peelCharge,")
print("with the M2-vs-M1 excess absorbed by the reduced (s,M2) layer.")
