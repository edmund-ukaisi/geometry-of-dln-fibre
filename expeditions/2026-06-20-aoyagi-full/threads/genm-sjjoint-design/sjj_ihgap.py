from functools import lru_cache
# ============================================================
# THE DECISIVE STRUCTURAL CHECK: at the BINDING cut t*, the atom-residual exponent on P_tail
#   (c' - a/2)  ->  ½·minAdm(redChain t* M)   as c' -> ½·minAdm M,
# i.e. the residual SATURATES the reduced chain's IH threshold, leaving ZERO budget for the
# coupling factor P_full^{-a/2} (Gram det). => no black-box product/Hölder bound via the IH can
# absorb the coupling; the shared exceptional divisors must carry BOTH orders (the (S,J) resolution).
# ============================================================
@lru_cache(None)
def minAdm(M):
    L=len(M)-1
    if L==0: return 0
    if L==1: return M[0]*M[1]
    return min((M[0]-t)*(M[1]-t)+minAdm((t,)+M[2:]) for t in range(min(M[0],M[1])+1))
def redChain(t,M): return (t,)+M[2:]
def tailChain(M): return M[1:]

print("For each chain: at binding cut t*, check ½·minAdm(M) = a/2 + ½·minAdm(redChain),")
print("so residual exponent (c'-a/2) -> ½·minAdm(redChain) as c'->½·minAdm(M) [budget SATURATED].\n")
bad=0; N=0
def binding_cut(M):
    best=None; bt=None
    for t in range(min(M[0],M[1])+1):
        v=(M[0]-t)*(M[1]-t)+minAdm(redChain(t,M))
        if best is None or v<best: best=v; bt=t
    return bt,best
for M in [(3,3,3,3),(2,2,2,2),(4,4,4,4),(3,3,4),(2,4,1),(3,3,3),(2,2,2)]:
    if len(M)-1<2: continue
    bt,val=binding_cut(M); a=(M[0]-bt)*(M[1]-bt); red=redChain(bt,M)
    lhs=val; rhs=a+minAdm(red)
    sat = (val == rhs)   # minAdm M == a + minAdm(redChain)  at binding cut (definitional)
    # coupling factor exponent a/2 ; budget left for coupling after P_tail saturates:
    # total ½minAdm(M) - (c'-a/2 -> ½minAdm(red)) - a/2 = ½minAdm(M) - ½minAdm(red) - a/2 = 0
    leftover = val - minAdm(red) - a
    print(f"  M={M}: t*={bt}, a={a}, redChain={red} minAdm={minAdm(red)} | "
          f"minAdm(M)={val} =? a+minAdm(red)={rhs} [{sat}]  leftover-budget(×2)={leftover}")
    N+=1
    if leftover!=0: bad+=1

# exhaustive over random chains: minAdm(M)=a*+minAdm(red*) at binding cut, leftover budget always 0
import random; random.seed(3); bad2=0; N2=4000
for _ in range(N2):
    L=random.randint(2,5); M=tuple(random.randint(1,4) for _ in range(L+1))
    bt,val=binding_cut(M); a=(M[0]-bt)*(M[1]-bt); red=redChain(bt,M)
    if val - minAdm(red) - a != 0: bad2+=1
print(f"\n  exhaustive: leftover-budget nonzero in {bad2}/{N2} random chains (0 => residual ALWAYS saturates IH threshold at binding cut)")

# ------------------------------------------------------------
# Hölder feasibility at the binding cut: to bound ∫ P_tail^{-(c'-a/2)} P_full^{-a/2} by a PRODUCT
# via Hölder (1/r+1/s=1, r,s>1) using the IH, need
#    (c'-a/2)·r < ½minAdm(redChain)   AND   (a/2)·s < ½minAdm(tailChain).
# As c'->½minAdm(M), (c'-a/2)->½minAdm(redChain), so need r<1 — IMPOSSIBLE (r>1). Hölder fails
# at EVERY binding cut with a>0.
# ------------------------------------------------------------
print("\nHölder feasibility at binding cut (need r>1 with (c'-a/2)r < ½minAdm(red) as c'->thresh):")
for M in [(3,3,3,3),(4,4,4,4),(2,2,2,2)]:
    bt,val=binding_cut(M); a=(M[0]-bt)*(M[1]-bt); red=redChain(bt,M)
    # limiting exponent on P_tail = ½minAdm(red); max r = ½minAdm(red)/(c'-a/2) -> 1
    rmax = minAdm(red)/minAdm(red) if a>0 else float('inf')  # limit = 1 exactly when a>0
    print(f"  M={M}: t*={bt} a={a}  max Hölder r (limit) = {rmax if a>0 else 'inf (a=0, trivial cut)'}"
          f"  => {'HÖLDER FAILS (need r>1)' if a>0 else 'trivial'}")
