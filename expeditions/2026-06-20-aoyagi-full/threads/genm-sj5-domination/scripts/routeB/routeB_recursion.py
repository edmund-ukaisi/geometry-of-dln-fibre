from functools import lru_cache
from itertools import product

@lru_cache(maxsize=None)
def minAdm(M):
    M=tuple(M)
    if len(M)==1: return 0
    if len(M)==2: return M[0]*M[1]
    return min((M[0]-t)*(M[1]-t)+minAdm((t,)+M[2:]) for t in range(min(M[0],M[1])+1))
def binding_cuts(M):
    mA=minAdm(M)
    return [t for t in range(min(M[0],M[1])+1)
            if (M[0]-t)*(M[1]-t)+minAdm((t,)+tuple(M[2:]))==mA]
def rho(M): return min(M[1:])
def rev(M): return tuple(reversed(M))

def pivot_ok_frontpeel(M):
    """head-split route finite at M peeling from the FRONT (strict convention)."""
    r=rho(M)
    for t in binding_cuts(M):
        if t>=1 and t*r < minAdm((t,)+tuple(M[2:])): return False
        for j in range(1, min(M[0]-t,M[1]-t)+1):
            u=t+j; a=M[0]-u; b=M[1]-u
            if a<1 or b<1: continue
            if u*r < minAdm((u,)+tuple(M[2:])): return False
    return True

@lru_cache(maxsize=None)
def routeB_dischargeable(M):
    """M is route-B dischargeable if SOME orientation (M or rev M) is pivot-good at the
       top peel AND every reduced chain (over that orientation's binding cuts) is itself
       dischargeable (recursively).  Base: <=2 widths trivially dischargeable."""
    M=tuple(M)
    if len(M)<=2: return True     # base leaf (n,m): minAdm=n*m, no peel
    for N in ({M, rev(M)}):
        if not pivot_ok_frontpeel(N): continue
        # all reduced chains over N's binding cuts must be dischargeable
        ok=True
        for t in binding_cuts(N):
            red=(t,)+tuple(N[2:])
            if not routeB_dischargeable(red): ok=False; break
        if ok: return True
    return False

# ---- full-recursion route-B dischargeability over widths 1..6, lengths 3..6 ----
stuck=[]
n=0
for Ln in [3,4,5,6]:
    for M in product(range(1,7),repeat=Ln):
        n+=1
        if not routeB_dischargeable(M): stuck.append(M)
print(f"chains scanned: {n}")
print(f"NOT route-B-dischargeable (full oriented recursion, per-node reversal+branch): {len(stuck)}")
# minimal
canon=sorted(set(min(M,rev(M)) for M in stuck), key=lambda M:(sum(M),len(M),M))
print("minimal non-dischargeable (up to reversal):", canon[:8])

# ---- do the bad WAIST chains also ARISE as reduced chains of good/other chains? ----
print("\nDo waist counterexamples arise as reduced chains of larger chains?")
targets={(2,1,2),(3,2,3),(3,1,3)}
found={t:[] for t in targets}
for Ln in [4,5]:
    for M in product(range(1,7),repeat=Ln):
        for t in binding_cuts(M):
            red=(t,)+tuple(M[2:])
            c=min(red,rev(red))
            if c in found and len(found[c])<3:
                found[c].append((M,'peel@t=%d'%t,'->',red))
for k,v in found.items():
    print(f"  {k} appears as redChain of e.g. {v[:2]}")

# ---- WHY: relate 'stuck' to the local structure (interior bottleneck) ----
print("\nStructure: is every stuck chain one with an interior waist < both neighbors somewhere?")
def has_strict_interior_waist(M):
    # some interior index i with M[i] < M[i-1] and M[i] < M[i+1]
    return any(M[i]<M[i-1] and M[i]<M[i+1] for i in range(1,len(M)-1))
print("  all stuck have a strict interior waist?", all(has_strict_interior_waist(M) for M in stuck))
print("  # chains WITH interior waist total:", sum(1 for Ln in [3,4,5,6] for M in product(range(1,7),repeat=Ln) if has_strict_interior_waist(M)))
