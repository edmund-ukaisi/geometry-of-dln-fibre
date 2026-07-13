from functools import lru_cache
from itertools import product
@lru_cache(maxsize=None)
def minadm(M):
    L1=len(M)
    if L1==1: return 0
    if L1==2: return M[0]*M[1]
    return min((M[0]-t)*(M[1]-t)+minadm((t,)+M[2:]) for t in range(min(M[0],M[1])+1))
def is_waist(M): return len(M)>=3 and M[1]<min(M[2:])
rev=lambda M: tuple(reversed(M))

# Codex F3 witness: (4,2,3,3) minAdm=5 diverges 5/2<c'<3, (4,2,3) minAdm=6 finite there
print("Codex F3 witness: minAdm(4,2,3,3)=",minadm((4,2,3,3))," minAdm(4,2,3)=",minadm((4,2,3)))

# reversal makes >=4-width waist chains front-GOOD:  N=rev M not front-pinched
print("\n>=4-width waist chains: is rev(M) NOT front-pinched (i.e. front-good)?")
bad=[]
for nw in range(4,7):
  for M in product(range(1,7),repeat=nw):
    if is_waist(M):
      if is_waist(rev(M)): bad.append((M,rev(M)))
print("  rev(waist) is front-good:", "OK all" if not bad else "FAIL "+str(len(bad))+" eg "+str(bad[:8]))

# minAdm reversal invariance (banked minAdm_comp_perm) sanity
badr=[M for nw in range(3,6) for M in product(range(1,6),repeat=nw) if minadm(M)!=minadm(rev(M))]
print("minAdm(M)=minAdm(rev M):", "OK" if not badr else "FAIL "+str(badr[:5]))

# reversal reduced target for 4-width waist M: head-split rev(M) -> redChain(u,rev M)=(u,M_{L-2},...,M0)
# check the reduced-chain threshold works: these are one-shorter, closed by IH (arity decreases). structural, no numeric needed.
print("\nWorked: (3,2,3,4) waist -> rev=(4,3,2,3); front-good? ", not is_waist((4,3,2,3)),
      " minAdm both:",minadm((3,2,3,4)),minadm((4,3,2,3)))
