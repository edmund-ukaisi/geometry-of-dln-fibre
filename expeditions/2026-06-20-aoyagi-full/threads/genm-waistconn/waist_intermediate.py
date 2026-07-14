from functools import lru_cache
from itertools import product
@lru_cache(maxsize=None)
def minadm(M):
    L1=len(M)
    if L1==1: return 0
    if L1==2: return M[0]*M[1]
    return min((M[0]-t)*(M[1]-t)+minadm((t,)+M[2:]) for t in range(min(M[0],M[1])+1))
def is_waist(M): return len(M)>=3 and M[1]<min(M[2:])

# Does a FRONT-GOOD chain M (M1 >= min(M2..)) peel (redChain u) to a WAIST reduced chain with M1'>=2?
# redChain(u,M)=(u,M2,...). It's a waist iff M2 < min(M3,...). Its N1 = M2. So M1>=2 intermediate waist
# arises when M front-good AND M2 < min(M3,...) AND M2>=2.
found=[]
for nw in range(4,6):
  for M in product(range(1,6),repeat=nw):
    frontgood = M[1] >= min(M[2:])           # not a strict front pinch
    deeppinch = M[2] < min(M[3:]) if nw>=4 else False   # redChain becomes a waist
    if frontgood and deeppinch and M[2]>=2:
      found.append(M); 
      if len(found)>=8: break
  if len(found)>=8: break
print("Front-good chains whose front-peel yields an M1>=2 WAIST reduced chain (nontrivial decoration):")
for M in found: print("  ",M,"-> redChain(u,·)=(u,",M[2],",",*M[3:],") waist, N1=",M[2])
print("=> the M1>=2 decorated waist genuinely arises in the recursion." if found else "=> does not arise")
