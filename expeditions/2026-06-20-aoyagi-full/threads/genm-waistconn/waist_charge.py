from functools import lru_cache
from itertools import product
@lru_cache(maxsize=None)
def minadm(M):
    L1=len(M)
    if L1==1: return 0
    if L1==2: return M[0]*M[1]
    return min((M[0]-t)*(M[1]-t)+minadm((t,)+M[2:]) for t in range(min(M[0],M[1])+1))
def is_waist(M): return len(M)>=3 and M[1]<min(M[2:])

# M1=1 waists: front-drop factorizes -> min(M0/2, minAdm(tail)/2) >= minAdm(M)/2 ?
print("M1=1 waists: is min(M0, minAdm(tail)) >= minAdm(M)? (both thresholds cover)")
bad=[]
for nw in range(3,6):
  for M in product(range(1,7),repeat=nw):
    if is_waist(M) and M[1]==1:
      if min(M[0], minadm(M[1:])) < minadm(M): bad.append(M)
print("  ", "OK all" if not bad else "FAIL "+str(bad[:6]))

# M1>=2 L>=1 waists: report the front/tail thresholds. front-drop needs eigen (decorated tail IH).
print("\nM1>=2, L>=1 waist examples (M, minAdm(M), M0*M1, minAdm(tail)):")
seen=0
for nw in range(4,6):
  for M in product(range(1,6),repeat=nw):
    if is_waist(M) and M[1]>=2 and seen<12:
      print("  ",M, minadm(M), M[0]*M[1], minadm(M[1:])); seen+=1

# sanity: (3,2,3,4)
for M in [(3,2,3,4),(2,1,2,2),(4,3,4,4)]:
  print(M,"minAdm",minadm(M),"tail",M[1:],"minAdm(tail)",minadm(M[1:]),"M0M1",M[0]*M[1])
