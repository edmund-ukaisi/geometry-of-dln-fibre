import itertools
from functools import lru_cache

# Faithful transcription of Lean Adm/Mval (Lambda.lean):
#   M = (M0..ML), L=len-1 ; T=(t0..t_{L-1}) [paper t^1..t^L]
#   admBound: j=0 -> min(M0,M1); j>=1 -> M[j+1]
#   admPred: weakly-decreasing, t_{L-1}=0, 0<=tj<=admBound
#   Mval = sum_{j=0}^{L-1} (tPrev_j - tj)*(M[j+1]-tj),  tPrev_0=M0, tPrev_j=t_{j-1}
def minAdm(M):
    L = len(M)-1
    if L == 0: return 0
    bounds = [min(M[0],M[1])] + [M[j+1] for j in range(1,L)]
    best = None
    # enumerate weakly-decreasing T with last=0
    ranges = [range(bounds[j]+1) for j in range(L)]
    for T in itertools.product(*ranges):
        if T[-1] != 0: continue
        if any(T[i] < T[i+1] for i in range(L-1)): continue  # weak decrease t0>=t1>=...
        val = 0
        for j in range(L):
            tprev = M[0] if j==0 else T[j-1]
            val += (tprev - T[j])*(M[j+1]-T[j])
        if best is None or val < best: best = val
    return best

def deepTailMin(M):
    return min(M[2:]) if len(M)>2 else M[-1]

# sanity: Aoyagi-style small cases
print("sanity minAdm:")
for M in [(2,2),(2,2,2),(4,4,4,4),(3,4,5,4),(2,3,2,2),(2,2,2,2)]:
    print(f"  M={M}: minAdm={minAdm(M)}  M0*min(M1,rho)={M[0]*min(M[1],deepTailMin(M))}")

print("\n"+"="*70)
print("KEY INEQUALITY minAdm(M) <= M0*min(M1, deepTailMin)  [uniform I_loss bound]")
print("interior cell exists: exists u in [0,min(M0,M1)] with (M0-u)+(M1-u) <= rho")
print("="*70)
def interior_us(M):
    rho = deepTailMin(M)
    return [u for u in range(0,min(M[0],M[1])+1) if (M[0]-u)+(M[1]-u) <= rho]

wit = [(4,4,4,4),(3,4,5,4),(3,3,3,4),(2,3,2,2),(5,5,5,5,5),(3,4,5,6,7),(6,8,5,5),(2,3,2,2,2)]
print("\nnamed witnesses:")
for M in wit:
    ma=minAdm(M); rhs=M[0]*min(M[1],deepTailMin(M)); ius=interior_us(M)
    print(f"  M={M}: minAdm={ma}  RHS={rhs}  {'OK' if ma<=rhs else '*** FAIL ***'}  slack={rhs-ma}  interior_u={ius}")

print("\nSCAN arity 3,4 widths 2..7  (report failures where an interior cell exists):")
fails=0; tot=0; margins=[]
for arity in (3,4):
    for M in itertools.product(range(2,8),repeat=arity):
        ius=interior_us(M)
        if not ius: continue
        tot+=1
        ma=minAdm(M); rhs=M[0]*min(M[1],deepTailMin(M))
        margins.append(rhs-ma)
        if ma>rhs:
            fails+=1
            if fails<=20: print(f"  FAIL M={M}: minAdm={ma} > RHS={rhs}  interior_u={ius}")
print(f"\n  interior-cell M's tested={tot}  failures={fails}  min slack={min(margins) if margins else 'NA'}  max slack={max(margins) if margins else 'NA'}")

# also: is the inequality EVER tight (slack 0)? those are the delicate cases
tights=[M for arity in (3,4) for M in itertools.product(range(2,8),repeat=arity)
        if interior_us(M) and minAdm(M)==M[0]*min(M[1],deepTailMin(M))]
print(f"  tight cases (slack=0), count={len(tights)}, examples={tights[:8]}")
