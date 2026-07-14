"""
T-Obl3b M2>M1 scope sweep.  Adjudicates the coverage question for the off-sector
mountain divergence on wide (M2>M1) chains.  EXACT integer arithmetic (minAdm via
the layer-peeling recursion); no floats in the load-bearing classification.

Quantities at a node chain M = (M0,M1,M2,...,ML), binding cut t*, off-sector u=t*+j:
  a = M0 - u,  b = M1 - u                        (row/col coranks of the front block)
  Z_deep = A1..A_{L-1} : M2 x ML                 (deep tail product)
  shell-CERTIFIED floor rank of Z_deep: m = min(M1, ML) - j   (Ky-Fan via Z_full=A0.Z_deep, M1 rows)
  corank weight W converges  <=>  rank(Z_deep) >= a+b.
  current single-eps shell can only certify m, so the CURRENT bound converges <=> m >= a+b.
  TRUE generic rank of Z_deep = deep bottleneck = min(M2,M3,...,ML).
"""
from functools import lru_cache
from itertools import product
from collections import Counter

@lru_cache(maxsize=None)
def minAdm(M):
    M = tuple(M)
    if len(M) == 1: return 0
    if len(M) == 2: return M[0]*M[1]
    best = None
    for t in range(min(M[0], M[1]) + 1):
        red = (t,) + M[2:]
        v = (M[0]-t)*(M[1]-t) + minAdm(red)
        best = v if best is None else min(best, v)
    return best

def binding_cuts(M):
    mA = minAdm(M)
    return [t for t in range(0, min(M[0], M[1]) + 1)
            if (M[0]-t)*(M[1]-t) + minAdm((t,)+tuple(M[2:])) == mA]

def analyse(M):
    """Return list of records for every proper off-sector shell (a>=1,b>=1) at every binding cut."""
    recs = []
    ML = M[-1]; M1 = M[1]; M2 = M[2]
    deepbott = min(M[2:])           # true generic rank of Z_deep (= min of deep-tail widths)
    for tstar in binding_cuts(M):
        r = min(M[0]-tstar, M[1]-tstar)
        for j in range(1, r+1):
            u = tstar + j; a = M[0]-u; b = M1-u
            if a < 1 or b < 1: continue
            m = min(M1, ML) - j                     # shell-certified floor
            cur_conv = (m >= a+b)                   # current single-eps bound converges?
            true_conv = (deepbott >= a+b)           # finer Z_deep-strat GENERIC stratum converges?
            recs.append(dict(M=M, tstar=tstar, j=j, u=u, a=a, b=b, m=m,
                             M1=M1, M2=M2, ML=ML, deepbott=deepbott,
                             wide=(M2 > M1), cur_conv=cur_conv, true_conv=true_conv))
    return recs

# ---- Sweep over 3..5 width chains, widths 2..5 --------------------------------
allrecs = []
for Llen in [3, 4, 5]:
    for M in product(range(2, 6), repeat=Llen):
        allrecs += analyse(M)

print("total proper off-sector shells (a>=1,b>=1):", len(allrecs))
fails = [r for r in allrecs if not r['cur_conv']]
print("CURRENT-BOUND failures (m < a+b):", len(fails))

# (1) every current-bound failure has M2>M1 ?
print("\n[Q1a] every current-bound failure is M2>M1 (local wide step)?",
      all(r['wide'] for r in fails))
print("[Q1a] any failure with M2<=M1?", any(not r['wide'] for r in fails))

# (2) L>=1 gate: at L=0 (3-width) Z_deep is a single width, generic rank full
fails_L0 = [r for r in fails if len(r['M']) == 3]
print("[Q1b] 3-width (L=0) current-bound failures:", len(fails_L0),
      " (expect nonzero only if deep bottleneck matters; see true_conv)")

# (3) does the FINER Z_deep-strat generic stratum converge on ALL current-bound failures?
print("\n[Q3] finer-strat generic stratum (deepbott >= a+b) holds on ALL current-bound failures?",
      all(r['true_conv'] for r in fails))
resid = [r for r in fails if not r['true_conv']]
print("[Q3] residual after finer strat (deepbott < a+b):", len(resid))
if resid:
    for r in resid[:12]:
        print("     ", r['M'], "u=%d a=%d b=%d m=%d deepbott=%d" % (r['u'],r['a'],r['b'],r['m'],r['deepbott']))

# (4) characterise the failing LEADING triple (M0,M1,M2) patterns
print("\n[scope] failing leading triples (M0,M1,M2) and their (a,b) — top patterns:")
pat = Counter((r['M'][0], r['M'][1], r['M'][2], r['a'], r['b']) for r in fails)
for k, v in sorted(pat.items()):
    m0,m1,m2,a,b = k
    print("     (M0,M1,M2)=(%d,%d,%d)  a=%d b=%d   x%d   [M0>M1:%s, M2>M1:%s]"
          % (m0,m1,m2,a,b,v, m0>m1, m2>m1))

# (5) sorting removes the wide pattern: for each failing chain, does its DESCENDING sort
#     have any current-bound failure?  (illustrates Q2 WOULD help IF finiteness were perm-invariant)
print("\n[Q2 illustration] for each distinct failing chain, does descending-sorted chain still fail?")
failM = sorted(set(r['M'] for r in fails))
still = 0
for M in failM:
    Msort = tuple(sorted(M, reverse=True))
    sf = [r for r in analyse(Msort) if not r['cur_conv']]
    if sf: still += 1
print("     distinct failing chains:", len(failM),
      " | of which descending-sorted STILL current-bound-fails:", still)
print("     (minAdm invariant check on a sample:)")
for M in failM[:5]:
    Msort = tuple(sorted(M, reverse=True))
    print("       minAdm%s=%d  minAdm(sorted)%s=%d  equal=%s"
          % (M, minAdm(M), Msort, minAdm(Msort), minAdm(M)==minAdm(Msort)))
