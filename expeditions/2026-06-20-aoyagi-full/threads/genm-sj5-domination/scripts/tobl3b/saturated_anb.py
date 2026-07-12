from functools import lru_cache
from itertools import product

# Exact minAdmRec (RouteMLayerSplit.minAdmRec): base leaf (n,m)->n*m;
#   minAdm(M) = min_{0<=t<=min(M0,M1)} [ (M0-t)(M1-t) + minAdm( (t,M2,...) ) ].
# redChain(t,M) = (t, M2, M3, ...).  peelCharge = (M0-t)(M1-t).

@lru_cache(maxsize=None)
def minAdm(M):
    M = tuple(M); assert len(M) >= 2
    if len(M) == 2:
        return M[0]*M[1]
    best = None
    for t in range(0, min(M[0], M[1])+1):
        red = (t,) + M[2:]
        val = (M[0]-t)*(M[1]-t) + minAdm(red)
        best = val if best is None else min(best, val)
    return best

def binding_cuts(M):
    M = tuple(M); mn = minAdm(M); cuts = []
    for t in range(0, min(M[0], M[1])+1):
        red = (t,) + M[2:]
        if (M[0]-t)*(M[1]-t) + minAdm(red) == mn:
            cuts.append(t)
    return mn, cuts

def shell_table(M, tstar):
    """Full shell table at a binding cut t*: for each shell j=0..r,
       cut = t*+j, freed corner (a-j)(b-j), redChain minAdm, charge C_j,
       and the reduced-weight convergence a-j < M2-b+1 (j<r; exponent (a-j)/2)."""
    M = tuple(M); a = M[0]-tstar; b = M[1]-tstar; r = min(a, b); M2 = M[2]
    rows = []
    for j in range(0, r+1):
        cut = tstar + j
        red = (cut,) + M[2:]
        freed = (a-j)*(b-j)
        Cj = freed + minAdm(red)
        expo = (a - j)                 # numerator of the freed-corner Gram exponent (a-j)/2
        conv = a - j < M2 - b + 1      # strict det-Gram convergence (for the SURVIVING corank rows)
        rows.append(dict(j=j, cut=cut, redChain=red, freed=freed,
                         minAdm_red=minAdm(red), Cj=Cj,
                         gram_expo_num=expo, conv_strict=conv,
                         saturated=(j == r)))
    return dict(a=a, b=b, r=r, M2=M2, surviving_corank=abs(b-a), rows=rows)

def report(M):
    mn, cuts = binding_cuts(M)
    print(f"\nM={M}  minAdm={mn}  carrierThreshold={mn/2}  binding cuts t*={cuts}")
    for t in cuts:
        info = shell_table(M, t)
        a, b, r = info['a'], info['b'], info['r']
        print(f"  t*={t}: a={a} b={b} r=min={r}  M2={info['M2']}  "
              f"surviving corank |b-a|={info['surviving_corank']}")
        for row in info['rows']:
            tag = "SATURATED" if row['saturated'] else ""
            print(f"     j={row['j']} cut={row['cut']} redChain={row['redChain']} "
                  f"freed={row['freed']} minAdm_red={row['minAdm_red']} "
                  f"C_j={row['Cj']} (>=minAdm? {row['Cj']>=mn}) "
                  f"gramExpo=(a-j)/2=({row['gram_expo_num']})/2 "
                  f"convStrict(a-j<M2-b+1)={row['conv_strict']} {tag}")
    return mn, cuts

# ---- The anchor ----
print("="*70)
print("ANCHOR (3,4,4): the minimal a!=b saturated-shell test")
print("="*70)
report((3,4,4))

# sibling anchors around it
for M in [(3,3,3),(4,4,4),(3,4,4),(4,5,5),(2,4,4),(3,5,5),(2,3,3),(3,4,5),(4,5,6)]:
    report(M)

# ---- Broad adversarial sweep: does the SATURATED-shell charge EVER undershoot at a!=b? ----
print("\n" + "="*70)
print("ADVERSARIAL SWEEP: saturated-shell charge C_r vs minAdm(M) over a!=b anchors")
print("="*70)
undershoot = []
neg_gram = []           # saturated Gram exponent (a-r)/2 must be EXACTLY 0
nonzero_freed = []      # saturated freed corner must be EXACTLY 0
count = 0
# arity 3,4,5 chains, widths 1..6
for L in (3,4,5):
    for M in product(range(1,7), repeat=L):
        mn, cuts = binding_cuts(M)
        for t in cuts:
            a = M[0]-t; b = M[1]-t; r = min(a,b)
            if a == 0 or b == 0:      # degenerate freed corner already at t*
                continue
            count += 1
            red_sat = (t+r,) + M[2:]
            freed_sat = (a-r)*(b-r)
            Cr = freed_sat + minAdm(red_sat)
            if Cr < mn:
                undershoot.append((M,t,a,b,r,Cr,mn))
            # surviving-side Gram exponent = min(a-r,b-r)/2 ; MUST be 0 (one side exhausted)
            if min(a-r, b-r) != 0:
                neg_gram.append((M,t,a,b,r, min(a-r,b-r)))
            if freed_sat != 0:
                nonzero_freed.append((M,t,a,b,r,freed_sat))
print(f"binding-cut/anchor instances checked (a,b>=1): {count}")
print(f"saturated-shell UNDERSHOOTS (C_r < minAdm): {len(undershoot)}")
for x in undershoot[:20]: print("   UNDERSHOOT", x)
print(f"saturated-shell nonzero freed corner (a-r)(b-r)!=0: {len(nonzero_freed)}")
for x in nonzero_freed[:20]: print("   NONZERO-FREED", x)
print(f"saturated-shell surviving-side Gram exponent min(a-r,b-r)!=0: {len(neg_gram)}")
for x in neg_gram[:20]: print("   NONZERO-GRAM", x)

# ---- t*+r == min(M0,M1) (saturation boundary is the maximal legal cut) ----
print("\n" + "="*70)
print("SATURATION BOUNDARY: t*+r == min(M0,M1) (cuts t*+j, j>r, illegal)?")
print("="*70)
bad_boundary = []
for L in (3,4,5):
    for M in product(range(1,7), repeat=L):
        mn, cuts = binding_cuts(M)
        for t in cuts:
            a = M[0]-t; b = M[1]-t; r = min(a,b)
            if a==0 or b==0: continue
            if t + r != min(M[0], M[1]):
                bad_boundary.append((M,t,a,b,r,t+r,min(M[0],M[1])))
print(f"instances where t*+r != min(M0,M1): {len(bad_boundary)}")
for x in bad_boundary[:20]: print("   ", x)
