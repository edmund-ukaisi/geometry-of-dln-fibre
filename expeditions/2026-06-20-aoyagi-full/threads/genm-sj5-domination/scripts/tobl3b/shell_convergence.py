from functools import lru_cache
from itertools import product

@lru_cache(maxsize=None)
def minAdm(M):
    M=tuple(M)
    if len(M)==2: return M[0]*M[1]
    best=None
    for t in range(0,min(M[0],M[1])+1):
        v=(M[0]-t)*(M[1]-t)+minAdm((t,)+M[2:])
        best=v if best is None or v<best else best
    return best

def binding_cuts(M):
    M=tuple(M); best=minAdm(M); res=[]
    for t in range(0,min(M[0],M[1])+1):
        if (M[0]-t)*(M[1]-t)+minAdm((t,)+M[2:])==best: res.append(t)
    return best,res

# ==================================================================
# THE KEY T-Obl3b EXACT CHECK:
#  On shell j (1<=j<=r=min(a,b)), the CoV's REDUCED det-Gram weight is
#  over (b-j) rows in the (M2-j)-strong subspace with exponent (a-j)/2.
#  It is FINITE  <=>  (a-j) < (M2-j)-(b-j)+1 = M2-b+1  <=>  a < M2-b+1+j.
#  So for j>=1 it is STRICTLY convergent  <=>  a <= M2-b+1 at the cut.
#  The BORDERLINE a = M2-b+1 bites ONLY at j=0 (theta-interpolation).
#
#  Verify:  at EVERY binding cut,  a <= M2-b+1   (=> all shells j>=1 strictly convergent),
#  and identify where equality (the j=0 borderline) occurs.
# ==================================================================
print("=== CHECK: a <= M2-b+1 at every genuine binding cut (=> shells j>=1 strictly convergent) ===")
viol=[]; borderline=[]; strict=0; total=0
ranges=[(range(1,8),4),(range(1,6),5),(range(1,5),6)]  # arity 3,4,5 sweeps
seen=set()
for rng_,length in ranges:
    for M in product(rng_,repeat=length):
        if M in seen: continue
        seen.add(M)
        best,cuts=binding_cuts(M)
        for t in cuts:
            a=M[0]-t; b=M[1]-t; M2=M[2]
            if a<1 or b<1: continue
            total+=1
            bound=M2-b+1
            if a>bound: viol.append((M,t,a,b,M2,bound))
            elif a==bound: borderline.append((M,t,a,b,M2))
            else: strict+=1
print(f"  total genuine binding cuts checked: {total}")
print(f"  VIOLATIONS (a > M2-b+1, would make even shell-j>=1 divergent): {len(viol)}   {viol[:6]}")
print(f"  borderline (a = M2-b+1, j=0 needs theta): {len(borderline)}   e.g. {borderline[:5]}")
print(f"  strictly convergent already at j=0 (a < M2-b+1): {strict}")
print()

# ==================================================================
# The exact EXPONENT BUDGET on each shell j (charges ADD; tight iff t*+j binding).
#  Deeper comparator = redChain(t*+j) = (t*+j, M2, ...).  Its threshold = minAdm/2.
#  Freed corner charge = (a-j)(b-j)/2.  Need c' - (a-j)(b-j)/2 < minAdm(redChain(t*+j))/2,
#  i.e. c' < C_j/2  where C_j = (a-j)(b-j) + minAdm(redChain(t*+j)).
#  Confirm C_j >= minAdm(M) with 0 undershoots and locate the tight shells.
# ==================================================================
def R(t,tail): return minAdm((t,)+tail)
print("=== EXPONENT BUDGET: C_j = (a-j)(b-j)+minAdm(redChain(t*+j)) >= minAdm(M), tight shells ===")
bad=0; tights=[]
for rng_,length in [(range(1,7),4),(range(1,5),5)]:
    for M in product(rng_,repeat=length):
        best,cuts=binding_cuts(M); tail=M[2:]
        for t in cuts:
            a=M[0]-t; b=M[1]-t
            if a<1 or b<1: continue
            r=min(a,b)
            for j in range(0,r+1):
                Cj=(a-j)*(b-j)+R(t+j,tail)
                if Cj<best: bad+=1
print(f"  C_j < minAdm(M) undershoots: {bad}  (0 expected)")
print()
print("=== ANCHOR (3,3,3) t*=1 detailed shell budget ===")
M=(3,3,3); best=minAdm(M); tail=M[2:]; t=1; a=M[0]-t; b=M[1]-t; r=min(a,b)
print(f"  minAdm(3,3,3)={best}, carrierThreshold=½·{best}={best/2}")
for j in range(0,r+1):
    cor=(a-j)*(b-j); Rj=R(t+j,tail); Cj=cor+Rj
    conv_ok = (a-j) < (M[2]-b+1)  if j>=1 else "(j=0: borderline check a<M2-b+1)"
    print(f"  shell j={j}: freed corner {a-j}x{b-j}=charge {cor}/2={cor/2};  redChain(t+{j})=({t+j},{M[2]}) minAdm={Rj} charge {Rj/2};  C_j={Cj} (=½·{Cj}={Cj/2});  reduced-conv (a-j)<M2-b+1: {(a-j)<(M[2]-b+1) if j>=1 else 'n/a'}")
print(f"  M2-b+1 = {M[2]}-{b}+1 = {M[2]-b+1};  a={a} => j=0 is {'BORDERLINE (a=M2-b+1)' if a==M[2]-b+1 else 'strict'}")
