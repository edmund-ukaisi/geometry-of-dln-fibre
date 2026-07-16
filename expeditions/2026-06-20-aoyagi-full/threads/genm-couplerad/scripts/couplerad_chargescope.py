"""
couplerad_chargescope.py -- RESPONSE to the decorrelated Codex counterexamples.  Does the CHARGE lower
the coupled codim below FLOOR, and if so, is it INSIDE or OUTSIDE the binding-strict-shell + rankgen scope?

Codex (self-contained, my conclusion withheld) produced:
  CE#2  (6,8,5,5) u=5: charged C_5 = 18 < FLOOR = minAdm(5,5,5) = 19.  [my LP reproduces 18 -- Codex is right]
  CE#1  (4,4,10,3,10) u=3 (arity 5, rho=3<min(M2,n)): single-matrix model C_3^0=7 < minAdm(3,10,3,10)=9.
  (R)   u=rho=10,k=2,a=8,b=1: ray infimum -> -infty (charge non-integrable).

QUESTION: are these WITHIN the gate scope (u = t* + j, 1<=j<r strict binding shells; rankgen a+b<=rho-1;
arity 4 single deep matrix)?  If they are only at NON-binding cuts / arity>=5 / large-a, the gate stands and
the scope is load-bearing.  We SCAN the actual binding shells exactly.
"""
from fractions import Fraction as Fr
from functools import lru_cache
import itertools

@lru_cache(maxsize=None)
def minAdm(M):
    M=tuple(M)
    if len(M)==2: return M[0]*M[1]
    m0,m1=M[0],M[1]; rest=M[2:]
    return min((m0-t)*(m1-t)+minAdm((t,)+rest) for t in range(0,min(m0,m1)+1))

def binding_cut(M):
    m0,m1=M[0],M[1]; rest=M[2:]
    best=None;targ=None
    for t in range(0,min(m0,m1)+1):
        v=(m0-t)*(m1-t)+minAdm((t,)+rest)
        if best is None or v<best: best=v;targ=t
    return targ, min(m0-targ, m1-targ)

def beta(p,k): return [(p-k+1)+2*(k-i) for i in range(1,k+1)]
def gamma_hier_at(e,a,b,s):
    k=len(e); lo=max(0,b-s); hi=min(b,k); best=None
    for h in range(lo,hi+1):
        v=a*sum(e[:h]) - h*(s-b+h)
        if best is None or v>best: best=v
    return best if best is not None else 0
def Ck_LP(u,rho,k,p,a,b,charge=True):
    s=rho-k; bt=beta(p,k); P=u*(rho-k); best=None; half=Fr(1,2)
    for assign in itertools.product([0,1],repeat=k):
        e=[half if x==0 else Fr(0) for x in assign]; g=[Fr(0) if x==0 else half for x in assign]
        if any(e[i]>e[i+1] for i in range(k-1)): continue
        f=half; D=min([2*f]+[2*(e[i]+g[i]) for i in range(k)])
        if D<=0: continue
        gc=gamma_hier_at(e,a,b,s) if charge else 0
        N=sum(e[i]*bt[i] for i in range(k))+P*f+u*sum(g)-gc
        v=2*N/D
        if best is None or v<best: best=v
    return best

# ---- (1) Confirm CE#2 exactly (my LP reproduces Codex) ----
print("CE#2 (6,8,5,5) u=5, k=5: my charged LP =", Ck_LP(5,5,5,5,1,3,charge=True),
      " loss-only =", Ck_LP(5,5,5,5,1,3,charge=False), " FLOOR minAdm(5,5,5) =", minAdm((5,5,5)))
tstar,r = binding_cut((6,8,5,5))
print(f"   (6,8,5,5): t*={tstar} r={r}  => u=5 is {'a BINDING strict shell' if (5>tstar and 5<tstar+r) else 'NOT a binding strict shell (t*+j, 1<=j<r); OUTSIDE gate scope'}")

# ---- (2) SCAN arity-4: charged LP < FLOOR on the ACTUAL binding strict shells + rankgen? ----
print("\nSCAN arity-4 widths 1..8: charged C_k < FLOOR on BINDING strict shells (u=t*+j,1<=j<r) + rankgen a+b<=rho-1:")
viol=[]; viol_norankgen=[]; ncell=0; ncell_norankgen=0
for M in itertools.product(range(1,9),repeat=4):
    tstar,r=binding_cut(M); rho=min(M[2:]); n=M[-1]; exc=abs(M[2]-n)
    for j in range(1,r):                       # STRICT shell: 1<=j<r
        u=tstar+j; a=M[0]-u; b=M[1]-u
        if a<1 or b<1: continue
        floor=minAdm((u,)+tuple(M[2:]))
        for k in range(1,rho+1):
            p=k+exc; C=Ck_LP(u,rho,k,p,a,b,charge=True)
            rankgen = (a+b<=rho-1)
            if rankgen:
                ncell+=1
                if C<floor: viol.append((M,u,k,a,b,C,floor))
            else:
                ncell_norankgen+=1
                if C<floor: viol_norankgen.append((M,u,k,a,b,C,floor))
print(f"  IN scope (strict shell + rankgen): cells={ncell}  charged-below-floor={len(viol)}")
print(f"  strict shell but OUTSIDE rankgen (a+b>=rho):    cells={ncell_norankgen}  charged-below-floor={len(viol_norankgen)}")
for w in viol[:20]: print("    IN-SCOPE VIOLATION:", w)
for w in viol_norankgen[:12]: print("    (out-of-rankgen) below floor:", w)

# ---- (3) also test j==r (the shell endpoint) and j from 1..r inclusive, to see where charge bites ----
print("\nSCAN arity-4: including the shell ENDPOINT j=r (u=t*+r), rankgen enforced:")
viol_incl=[]; ncell_incl=0
for M in itertools.product(range(1,9),repeat=4):
    tstar,r=binding_cut(M); rho=min(M[2:]); n=M[-1]; exc=abs(M[2]-n)
    for j in range(1,r+1):                      # include endpoint j=r
        u=tstar+j; a=M[0]-u; b=M[1]-u
        if a<1 or b<1 or a+b>rho-1: continue
        floor=minAdm((u,)+tuple(M[2:]))
        for k in range(1,rho+1):
            p=k+exc; C=Ck_LP(u,rho,k,p,a,b,charge=True)
            ncell_incl+=1
            if C<floor: viol_incl.append((M,u,k,a,b,C,floor))
print(f"  cells={ncell_incl}  charged-below-floor={len(viol_incl)}")
for w in viol_incl[:20]: print("    VIOLATION (j=1..r):", w)

# ---- (4) WAIST partition (arch1build verdict check): M1 < deepTailMin (rho). ------------------------
# arch1build determined the WAIST case (M1 < deepTailMin) is NOT a separate branch -- the direct coupled
# route covers it.  Decorrelated check: does charge-domination (0 charged-below-floor on the binding
# strict shells + rankgen) STILL hold for waist configs?  If any waist cell undercuts -> reopens the branch.
print("\n" + "="*100)
print("WAIST CHECK: configs with M1 < deepTailMin(rho).  Charge C_k < FLOOR on binding strict shells")
print("(u=t*+j, 1<=j<r) + rankgen a+b<=rho-1, partitioned WAIST (M1<rho) vs non-waist (M1>=rho):")
print("="*100)
def scan_partition(width_ranges, label):
    cfg_w=set(); cw=0; vw=[]; cn=0; vn=[]
    for M in itertools.product(*width_ranges):
        tstar,r=binding_cut(M); rho=min(M[2:]); n=M[-1]; exc=abs(M[2]-n)
        waist = (M[1] < rho)
        for j in range(1,r):
            u=tstar+j; a=M[0]-u; b=M[1]-u
            if a<1 or b<1 or a+b>rho-1: continue
            floor=minAdm((u,)+tuple(M[2:]))
            for k in range(1,rho+1):
                C=Ck_LP(u,rho,k,k+exc,a,b,charge=True)
                if waist:
                    cw+=1; cfg_w.add(M)
                    if C<floor: vw.append((M,u,k,a,b,C,floor))
                else:
                    cn+=1
                    if C<floor: vn.append((M,u,k,a,b,C,floor))
    print(f"  [{label}] WAIST (M1<rho): configs-with-in-scope-cells={len(cfg_w)}  cells={cw}  charged-below-floor={len(vw)}")
    print(f"  [{label}] non-waist (M1>=rho):                              cells={cn}  charged-below-floor={len(vn)}")
    for w in vw[:20]: print("    WAIST VIOLATION:", w)
    return cw, len(vw)
cw1,vw1 = scan_partition([range(1,9)]*4, "widths 1..8")
# widen to guarantee deep-waist sampling: narrow M1, wide deep (M2,M3)
cw2,vw2 = scan_partition([range(2,8), range(1,6), range(4,12), range(4,12)], "M1 narrow, deep wide")
print(f"\nWAIST VERDICT: total waist in-scope cells checked = {cw1+cw2};  charged-below-floor = {vw1+vw2}")
print("  => 0 below-floor: WAIST covered by the coupled route, charge-domination holds, NO separate branch."
      if vw1+vw2==0 else "  => WAIST UNDERCUT -> reopens as a real branch. FLAG.")

print("\nExplicit waist witnesses (M1<rho), min_k charged C_k vs floor:")
for M in [(5,3,6,6),(6,2,5,5),(4,3,7,7),(6,4,8,8),(7,3,8,6)]:
    tstar,r=binding_cut(M); rho=min(M[2:]); n=M[-1]; exc=abs(M[2]-n)
    shells=[]
    for j in range(1,r):
        u=tstar+j; a=M[0]-u; b=M[1]-u
        if a<1 or b<1 or a+b>rho-1: continue
        floor=minAdm((u,)+tuple(M[2:]))
        mn=min(Ck_LP(u,rho,k,k+exc,a,b,charge=True) for k in range(1,rho+1))
        shells.append(f"u={u}(a={a},b={b}): min_k Ccharged={mn} floor={floor} ok={mn>=floor}")
    print(f"  M={M} waist(M1={M[1]}<rho={rho})={M[1]<rho} t*={tstar} r={r}: " +
          ("; ".join(shells) if shells else "no in-scope strict shell"))
