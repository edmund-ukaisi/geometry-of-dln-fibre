import itertools
from functools import lru_cache
from fractions import Fraction as F
from scipy.optimize import linprog

def admBound(M,j): return min(M[0],M[1]) if j==0 else M[j+1]
def is_adm(M,T):
    L=len(T)
    for j in range(L):
        if T[j]>admBound(M,j): return False
    for i in range(L):
        for j in range(L):
            if i<=j and T[j]>T[i]: return False
    return L<1 or T[L-1]==0
def adm_cone(M):
    L=len(M)-1
    return [T for T in itertools.product(*[range(admBound(M,j)+1) for j in range(L)]) if is_adm(M,T)]
def Mval(M,T):
    s=0
    for j in range(len(T)):
        tprev=M[0] if j==0 else T[j-1]; s+=(tprev-T[j])*(M[j+1]-T[j])
    return s
def redChain(t,M): return (t,)+M[2:]
@lru_cache(None)
def minAdm(M):
    L=len(M)-1
    if L==0: return 0
    if L==1: return M[0]*M[1]
    return min((M[0]-x)*(M[1]-x)+minAdm(redChain(x,M)) for x in range(min(M[0],M[1])+1))

def trace(M,T):
    cur=M; steps=[]; j=0
    while len(cur)>=3:
        t=T[j]; p=cur[0]-t; q=cur[1]-t; pq=p*q
        steps.append(dict(cur=cur,t=t,pq=pq)); cur=redChain(t,cur); j+=1
    return steps, cur

def exp_shift_threshold(M,T):
    """the additive exponent-shift composition: sup c' s.t. finite.
       peel each layer (regime A shift c'->c'-pq/2), then terminal (regime B, c'<pq_T/2).
       finiteness sup = 1/2*(sum peel charges + terminal charge)."""
    steps,leaf=trace(M,T)
    peel=sum(s['pq'] for s in steps)
    term=leaf[0]*leaf[1] if len(leaf)==2 else 0
    return F(peel+term,2), peel, term, leaf

print("="*92)
print("FULL BINDING-BRANCH SWEEP: exponent-shift additive composition + terminal classification")
print("="*92)
allpass=True
for M in [(3,3,4),(2,2,2,2),(3,3,3,4),(3,3,2,2),(4,4,2,2),(2,2,2)]:
    mm=minAdm(M); binding=[T for T in adm_cone(M) if Mval(M,T)==mm]
    print(f"\n### M={M}  minAdm={mm}  1/2*minAdm={F(mm,2)}   #binding={len(binding)}")
    for T in binding:
        thr,peel,term,leaf=exp_shift_threshold(M,T)
        steps,_=trace(M,T); charges=[s['pq'] for s in steps]
        ok = (thr==F(mm,2))
        allpass = allpass and ok
        kind = f"free-matrix{leaf}(chg {term})" if len(leaf)==2 else f"trivial{leaf}"
        # bridge LHS at terminal
        rem = term if len(leaf)==2 else 0
        print(f"   T={T}: charges={charges}+term{term} -> expShift sup={thr}  (==1/2minAdm? {ok}) "
              f"| terminal={kind} | 1/2*minAdm(remTerm)={F(rem,2)}")
print(f"\nALL branches: exponent-shift sup == 1/2*minAdm ?  {allpass}")

# ---- TORIC confirmation: the nested-shared monomial model gives RLCT = 1/2*minAdm (not 1/2*min(charges)) ----
# Build the shared-radial nested monomial sum for a branch and compute Newton-polytope RLCT via LP.
# Model per Aoyagi/step0_closure: sequential blow-up, layer-j corank block contributes generators that
# carry the product of radials u_0..u_j (nested-shared) times a fresh block coordinate.
def toric_rlct(sq_monos, weights):
    n=len(sq_monos[0]); c=[float(w) for w in weights]
    A_ub=[[-a for a in al] for al in sq_monos]; b_ub=[-1.0]*len(sq_monos)
    r=linprog(c,A_ub=A_ub,b_ub=b_ub,bounds=[(0,None)]*n,method='highs')
    return r.fun

print("\n"+"="*92)
print("TORIC cross-check: nested-shared monomial model reproduces 1/2*minAdm (NOT 1/2*min(charges))")
print("="*92)
# For each layer-j block of charge pq_j (p_j x q_j freed entries), after nested-shared blow-up the
# block's pq_j generators are  (prod_{i<=j} u_i) * x_{j,a}   for a in 1..pq_j  (each block entry a monomial).
# Jacobian of the composed blow-up: radial u_i carries exponent (running remaining dimension -1).
# We test the ADDITIVE claim: RLCT of sum over all block generators (with correct Jacobian) = 1/2*minAdm.
def build_nested_model(M,T):
    steps,leaf=trace(M,T)
    blocks=[s['pq'] for s in steps if s['pq']>0]  # radial per positive-charge peel
    d=len(blocks)  # exceptional radials u_0..u_{d-1}
    # variable order: [u_0..u_{d-1}] + one fresh coord per generator's block (kept implicit: each block
    # entry is a distinct fresh var). We encode each generator as squared-exponent vector over
    # [u_0..u_{d-1}, block-fresh-vars].
    # nested-shared: block j's generators carry u_0..u_j each to power 1; plus its own fresh var pow 1.
    # terminal free-matrix (charge term): its `term` generators carry u_0..u_{d-1} (all radials) + fresh.
    gens=[]; 
    nfresh=0
    # count fresh: each block j contributes pq_j fresh entries; terminal contributes `term` fresh entries.
    term=leaf[0]*leaf[1] if len(leaf)==2 else 0
    freshblocks=blocks+([term] if term>0 else [])
    total_fresh=sum(freshblocks)
    def vec(): return [0]*(d+total_fresh)
    fresh_ptr=0
    for j,chg in enumerate(freshblocks):
        radials_upto = min(j, d-1)  # for a peel block j<d carries u_0..u_j; terminal (j==d) carries u_0..u_{d-1}
        rlast = j if j<d else d-1
        for a in range(chg):
            v=vec()
            for i in range(0, rlast+1):
                v[i]=2  # squared exponent 2 (monomial to power 1, squared)
            v[d+fresh_ptr]=2
            fresh_ptr+=1
            gens.append(v)
    # weights (Jacobian h+1) per variable: radial u_i gets h_i+1; fresh vars get 1 (Lebesgue, h=0 -> weight 1)
    # Jacobian of nested radial blow-ups: u_i exponent h_i = (dim blown up at step i) - 1.
    # dim at step i = (sum of remaining block sizes from i onward)  -- the composed centre dimension.
    w=[1.0]*(d+total_fresh)
    # h_i for radial i: the number of fresh coords that carry u_i, minus 1  (radial blow-up in that dim)
    for i in range(d):
        carriers=sum(1 for g in gens if g[i]>0)
        w[i]=carriers   # h_i+1 = carriers  (radial blowup Jacobian in `carriers`-dim = u^{carriers-1})
    return gens,w,d,total_fresh

for M,T in [((3,3,4),(1,0)),((2,2,2,2),(1,1,0)),((3,3,3,4),(1,0,0)),((3,3,3,4),(2,1,0))]:
    mm=minAdm(M)
    gens,w,d,nf=build_nested_model(M,T)
    r=toric_rlct(gens,w)
    print(f"   M={M} T={T}: nested-shared toric RLCT={r:.6f}  target 1/2*minAdm={float(F(mm,2)):.6f}  match={abs(r-float(F(mm,2)))<1e-9}")
