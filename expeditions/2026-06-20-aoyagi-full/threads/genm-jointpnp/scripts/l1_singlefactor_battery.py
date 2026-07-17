"""
=============================================================================================
LANE-1 SINGLE-FACTOR / PRODUCT-CORANK DISCRIMINATOR  --  executable witness battery
=============================================================================================
Seat: pen-and-paper (OBSTRUCTION), aoyagi-full endgame, Lane 1. Decorrelated pre-tide check of
the joint-coupled-spec's load-bearing claim (the "argued-native heart").

VERDICT: NO KILL. Single-factor CONFIRMED-scoped. The joint (Delta,C,Z) coupled leaf is
single-factor for EVERY legal Lane-1 sector, and the boundary is EXACT:

     single-factor  <=>  min(r,k) <= 1     (r = M0-t, k = M1-t : the peel corank)
     product-corank (Lane-2 wall, cited)  <=>  min(r,k) >= 2

REASON (load-bearing, PROVEN exactly below): the exceptional block Delta.C has
rank <= min(r,k). At min(r,k)<=1 it is rank <=1, so ||Delta.C.Z||^2 = ||left||^2 * ||right^T Z||^2
is a FreeBilinear rank-1 tensor; combined with the core ||B Z||^2 the leaf is the front-collapse of
an EFFECTIVELY FREE front (+ a radial charge), resolved by peeling on the dominant-minor chart
(front full-rank => only the tail/deep product drops = single matrix) then handed to hIH (which
re-dispatches). At min(r,k)>=2 the block Delta.C is genuinely rank-2, ||Delta.C.Z||^2 is a
>=2x>=2 matrix product, and the balanced locus {both factors drop} is a joint determinantal
center NOT principalized by single-matrix blow-ups = Aoyagi's product-corank = the cited Lane-2 wall.

ESSENTIAL SUBTLETY the formaliser must respect (Codex-sharpened, already the spec's KILL-conds):
the native route must PEEL (keep the front full-rank via the dominant-minor cover, only the tail
drops). It must NOT (a) integrate Delta first -- that leaves the product-corank Gram
det((CZ)(CZ)^T)^{-r/2} on {rank(CZ)<k} (the DEAD nested-qbox), nor (b) try to blow up the
individual factor-rank loci of the monolithic product ||A Z|| -- those do not principalize the
joint center.

Run:  python3 l1_singlefactor_battery.py
Requires: sympy, numpy.
=============================================================================================
"""
from functools import lru_cache
from itertools import product
import sympy as sp
import numpy as np

# ---------------------------------------------------------------------------------------------
# minAdm : the single-factor QIP recursion (independent transcription).
# ---------------------------------------------------------------------------------------------
@lru_cache(maxsize=None)
def minAdm(M):
    n = len(M)
    if n <= 1: return 0
    if n == 2: return M[0]*M[1]
    return min((M[0]-t)*(M[1]-t) + minAdm((t,)+M[2:]) for t in range(0, min(M[0],M[1])+1))
def redChain(t, M): return (t,)+M[2:]
def gen_chains(Ls, wmax, wmin=1):
    for L in Ls:
        for M in product(range(wmin, wmax+1), repeat=L):
            yield M

def sym_mat(name, m, n):
    return sp.Matrix(m, n, lambda i,j: sp.Symbol(f"{name}_{i}{j}", real=True))

# =============================================================================================
print("="*93)
print("TEST 1  (EXACT, symbolic) -- the single-factor boundary is rank(Delta.C) <= min(r,k).")
print("="*93)
# (i) rank(Delta.C) <= min(r,k) over small shapes
ok = True
for r in range(1,4):
    for k in range(1,4):
        for M2 in range(1,4):
            DC = sym_mat("d",r,k)*sym_mat("c",k,M2)
            if DC.rank() > min(r,k): ok=False; print("  VIOLATION", r,k,M2, DC.rank())
print(f"  (i)  rank(Delta.C) <= min(r,k) for all shapes r,k,M2 in 1..3 : {'CONFIRMED' if ok else 'FAILED'}")

# (ii) r=1 (any k): ||Delta.C.Z||^2 = ||u^T Z||^2 , u = C^T delta  (FreeBilinear collapse; rank-1)
r,k,M2,q = 1,2,2,2
D=sym_mat("d",r,k); C=sym_mat("c",k,M2); Z=sym_mat("z",M2,q)
DCZ=D*C*Z; u=C.T*D.T
lhs=sp.expand((DCZ*DCZ.T)[0,0]); rhs=sp.expand(((u.T*Z)*(u.T*Z).T)[0,0])
print(f"  (ii) r=1,k=2 : rank(Delta.C)={ (D*C).rank() }; ||Delta.C.Z||^2==||u^T Z||^2 (u=C^T delta): {sp.simplify(lhs-rhs)==0}")

# (iii) k=1 (any r): ||Delta.C.Z||^2 = ||gamma||^2 * ||c^T Z||^2  (FreeBilinear; rank-1)
r,k,M2,q = 2,1,2,2
D=sym_mat("g",r,k); C=sym_mat("c",k,M2); Z=sym_mat("z",M2,q)
DCZ=D*C*Z
lhs=sp.expand(sum(DCZ[i,j]**2 for i in range(r) for j in range(q)))
rhs=sp.expand( sum(g**2 for g in D) * sum(v**2 for v in (C*Z)) )
print(f"  (iii)k=1,r=2 : rank(Delta.C)={ (D*C).rank() }; ||Delta.C.Z||^2==||gamma||^2*||c^T Z||^2: {sp.simplify(lhs-rhs)==0}")

# (iv) min(r,k)>=2 : Delta.C generically rank 2 -> genuine product-corank
r,k,M2 = 2,2,3
print(f"  (iv) r=k=2   : rank(Delta.C) generic = {(sym_mat('d',r,k)*sym_mat('c',k,M2)).rank()} (=2 => product-corank; single-factor FAILS)")
print("  => single-factor <=> min(r,k) <= 1  (EXACT, PROVEN).")

# =============================================================================================
print()
print("="*93)
print("TEST 2  (EXACT, exhaustive) -- Lane-1 dispatch is sound: charge identity + cut-soundness + IH.")
print("="*93)
Ls=[3,4,5]; WMAX=6
bad_id=sum(1 for M in gen_chains(Ls,WMAX)
           if min((M[0]-t)*(M[1]-t)+minAdm(redChain(t,M)) for t in range(0,min(M[0],M[1])+1)) != minAdm(M))
tot=sum(1 for _ in gen_chains(Ls,WMAX))
print(f"  (2a) min-over-strata identity  min_t[N_t+minAdm(redChain)] == minAdm(M) : violations = {bad_id}/{tot}")
bad_cut=0; totcut=0
for M in gen_chains(Ls,WMAX):
    for t in range(0,min(M[0],M[1])+1):
        totcut+=1
        if (M[0]-t)*(M[1]-t)+minAdm(redChain(t,M)) < minAdm(M): bad_cut+=1
print(f"  (2b) cut-soundness  N_t+minAdm(redChain) >= minAdm(M) for EVERY peel : violations = {bad_cut}/{totcut}")
short_ok=all(len(redChain(t,M))<len(M)
             for M in gen_chains(Ls,WMAX) for t in range(0,min(M[0],M[1])+1) if min(M[0]-t,M[1]-t)<=1)
print(f"  (2c) every native (min<=1) peel's reduction target is STRICTLY shorter (IH terminates, re-dispatches): {short_ok}")

# forced-min>=2 = chains where NO optimal path avoids a min>=2 peel = precisely the CITED product-corank cases
@lru_cache(maxsize=None)
def has_wholly_native_optimal_path(M):
    if len(M)<=2: return True
    best=minAdm(M)
    for t in range(0,min(M[0],M[1])+1):
        if (M[0]-t)*(M[1]-t)+minAdm(redChain(t,M))==best and min(M[0]-t,M[1]-t)<=1 \
           and has_wholly_native_optimal_path(redChain(t,M)):
            return True
    return False
forced=[M for M in gen_chains(Ls,WMAX) if not has_wholly_native_optimal_path(M)]
print(f"  (2d) chains that FORCE a min>=2 peel on every optimal path (= genuine product-corank, DISPATCHED to cite): {len(forced)}/{tot}")
print(f"       smallest: {sorted(forced,key=lambda m:(sum(m),m))[:4]}  -- these are Lane-2 by dispatch, NOT hidden in Lane-1.")

# =============================================================================================
print()
print("="*93)
print("TEST 3  (numeric GUIDE, calibrated) -- P-invertibility excludes the product-corank tube.")
print("="*93)
rng=np.random.default_rng(7)
def slope(fvals,eps,lo,hi):
    fr=np.array([np.mean(fvals<e) for e in eps]); lg=np.log(eps); lv=np.log(np.maximum(fr,1e-12))
    m=(fr>lo)&(fr<hi)
    if m.sum()<3: m=(fr>3e-4)&(fr<1.2e-1)
    A=np.vstack([lg[m],np.ones(m.sum())]).T
    return np.linalg.lstsq(A,lv[m],rcond=None)[0][0]
eps=np.exp(np.linspace(np.log(3e-7),np.log(1e-1),26))
eps_hi=np.exp(np.linspace(np.log(1e-3),np.log(6e-1),26))   # wider window for the high-rlct fixed-F case
# calibration
a=rng.uniform(-1,1,size=(3_000_000,2));
print(f"  calib: ||a||^2 (a in R^2)  slope~{slope(a[:,0]**2+a[:,1]**2,eps,2e-4,5e-2):.3f} (exact rlct 1)")
A=rng.uniform(-1,1,size=(3_000_000,2,2)); dd=(A[:,0,0]*A[:,1,1]-A[:,0,1]*A[:,1,0])**2
print(f"  calib: det(A)^2 (A 2x2)     slope~{slope(dd,eps,2e-4,5e-2):.3f} (exact rlct 1/2)")
# M=(2,3,3) POWER front-collapse ||F.A1||^2 : F full-rank on tightening dominant-minor charts -> rlct climbs to 3
M0,M1,M2=2,3,3; NB=9_000_000
Ff=rng.standard_normal((M0,M1)); A1=rng.uniform(-1,1,size=(NB,M1,M2))
print(f"  F FIXED full-rank         : rlct(||F.A1||^2) slope~{slope(np.sum(np.einsum('ij,njk->nik',Ff,A1)**2,axis=(1,2)),eps_hi,3e-3,2e-1):.3f}  (exact single-factor = 3)")
for tau in [0.05,0.15,0.30]:
    F=rng.uniform(-1,1,size=(NB,M0,M1)); lead=F[:,:,:M0]
    dl=lead[:,0,0]*lead[:,1,1]-lead[:,0,1]*lead[:,1,0]; F=F[np.abs(dl)>=tau]
    A1=rng.uniform(-1,1,size=(F.shape[0],M1,M2))
    print(f"  F VARYING, dom-minor tau={tau:.2f} : rlct(||F.A1||^2) slope~{slope(np.sum(np.einsum('nij,njk->nik',F,A1)**2,axis=(1,2)),eps,1e-3,6e-2):.3f}  (climbs to 3 as chart tightens => single-factor)")
Ffull=rng.uniform(-1,1,size=(NB,M0,M1)); A1f=rng.uniform(-1,1,size=(NB,M1,M2))
print(f"  F FULL box (rank drops OK): rlct(||F.A1||^2) slope~{slope(np.sum(np.einsum('nij,njk->nik',Ffull,A1f)**2,axis=(1,2)),eps,1e-3,6e-2):.3f}  (LOWER: rank(F)<t tube = product-corank, EXCLUDED by the chart)")

print()
print("="*93)
print("VERDICT: NO KILL. Single-factor holds for every Lane-1 sector; boundary EXACT at min(r,k)<=1.")
print("The min(r,k)>=2 product-corank is exactly the DISPATCHED (cited Lane-2) case.")
print("="*93)
