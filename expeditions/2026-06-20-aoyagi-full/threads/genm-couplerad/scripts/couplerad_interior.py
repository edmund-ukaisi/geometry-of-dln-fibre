import numpy as np
from functools import lru_cache
np.random.seed(0)

# ---- minAdm (fetched formula) ----
import sys
sys.setrecursionlimit(10000)
@lru_cache(maxsize=None)
def minAdm(M):
    if len(M) == 1:
        return 0
    m0, m1, *rest = M
    rest = tuple(rest)
    return min((m0 - t) * (m1 - t) + minAdm((t,) + rest) for t in range(0, min(m0, m1) + 1))

def deepTailMin(M):
    return min(M[2:]) if len(M) > 2 else M[-1]

# ======================================================================
# PART 1: structural verification of the RLCT threshold for I_loss
#   f(P,B12,C) = frobSq([P|B12].S) + frobSq(C.K),  S=[Qinl;Qb], K=Qinl.Pi
#   claim: as a PSD quadratic in vec(P,B12,C), rank(H) = u*r_stack + a*r_K,
#          r_stack = rank(S) = min(M1, rho_d),  r_K = rank(K) = r_stack - b.
#   RLCT threshold: int_box f^{-q} < inf  iff  2q < rank(H).
# ======================================================================
def build_QinlQb(u, b, M2, n, rho_d):
    # Z_deep: M2 x n, rank rho_d ; z0: u x M2 ; A_cor: b x M2
    Z = np.random.randn(M2, rho_d) @ np.random.randn(rho_d, n)   # rank rho_d (generic)
    z0 = np.random.randn(u, M2)
    Acor = np.random.randn(b, M2)
    Qinl = z0 @ Z          # u x n
    Qb   = Acor @ Z        # b x n
    return Qinl, Qb, Z

def frob2(X):
    return float(np.sum(X*X))

def loss_rank_and_decouple(u, a, b, M1, M2, n, rho_d):
    Qinl, Qb, Z = build_QinlQb(u, b, M2, n, rho_d)
    # Pi = I - Qb^T (Qb Qb^T)^-1 Qb   (proj off rowspace(Qb))
    G = Qb @ Qb.T
    Pi = np.eye(n) - Qb.T @ np.linalg.pinv(G) @ Qb
    K = Qinl @ Pi          # u x n
    S = np.vstack([Qinl, Qb])   # (u+b) x n
    r_stack = np.linalg.matrix_rank(S, tol=1e-8)
    r_K = np.linalg.matrix_rank(K, tol=1e-8)
    # decoupling check: E_tr = frobSq(C.Qtilde.Pi) indep of P,B12 ?  Qtilde=Qinl+Pinv B12 Qb
    P = np.random.randn(u,u); B12 = np.random.randn(u,b); C = np.random.randn(a,u)
    Pinv = np.linalg.inv(P)
    Qtilde = Qinl + Pinv @ B12 @ Qb
    E_tr_full = frob2(C @ Qtilde @ Pi)
    E_tr_simp = frob2(C @ Qinl @ Pi)
    # E_top = frobSq(P Qinl + B12 Qb) vs frobSq([P|B12].S)
    E_top_a = frob2(P @ Qinl + B12 @ Qb)
    E_top_b = frob2(np.hstack([P,B12]) @ S)
    # rank of the loss quadratic H via linear maps: rank = u*rank(S) + a*rank(K)
    rankH_pred = u*r_stack + a*r_K
    return dict(r_stack=r_stack, r_K=r_K, r_stack_formula=min(M1,rho_d),
                r_K_formula=min(M1,rho_d)-b, rankH_pred=rankH_pred,
                decouple_err=abs(E_tr_full-E_tr_simp), etop_err=abs(E_top_a-E_top_b))

print("="*70)
print("PART 1: RLCT-threshold structure (r_stack, r_K, rank H) + decoupling")
print("="*70)
# use a config with M1<=rho_d and one with M1>rho_d
for (u,a,b,M1,M2,n,rho_d,tag) in [
    (3,1,1,4,4,4,4,"(4,4,4,4)@u3: M1=4=rho_d boundary"),
    (2,1,2,4,5,4,4,"(3,4,5,4)@u2: a=1 b=2, M1=4=rho_d"),
    (2,3,2,5,6,6,6,"M1=5<rho_d=6 (full ranks)"),
    (2,2,4,6,6,3,3,"M1=6>rho_d=3 (deficient)"),
]:
    r = loss_rank_and_decouple(u,a,b,M1,M2,n,rho_d)
    ok_rs = (r['r_stack']==r['r_stack_formula'])
    ok_rk = (r['r_K']==r['r_K_formula'])
    print(f"\n{tag}")
    print(f"  r_stack={r['r_stack']} (formula min(M1,rho)={r['r_stack_formula']}) {'OK' if ok_rs else 'MISMATCH'}"
          f" | r_K={r['r_K']} (formula r_stack-b={r['r_K_formula']}) {'OK' if ok_rk else 'MISMATCH'}")
    print(f"  rank(H)=u*r_stack+a*r_K = {r['rankH_pred']}  -> RLCT threshold 2q < {r['rankH_pred']}, i.e. c' < M0*r_stack/2")
    print(f"  decouple err (E_tr P,B12-indep)={r['decouple_err']:.2e}  E_top form err={r['etop_err']:.2e}")

# ======================================================================
# PART 2: the KEY inequality  minAdm(M) <= M0 * min(M1, deepTailMin)
#   (uniform I_loss bound <=> this, since c' < 1/2 minAdm M must imply c' < M0*r_stack/2)
# ======================================================================
print("\n"+"="*70)
print("PART 2: minAdm(M) <= M0 * min(M1, deepTailMin) ?   [interior cells exist: a+b<=rho_d for some u]")
print("="*70)

def check(M):
    ma = minAdm(M)
    rho = deepTailMin(M)
    rhs = M[0]*min(M[1], rho)
    # does an interior cell exist? interior u: a+b<=rho, a=M0-u,b=M1-u, u in [0,min(M0,M1)]
    interior_us = [u for u in range(0, min(M[0],M[1])+1) if (M[0]-u)+(M[1]-u) <= rho]
    return ma, rhs, (ma<=rhs), interior_us

witnesses = [(4,4,4,4),(3,4,5,4),(3,3,3,4),(2,3,2,2),(4,4,4,4),(5,5,5,5,5),(3,4,5,6,7)]
print("\nDispatch/named witnesses:")
for M in witnesses:
    ma,rhs,ok,ius = check(M)
    print(f"  M={M}: minAdm={ma}  M0*min(M1,rho)={rhs}  {'OK  ma<=rhs' if ok else '*** FAIL ma>rhs ***'}  interior_u={ius}")

print("\nSCAN arity 3,4,5 widths 2..7 (report ALL failures of minAdm<=M0*min(M1,rho)):")
import itertools
fails=0; total=0; fails_interior=0; tot_interior=0
for arity in (3,4,5):
    for M in itertools.product(range(2,8), repeat=arity):
        ma,rhs,ok,ius = check(M)
        total+=1
        if not ok:
            fails+=1
            if len(ius)>0:
                fails_interior+=1
                if fails_interior<=15:
                    print(f"  FAIL (interior exists) M={M}: minAdm={ma} > M0*min(M1,rho)={rhs}  interior_u={ius}")
        if len(ius)>0: tot_interior+=1
print(f"\n  total={total}  all-fails={fails}  interior-cell-fails={fails_interior} (of {tot_interior} with interior cells)")
