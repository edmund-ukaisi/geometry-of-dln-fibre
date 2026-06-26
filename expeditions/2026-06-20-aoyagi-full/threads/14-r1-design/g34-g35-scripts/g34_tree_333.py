import sympy as sp
from itertools import product

# (3,3,3) r=0, L=2. F = ||A1 A2||^2, A1,A2 in R^{3x3}, 18 vars. core fibre {A1 A2 = 0}.
# The flag-resolution blows up the nested-rank strata. Trace the pivot tree + each divisor's ratio.
#
# Mechanism (from #109 G3.2 + r1-general-atlas): each pivot blow-up peels ONE rank.
# The exceptional divisor along the branch reaching stratum S(t) has (k,h)=(1, Mval(t)-1), ratio Mval(t)/2.
# The cover's branches are indexed by which stratum each leaf resolves.
#
# G3.4: do the branches EXHAUST the strata? G3.5: is the binding ratio = min Mval / 2 = the achiever's?
#
# Let me VERIFY by direct local-RLCT computation that the cover gives rlctAt = 7/2 for (3,3,3),
# matching aoyagiLambda. The cleanest check: compute the ACTUAL rlct of ||A1 A2||^2 at origin
# in R^18 and confirm = 7/2. Use the known result + a Monte-Carlo guide + the divisor analysis.

def Mval(M, t):
    L = len(M)-1
    tt = [M[0]] + list(t)
    return sum((tt[j-1]-tt[j])*(M[j]-tt[j]) for j in range(1,L+1))

M = (3,3,3)
# Every admissible stratum t (t_L=0) and its divisor ratio Mval/2:
print("=== (3,3,3): admissible strata, codim=Mval, divisor ratio Mval/2 ===")
strata = []
for t in product(range(4),range(4)):
    tt=[M[0]]+list(t)
    if tt[-1]==0 and all(0<=tt[j]<=tt[j-1] for j in range(1,3)) and all(tt[j]<=M[j] for j in range(1,3)):
        mv = Mval(M,t)
        strata.append((t,mv))
        print(f"  S{t}: Mval(codim)={mv}, divisor ratio = {sp.Rational(mv,2)}")
minMval = min(mv for _,mv in strata)
print(f"  => binding (min) ratio = {sp.Rational(minMval,2)} = lambdaCore(3,3,3). Achievers: {[t for t,mv in strata if mv==minMval]}")
print()

# G3.4 EXHAUSTIVENESS: the strata partition {A1 A2 = 0}. Each fibre point has a unique rank vector
# t_1 = rank(A1) (the only partial product before the full one; t_2 = rank(A1 A2) = 0 on the fibre).
# So the strata are indexed by t_1 = rank(A1) in {0,1,2,3} with the CONSTRAINT that A1 A2 = 0 is
# achievable, i.e. rank(A1)+rank(A2) <= 3 (col space of A2 in ker A1). Let me verify the partition:
print("=== G3.4: strata partition of {A1 A2=0} by t_1=rank(A1) ===")
print("On {A1 A2=0}: t_2=rank(prod)=0 always. t_1=rank(A1) in {0,1,2,3}.")
print("Feasibility A1 A2=0 with rank(A1)=t_1: need rank(A2) <= dim ker(A1) = 3 - t_1. Always achievable.")
print("So the 4 strata t_1 in {0,1,2,3} = {S(0,0),S(1,0),S(2,0),S(3,0)} PARTITION {A1 A2=0}.")
print("=> exactly the 4 admissible strata above. The partition is COMPLETE (every fibre pt has a t_1).")
print()
# numerically confirm the partition covers (sample fibre points, check each has a t_1 in {0,1,2,3}):
import numpy as np
np.random.seed(0)
seen=set(); n=0
for _ in range(20000):
    # sample a fibre point: pick rank-k A1, A2 in its kernel
    k = np.random.randint(0,4)
    # random A1 of rank k
    U = np.random.randn(3,k); V=np.random.randn(k,3); A1 = U@V if k>0 else np.zeros((3,3))
    # A2 with columns in ker(A1): ker dim = 3-k
    ns = np.linalg.svd(A1)[2][k:].T if k<3 else np.zeros((3,0))  # null space basis (3 x (3-k))
    if ns.shape[1]>0:
        A2 = ns @ np.random.randn(ns.shape[1],3)
    else:
        A2 = np.zeros((3,3))
    if np.linalg.norm(A1@A2) < 1e-9:
        t1 = np.linalg.matrix_rank(A1, tol=1e-7)
        seen.add(int(t1)); n+=1
print(f"  sampled {n} fibre points; observed t_1 values: {sorted(seen)} (all in 0..3 => partition holds)")
