import sympy as sp
from itertools import product

# Mval(M,t) for a chain M=(M^1,...,M^{L+1}), rank vector t=(t_1,...,t_L) (t_0=M^1, but here B=0 core).
# Aoyagi block sizes (from r1-general-atlas R1.3): residual blocks
#   block_1 size (M^1 - t_1)(M^2 - t_1)
#   block_j size (t_{j-1} - t_j)(M^{j+1} - t_j)  for j=2..L
# Mval(t) = sum of block sizes. Admissible: weakly DECREASING t_1>=t_2>=...>=t_L, t_L=0 (on {prod=0}),
#   and t_j <= min(M^j-?,...) feasibility: 0<=t_j, t_j<=M^{j+1}, t_j<=t_{j-1}, block sizes >=0.
# Actually the rank vector t_j = rank of the partial product C^(1)...C^(j); on {prod=0}, t_L=0.
# Feasibility (rank pattern realizable): t_j <= min(t_{j-1}, M^{j+1}) with t_0 = M^1.
def Mval(M, t):
    L = len(M)-1
    # t = (t_1,...,t_L); prepend t_0 = M[0]
    tt = [M[0]] + list(t)
    total = 0
    # block_1: (M^1 - t_1)(M^2 - t_1)  -- in 1-indexed M, M^1=M[0], M^2=M[1]
    # general per Aoyagi: sum over j=1..L of (t_{j-1}-t_j)(M^{j+1}-t_j) with t_0=M^1
    # Wait: block_1 uses (M^1 - t_1) not (t_0 - t_1)=(M^1 - t_1). Same. Good, uniform:
    for j in range(1, L+1):
        total += (tt[j-1] - tt[j])*(M[j] - tt[j])
    return total

def admissible(M, t):
    L = len(M)-1
    tt = [M[0]] + list(t)
    if tt[-1] != 0:  # t_L = 0 on {prod=0}
        return False
    for j in range(1, L+1):
        if not (0 <= tt[j] <= tt[j-1]):  # weakly decreasing, nonneg
            return False
        if tt[j] > M[j]:  # t_j <= M^{j+1} (M[j] is M^{j+1} 0-indexed)
            return False
    return True

for M in [(2,2,2),(3,3,3),(3,2,3),(4,3,2),(2,3,2)]:
    L = len(M)-1
    adm = []
    for t in product(*[range(M[0]+1)]*L):
        if admissible(M,t):
            adm.append((t, Mval(M,t)))
    mvals = [m for _,m in adm]
    minMval = min(mvals)
    achievers = [t for t,m in adm if m==minMval]
    print(f"M={M}: Adm strata (t -> Mval):")
    for t,m in sorted(adm):
        star = "  <-- ACHIEVER (min)" if m==minMval else ""
        print(f"    t={t}  Mval={m}{star}")
    print(f"  min_Adm Mval = {minMval}, lambdaCore = {sp.Rational(minMval,2)}, achievers={achievers}")
    print()
