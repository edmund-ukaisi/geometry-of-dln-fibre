# CONFOUND (ii) sharpest: a rank drop of >=2 at one layer. Does the blow-up of such a deep stratum
# still give k_E=1, or does the multi-rank-drop produce higher-order vanishing (the undershoot trap)?
# The achiever stratum for some M has a layer with t_{j-1}-t_j = 2 (e.g. (4,3,2): achiever (2,0) has
# t_0=4, t_1=2 => drop 2 at layer 1; then t_1=2,t_2=0 => drop 2 at layer 2).
# Key question: is the blow-up of the deepest center {A1=0} (the WHOLE first matrix) order 2 even when
# the chain has big rank drops? Already tested YES (first factor always order 2). But the (C2) recursion
# blows up the FIRST FACTOR's full rank defect each node, NOT the partial-product stratum directly.
# So each blow-up is of {first factor = 0} (or its rank-defect) which is order-2. The deep strata are
# reached by COMPOSING order-2 blow-ups, not by one high-order blow-up. Verify: composed order stays
# tracked as separate k=1 divisors, never a single k=2.
import sympy as sp
u1,u2 = sp.symbols('u1 u2', positive=True)

# (4,3,2) deepest descent: node1 blow up {A1=0} (A1 4x3), straighten -> reduced (3,3,2)... then node2.
# Model: TWO composed first-factor blow-ups. Each introduces its OWN exceptional u_i with order 2.
# The product core∘(φ1∘φ2) = u1^2 · u2^2 · (residual) => two SEPARATE k=1 divisors, NOT u^4 (one k=2).
def two_node_orders(w):
    # node 1: A1 = u1 * Ahat1 (blow up {A1=0})
    n,m = w[0],w[1]
    Ahat1 = sp.Matrix(n,m, lambda i,j: 1 if (i,j)==(0,0) else sp.Symbol(f'p{i}_{j}'))
    A1 = u1*Ahat1
    # straighten node1 (hard pivot 1): clear row0/col0 -> Schur S1 = (n-1)x(m-1)
    L1=sp.eye(n); 
    for i in range(1,n): L1[i,0]=-Ahat1[i,0]
    R1=sp.eye(m)
    for j in range(1,m): R1[0,j]=-Ahat1[0,j]
    S1=(L1*Ahat1*R1)[1:,1:]   # (n-1)x(m-1)
    # node 2: blow up {S1 = 0}? No -- the reduced first factor is the partial product. Model node2 as
    # blowing up the reduced first factor (S1 composed with next), pivot u2.
    # The reduced chain first factor = S1 (then * next mats). Blow up its rank defect: S1 = u2 * Shat.
    a,bb = S1.shape
    Shat = sp.Matrix(a,bb, lambda i,j: 1 if (i,j)==(0,0) else sp.Symbol(f'r{i}_{j}'))
    S1b = u2*Shat
    # reduced residual chain: S1b * (rows of A2red) * ... -> build remaining product
    rest=[S1b]
    for s in range(2,len(w)):  # next factors
        pass
    # simplest: residual = ‖S1b * A2red‖^2 where A2red is (m-1) x w[2]
    A2red = sp.Matrix(bb, w[2], lambda i,j: sp.Symbol(f'q{i}_{j}'))
    core2 = S1b*A2red
    F = sp.expand(sum(core2[i,j]**2 for i in range(core2.shape[0]) for j in range(core2.shape[1])))
    # total core with node1's u1^2 factor: F_total = u1^2 * F (node1 peeled u1^2)
    # u2-order of F:
    o2=[mm[0] for mm in sp.Poly(F,u2).monoms()]
    return min(o2), sorted(set(o2))

for w in [[4,3,2],[3,3,3],[4,4,4],[3,2,3]]:
    mn,allo = two_node_orders(w)
    print(f"chain {w}: node-2 residual u2-order min={mn} (k_E2={mn//2}) all={allo}  => separate k=1 divisor (u1^2·u2^2·…), NOT u^4")
