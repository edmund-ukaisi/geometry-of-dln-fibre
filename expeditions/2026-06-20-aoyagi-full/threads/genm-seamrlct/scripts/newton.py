import numpy as np, itertools
from fractions import Fraction as Fr
import scipy.optimize as opt
# rlct of a sum of squared monomials  f = sum_a  x^{2 a}  (each 'a' an exponent vector, the monomial squared)
# via Newton polyhedron: rlct = max t s.t. t*(1,..,1) NOT in interior... standard LP:
#   rlct = min over the polyhedron of the "distance"; for f=sum x^{2a}, Gamma+ = conv{2a}+R^n_+.
#   rlct = 1 / t0 where t0 = min{ t : (t,..,t) in Gamma+ } = max over facet-normals.
#   Equivalent LP: t0 = min_{lambda>=0, sum over verts=1} max_i ... ; simplest: LP
#   t0 = min t  s.t.  (t,...,t) = sum_k w_k*(2a_k) + s,  s>=0, w>=0, sum w_k =? NO -- Gamma+ = conv(verts)+R+^n
#   (t..t) in Gamma+  <=>  exists convex comb c of verts with c <= (t..t) componentwise.
#   t0 = min over convex combos c of verts of ( max_i c_i ).  => LP: min M s.t. c=conv comb, c_i<=M.
def t0_of(verts):
    verts=[np.array(v,dtype=float)*2 for v in verts]   # squared -> 2*exponent
    n=len(verts[0]); K=len(verts)
    # variables: w_1..w_K (>=0, sum=1), M ; minimize M s.t. sum_k w_k verts[k][i] <= M  all i
    # LP: min c^T z, z=(w..,M)
    c=np.zeros(K+1); c[-1]=1.0
    A_ub=[]; b_ub=[]
    for i in range(n):
        row=np.zeros(K+1)
        for k in range(K): row[k]=verts[k][i]
        row[-1]=-1.0
        A_ub.append(row); b_ub.append(0.0)
    A_eq=[np.concatenate([np.ones(K),[0.0]])]; b_eq=[1.0]
    bounds=[(0,None)]*K+[(None,None)]
    res=opt.linprog(c,A_ub=np.array(A_ub),b_ub=np.array(b_ub),A_eq=np.array(A_eq),b_eq=np.array(b_eq),bounds=bounds)
    return res.fun
def rlct_monomial(edges,n):
    # each edge (i,j) -> monomial x_i x_j ; squared. plus we can add pure squares.
    verts=[]
    for e in edges:
        v=[0]*n
        for idx in e: v[idx]+=1
        verts.append(v)
    t0=t0_of(verts)
    return 1.0/t0, t0
def codim_edges(edges,n):
    # zero set of sum (x_e)^2 = intersection {all edge-monomials=0}; codim = min vertex cover size
    # brute force min hitting set
    best=n+1
    for r in range(n+1):
        for S in itertools.combinations(range(n),r):
            Sset=set(S)
            if all(any(i in Sset for i in e) for e in edges): best=min(best,r); break
        if best<=r: break
    return best

cases={
 "path P2 (e1e2)": ([(0,1)],2),
 "path P3 (e1e2,e2e3)": ([(0,1),(1,2)],3),
 "path P4": ([(0,1),(1,2),(2,3)],4),
 "star S3 (e1e2,e1e3,e1e4)": ([(0,1),(0,2),(0,3)],4),
 "tree (e1e2,e2e3,e2e4)": ([(0,1),(1,2),(1,3)],4),
 "TRIANGLE C3 (odd cycle)": ([(0,1),(1,2),(2,0)],3),
 "square C4 (even cycle)": ([(0,1),(1,2),(2,3),(3,0)],4),
 "pentagon C5 (odd cycle)": ([(0,1),(1,2),(2,3),(3,4),(4,0)],5),
 "K4 (complete, has odd cycles)": ([(0,1),(0,2),(0,3),(1,2),(1,3),(2,3)],4),
}
print(f"{'structure':>34} {'rlct':>7} {'codim':>6} {'codim/2':>8} {'deficit?':>9}")
for name,(edges,n) in cases.items():
    rl,t0=rlct_monomial(edges,n); cod=codim_edges(edges,n)
    df="DEFICIT" if rl < cod/2-1e-6 else "benign"
    print(f"{name:>34} {rl:>7.3f} {cod:>6} {cod/2:>8.2f} {df:>9}")
