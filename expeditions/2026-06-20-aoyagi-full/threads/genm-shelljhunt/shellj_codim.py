import numpy as np, sympy as sp
from itertools import product

# ---------- exact codim of {B W = 0}, stratified by r = rank B ----------
# B: M0 x M1, W: M1 x M2.  On the deepest {BW=0} point with rank B = r,
# codim Z_r = (M0-r)(M1-r) + r*M2   (thresholdhunt / Aoyagi determinantal formula)
def codim_r(M0,M1,M2,r): return (M0-r)*(M1-r) + r*M2
def minAdm3(M0,M1,M2):
    rs=range(0,min(M0,M1)+1); vals=[(r,codim_r(M0,M1,M2,r)) for r in rs]
    m=min(v for _,v in vals); arg=[r for r,v in vals if v==m]
    return m, arg, dict(vals)

for (M0,M1,M2) in [(3,3,3),(4,4,4),(6,6,6)]:
    m,arg,tab=minAdm3(M0,M1,M2)
    print(f"chain {(M0,M1,M2)}: minAdm={m} argmin r*={arg}  codim_r table={tab}")

print("\n--- EXACT rank verification of codim_r via smooth-point Jacobian (over Q) ---")
def jac_rank_at_smooth_point(M0,M1,M2,r):
    # Build B0 (rank r), W0 with col(W0) subset ker(B0), rank W0 = min(M1-r, M2)  (deepest)
    # choose rational generic-ish entries; verify rank of dPhi(dB,dW)=dB*W0 + B0*dW  = codim.
    import random
    random.seed(0)
    B0=sp.zeros(M0,M1)
    for i in range(r):
        for k in range(M1): B0[i,k]=sp.Integer(random.randint(-3,3))
    # ensure rank r: keep first r rows generic, rest zero -> rank <= r; make exactly r
    # W0: columns in ker(B0). ker(B0) has dim M1 - r (B0 has r nonzero rows).
    ker=B0.nullspace()  # list of M1-vectors
    W0=sp.zeros(M1,M2)
    # fill first len(ker) columns of W0 with ker basis (rank W0 = min(M1-r,M2) generically)
    ncols=min(len(ker),M2)
    for c in range(ncols):
        for k in range(M1): W0[k,c]=ker[c][k]
    # differential rank: Phi(B,W)=B*W, dPhi = dB*W0 + B0*dW, linear map R^{M0*M1+M1*M2}->R^{M0*M2}
    dB=sp.Matrix(M0,M1, lambda i,j: sp.Symbol(f"b_{i}_{j}"))
    dW=sp.Matrix(M1,M2, lambda i,j: sp.Symbol(f"w_{i}_{j}"))
    D=dB*W0+B0*dW
    vars_=list(dB)+list(dW)
    Jm=sp.Matrix([[sp.diff(D[i,j],v) for v in vars_] for i in range(M0) for j in range(M2)])
    return Jm.rank(), r
for (M0,M1,M2) in [(3,3,3),(4,4,4),(6,6,6)]:
    for r in range(0,min(M0,M1)+1):
        rk,_=jac_rank_at_smooth_point(M0,M1,M2,r)
        print(f"  {(M0,M1,M2)} r={r}: Jacobian rank(codim)={rk}  formula (M0-r)(M1-r)+rM2={codim_r(M0,M1,M2,r)}  match={rk==codim_r(M0,M1,M2,r)}")
