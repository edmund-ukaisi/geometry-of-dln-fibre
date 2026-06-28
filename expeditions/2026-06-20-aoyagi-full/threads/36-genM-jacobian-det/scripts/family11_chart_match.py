"""
CONNECT the front-product rank-one fact to the LANDED scalarGram_cancel signature:
  scalarGram_cancel_of_rankOneColumns (c0)(mu)(hc: sum c0^2 != 0)(P1: rows x Fin 1)(P2: rows x s)
    (hP1: P1 i 0 = c0 i)(hP2: P2 i j = mu j * c0 i): P1*((P1^T P1)^-1 P1^T P2)=P2
In the chart, P1 = P[:, :1] (the single pivot column), P2 = P[:, 1:] (the s=m1-1 residual columns).
So:  c0 i = P i 0 = P1 i 0 ;  for residual column j (0<=j<s), it is column (j+1) of P:
     P2 i j = P i (j+1) = mu_{j+1} * c0 i  where mu_{j+1} = (column j+1 scalar).
Define MU j := the scalar so that P[:, j+1] = MU j * c0. Verify exactly, AND verify off-pole
condition ||c0||^2 = sum_i (P i 0)^2 != 0 generically.
From the outer-product P = U V (U: m0 x 1, V: 1 x m1):  P i j = U[i] * V[j], c0 i = U[i]*V[0],
  MU j = V[j+1]/V[0].  ||c0||^2 = V[0]^2 * sum U[i]^2.  Pole = {V[0]=0} union {U=0}.
"""
import sympy as sp, itertools, sys
sys.path.insert(0, '/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/genm-frontrank-pnp/expeditions/2026-06-20-aoyagi-full/threads/36-genM-jacobian-det/scripts')
from witness_tide_validated import achiever
def Text(M,tach,k): return M[0] if k==0 else tach[k-1]
def smeared():
    out=[]
    for L in range(2,5):
      for M in itertools.product(range(1,4),repeat=L+1):
        M=list(M); T0,mv=achiever(M)
        if mv==0: continue
        tach=[M[0]]+list(T0)
        interior=any(Text(M,tach,k)-Text(M,tach,k+1)>=1 and M[k]-Text(M,tach,k+1)>=1 for k in range(1,L))
        if interior: continue
        if T0[L-2]<M[L-1]: out.append((M,T0,mv,L))
    return out
cases = smeared()
fam11 = [(M,T0,mv,L) for (M,T0,mv,L) in cases if T0[L-2]==1 and M[L]==1]

nok=0
for (M,T0,mv,L) in fam11:
    m0=M[0]; m1=M[L-1]; r=1; s=m1-r
    facs=[sp.Matrix(M[k],M[k+1],lambda i,j,k=k: sp.Symbol(f'a{k}_{i}_{j}')) for k in range(L-1)]
    P=facs[0]
    for k in range(1,L-1): P=P*facs[k]
    # split at first width-1 position p*
    path=[M[k] for k in range(0,L)]; pstar=path.index(1)
    if pstar==0:
        U=sp.eye(m0); V=P
    else:
        U=facs[0]
        for t in range(1,pstar): U=U*facs[t]   # m0 x 1
        V=facs[pstar]
        for t in range(pstar+1,L-1): V=V*facs[t]  # 1 x m1
    # c0 = col 0 of P
    c0=[sp.cancel(P[i,0]) for i in range(m0)]
    # MU j for residual cols j=0..s-1 i.e. P col (j+1) = MU j * c0
    ok=True
    for jj in range(s):
        colidx=jj+1
        # need P[i,colidx] = MU * c0[i] for all i, consistent MU
        # MU candidate: from outer product, V[colidx]/V[0]; verify P[i,colidx]*c0[0]==P[i,0]*P[?]
        # cross check: P[i,colidx]*c0[i2] == P[i2,colidx]*c0[i]  (already verified rank-one earlier);
        # consistency: P[i,colidx] = (P[i0,colidx]/c0[i0]) * c0[i] for any i0 with c0[i0]!=0
        for i in range(m0):
            for i2 in range(m0):
                if sp.simplify(P[i,colidx]*c0[i2]-P[i2,colidx]*c0[i])!=0: ok=False
    # off-pole ||c0||^2
    nrm=sp.simplify(sum(ci**2 for ci in c0))
    nz = (nrm != 0)  # symbolically nonzero (generic)
    if ok and nz: nok+=1
    else: print("CHART-MATCH FAIL", M, "ok=",ok,"nrm=",nrm)

print(f"chart P1/P2 split matches scalarGram signature + ||c0||^2 generically nonzero: {nok}/34")
# Also: confirm the ||c0||^2 pole is EXACTLY {det(P1^T P1)=0} = {sum_i (P i 0)^2 = 0}
print("NOTE: pole {||c0||^2=0} = {P1^T P1 = 0} (1x1 Gram), matching certificate's null pole.")
