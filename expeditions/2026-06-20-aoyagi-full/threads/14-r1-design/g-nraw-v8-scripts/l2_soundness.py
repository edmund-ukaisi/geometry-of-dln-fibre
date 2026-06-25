"""Confirm the L=2 soundness GEOMETRICALLY and pin WHY it works only at L=2.

L=2 chain M=(m,k,n): loss = ||A.B||^2, A: m x k (blown up: A=y0*Ahat), B = A^2: k x n FREE matrix.
core = ||Ahat.B||^2.  Ahat=[[1,u],[v,W]].
Erow = B[0,:] + u^T B[1:,:]  = (row 0 of the FREE matrix B) + u^T (rows 1.. of B).
Since B is FREE, B[0,:] are n independent free coords; the map params->Erow is a SUBMERSION onto R^n
at the deepest point (its differential includes dB[0,:] = full rank n).  So the n Erow coords are
genuine Morse directions: ||Erow||^2 = sum of n independent squared-linear-forms.
The residual is ||S.Bred||^2 with S = W - v u^T the (m-1)x(k-1) Schur complement and Bred=B[1:,:] the
(k-1)x n FREE block -> this IS the reduced-chain loss dlnLoss(m-1,k-1,n) 0.
So at L=2:  rlct(node) = n/2 (the Morse block) + rlct(reduced) ... capped by mk/2.  Telescopes.

The L=2-ONLY mechanism, made exact: B is a SINGLE free matrix ONLY when the 'remaining layers' are
exactly ONE layer, i.e. L-1 = 1 <=> L = 2.  For L>=3 'remaining' = >=2 layers, B is a product, NOT free.
"""
import sympy as sp
from geom_nraw import build_B

def check_submersion(M):
    L=len(M)-1; M1=M[1]; Mlast=M[-1]
    B,layers = build_B(M)
    u=sp.Matrix(M1-1,1,lambda i,j: sp.Symbol(f"u_{i}"))
    Erow = sp.expand((B[0,:] + u.T*B[1:,:]).T)
    params=list(u)+layers
    J0 = Erow.jacobian(params).subs({p:0 for p in params})
    return J0.rank(), Mlast

print("Submersion check: rank d(Erow)|0  ==  M_last  <=>  L==2:")
for M in [(2,2,2),(3,3,3),(2,3,4),(4,2,3),   # L2
          (2,2,2,2),(3,3,3,3),(2,3,4,2)]:     # L3
    r,ml=check_submersion(M)
    print(f"  M={M} (L={len(M)-1}): rank={r}, M_last={ml}, {'SUBMERSION (Morse=M_last)' if r==ml else 'NOT submersion (Morse=0)'}")

print("\nWHY: 'remaining layers' = L-1.  B is a single free matrix iff L-1==1 iff L==2.")
print("For L>=3 the residual ||S.Bred||^2 also has Bred a PRODUCT, so the child is again a deep")
print("product -- the recursion schurStateRed keeps L layers, never reaching the free-B base case.")
