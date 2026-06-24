"""Confirm the DEGREE structure of Erow entries as polynomials in the deformation params,
   and what ||Erow||^2 looks like at the deepest point, for L=2 vs L>=3.

For L=2: B = A^2 (single free matrix). Erow_t = B[0,t] + sum_i u_i B[i+1,t]
         = A2_{0,t} + sum_i u_i A2_{i+1,t}.  Leading term A2_{0,t} is LINEAR (degree 1) in params.
         => Erow is a submersion onto R^{Mlast} at the deepest pt: M_last Morse directions. n_raw=Mlast.

For L>=3: B = A^2 . A^3 ... so B[0,t] = sum over paths of products of >=2 layer entries: degree >= 2.
          Erow_t = (deg>=2 in layer params) + sum_i u_i (deg>=1).  The u_i*B[i+1,t] term: B[i+1,t] is
          itself degree>=2 in layers, times u_i => degree >=3.  So EVERY monomial of Erow_t has total
          degree >= 2.  => dErow/dparams = 0 at the origin.  NO linear (Morse) part.
"""
import sympy as sp
from geom_nraw import build_B

def report(M):
    L=len(M)-1; M1=M[1]; Mlast=M[-1]
    B, layer_syms_list = build_B(M)
    u = sp.Matrix(M1-1,1,lambda i,j: sp.Symbol(f"u_{i}"))
    params = list(u)+layer_syms_list
    Brow0=B[0,:]; Bred=B[1:,:]
    Erow = sp.expand((Brow0 + u.T*Bred).T)  # Mlast x 1
    mindeg=[]
    for t in range(Mlast):
        p = sp.Poly(Erow[t], *params)
        # min total degree among monomials
        degs = [sum(m) for m in p.monoms()]
        mindeg.append(min(degs) if degs else 0)
    print(f"  M={M} (L={L}): per-entry MIN total degree of Erow = {mindeg}   (1 => has Morse part)")

for M in [(2,2),(2,2,2),(3,3,3),(2,2,2,2),(3,3,3,3),(2,1,3,2),(2,2,2,2,2)]:
    report(M)
