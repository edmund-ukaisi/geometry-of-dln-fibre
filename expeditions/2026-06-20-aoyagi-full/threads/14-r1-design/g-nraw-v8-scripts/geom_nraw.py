"""GEOMETRY OF n_raw: count free smooth (Morse) directions the Erow-shear exposes, exactly.

Setup (per the brief).  Chain M : Fin(L+1)->N.  Layer 0 = A : M0 x M1.
B = A^1 . A^2 ... A^L  (product of remaining layers), B : M1 x M(last).
At the deepest (all-zero) point the loss is dlnLoss = ||A.B||^2.

Blow up layer 0: A = y0 * Ahat, Ahat[0,0]=1 (hard pivot).  core = ||Ahat.B||^2.
Schur:  Ahat = [[1, u^T],[v, W]],  u in R^{M1-1}, v in R^{M0-1}, W (M0-1)x(M1-1).
Erow = (Ahat.B)[0,:] = B[0,:] + u^T . B[1:,:]   (1 x M(last)).
S = W - v u^T  (M0-1 x M1-1 Schur complement),  reduced core = ||S . Bred||^2, Bred = B[1:,:].

QUESTION: the cover's  sum Erow^2  smooth block counts the FREE Morse directions exposed by the
shear  B[0,:] |-> Erow.  For L=2, B = A^1 is a FREE matrix, so B[0,:] are M(last) FREE coords =>
n_raw = M(last).  For L>=3, B is a PRODUCT A^1...A^L.  Are the Erow entries free, or constrained?

We compute n_raw GEOMETRICALLY two ways and compare:
 (count A) the rank of the JACOBIAN of the map  params -> Erow  at the deepest point (= dim of the
           image = # independent linear-in-perturbation directions Erow can move),
 (count B) the # of entries of Erow that are ALGEBRAICALLY INDEPENDENT as functions of the params.

Both should equal the # of free smooth Morse directions n_raw if 'B[0,:] free' is the right reading.
We do this with EXACT sympy symbols for the layer matrices.
"""
import sympy as sp
from itertools import product

def layer_syms(rows, cols, name):
    return sp.Matrix(rows, cols, lambda i,j: sp.Symbol(f"{name}_{i}_{j}"))

def build_B(M):
    """B = A1 . A2 ... A^L  as a symbolic M1 x M(last) matrix, with all layer entries free symbols.
       Layers: A^s : M[s] x M[s+1], s=1..L-1 (0-indexed s from 1).  Actually chain widths M[0..L].
       Layer 0 = A : M0 x M1 (blown up, handled separately).
       Remaining layers s=1..L-1: A^{(s)} : M[s] x M[s+1].  Product B = A^{(1)}...A^{(L-1)}?
       Wait: there are L layers total (A^1..A^L) mapping widths M0->M1->...->M_L.
       Layer indices i=1..L: A^i : M[i-1] x M[i].  Layer 0 in brief = A^1 (M0 x M1).
       B = A^2 . A^3 ... A^L : M1 x M_L.  (product of remaining L-1 layers)
    """
    L = len(M)-1
    # B = A^2 ... A^L, layer A^i : M[i-1] x M[i], i=2..L
    mats = [layer_syms(M[i-1], M[i], f"A{i}") for i in range(2, L+1)]
    if not mats:  # L=1: B is empty product = identity M1 x M1? brief: B=A^1...A^L product of remaining.
        # For L=1 there are no remaining layers; B is the M1 x M(last)=M1 x M1 ... but M(last)=M1.
        # Empty product over M1 -> identity. We'll treat L=1 separately (no product).
        return sp.eye(M[1]), []
    B = mats[0]
    for m in mats[1:]:
        B = B * m
    syms = []
    for m in mats:
        syms += list(m)
    return B, syms

def n_raw_geometry(M):
    """Return (Mlast, jac_rank_of_Erow_wrt_u_and_layers, alg_indep_count)."""
    L = len(M)-1
    Mlast = M[-1]
    M1 = M[1]
    B, layer_syms_list = build_B(M)   # B : M1 x Mlast
    # u in R^{M1-1}
    u = sp.Matrix(M1-1, 1, lambda i,j: sp.Symbol(f"u_{i}"))
    Brow0 = B[0,:]            # 1 x Mlast
    Bred  = B[1:,:]           # (M1-1) x Mlast
    Erow = Brow0 + (u.T * Bred)   # 1 x Mlast
    Erow = sp.Matrix([sp.expand(e) for e in Erow])  # column of Mlast exprs

    # ALL deformation params at the deepest point: u (the shear) + all layer entries of B.
    params = list(u) + layer_syms_list
    # Jacobian of Erow wrt params, evaluated at the deepest point = all params 0.
    J = Erow.jacobian(params)
    J0 = J.subs({p:0 for p in params})
    rank_at0 = J0.rank()

    # Algebraic independence proxy: rank of Jacobian at a GENERIC point (max # indep functions).
    import random
    subs_gen = {p: sp.Rational(random.randint(1,97), random.randint(1,53)) for p in params}
    Jg = J.subs(subs_gen)
    rank_generic = Jg.rank()
    return Mlast, rank_at0, rank_generic, len(Erow)

if __name__ == "__main__":
    print("M -> (M_last,  rank(dErow/dparams)@deepest,  rank@generic,  #Erow entries)")
    cases = [(2,2),(3,3),               # L=1 (B = identity)
             (2,2,2),(3,3,3),(2,2,4),(3,2,5),(2,3,4),  # L=2 (B = single free matrix A^2)
             (2,2,2,2),(3,3,3,3),(2,1,3,2),(2,2,1,2),(2,3,2,4),  # L=3 (B = A^2 A^3 product)
             (2,2,2,2,2),(3,3,3,3,3)]   # L=4
    for M in cases:
        Mlast, r0, rg, ne = n_raw_geometry(M)
        L=len(M)-1
        flag = "" if r0==Mlast else "  <-- r0 != M_last"
        print(f"  M={M} (L={L}): M_last={Mlast}  rank@0={r0}  rank@gen={rg}  #Erow={ne}{flag}")
