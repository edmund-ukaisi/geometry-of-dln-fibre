#!/usr/bin/env python3
"""
TRUE per-chart rlct-contribution via the toric LP (the cover/value SEAM + Codex kill-(c)).

For a chart g_c with jac |det Dg_c| = x^kappa and loss = sum_i (gen_i)^2, the exact toric RLCT
(Aoyagi Lemma-1: rlct(sum g^2) = rlct<g>) over ALL monomial valuations w >= 0 is
    rlct_chart = ( min_{w>=0}  w.kappa + sum_j w_j  s.t.  w.m >= 1  for every monomial m of every gen )  / 2.
(The /2 = the square; the denominator's min over monomials is fixed to 1 by the constraints, the
 numerator's +sum w_j is the standard dx per-variable contribution.)

This is the DECISIVE test for the over-vanishing leaves: an over-vanishing chart vanishes to
HIGHER order, which for a LOWER bound could LOWER rlct below 4.  If rlct_chart >= 4 even for the
over-vanishing leaves, the fixed-shear fan is SAFE (higher order => higher, not lower, rlct); if
some leaf gives rlct_chart < 4, that leaf must be EXCLUDED from the value cover (RED for the
fixed-shear fan as a value family).

VALIDATION: the canonical must return exactly 4.
"""
import sympy as sp
import numpy as np
from scipy.optimize import linprog

u = sp.symbols('u0:21')
def A0(w): return sp.Matrix([[w[20],w[2],w[3]],[w[0],w[4],w[6]],[w[1],w[5],w[7]]])
def A1(w): return sp.Matrix(4,3, lambda a,b: w[8+4*b+a])
def bb(S,p):
    S=set(S)
    return lambda w: [ (w[p] if j==p else (w[p]*w[j] if j in S else w[j])) for j in range(21) ]
PERMIDX={0:8,1:9,2:10,3:11,4:1,5:5,6:6,7:7,8:0,9:2,10:3,11:4}
def permP(w): return [ w[PERMIDX[k]] if k in PERMIDX else w[k] for k in range(21) ]
def shearH(w):
    g=list(w)
    g[4]=w[4]+w[0]*w[2]; g[5]=w[5]+w[1]*w[2]; g[6]=w[6]+w[0]*w[3]; g[7]=w[7]+w[1]*w[3]
    g[8]=w[8]-w[0]*w[12]-w[1]*w[16]; g[9]=w[9]-w[0]*w[13]-w[1]*w[17]
    g[10]=w[10]-w[0]*w[14]-w[1]*w[18]; g[11]=w[11]-w[0]*w[15]-w[1]*w[19]
    return g
C0=[0,1,2,3,4,5,6,7,20]; C1=[0,1,2,3,4,5,6,7]; C2=[1,5,6,7]
def g_leaf(p1,p2,p3):
    w=bb(C2,p3)(list(u)); w=bb(C1,p2)(w); w=permP(w); w=shearH(w); w=bb(C0,p1)(w)
    return w

def jac_kappa(w):
    J=sp.Matrix(21,21, lambda i,j: sp.diff(w[i],u[j]))
    dp=sp.Poly(sp.expand(J.det()),*u)
    return np.array([min(m[i] for m in dp.monoms()) for i in range(21)], dtype=float)

def gen_monomials(w):
    P=A1(w)*A0(w); gens=[sp.expand(P[i,j]) for i in range(4) for j in range(3)]
    mons=set()
    for g in gens:
        if g==0: continue
        for m in sp.Poly(g,*u).monoms():
            mons.add(m)
    return [np.array(m,dtype=float) for m in mons]

def true_rlct(p1,p2,p3):
    w=g_leaf(p1,p2,p3)
    kappa=jac_kappa(w); mons=gen_monomials(w)
    # min  (kappa+1).x   s.t.  A.x >= 1 (each monomial),  x>=0
    c = kappa + 1.0
    A_ub = -np.array(mons)         # -m . x <= -1
    b_ub = -np.ones(len(mons))
    res = linprog(c, A_ub=A_ub, b_ub=b_ub, bounds=[(0,None)]*21, method='highs')
    return res.fun/2.0 if res.success else None

if __name__=='__main__':
    print("="*80)
    print("TRUE per-chart rlct-contribution (toric LP) -- cover/value seam + kill-(c)")
    print("="*80)
    print("VALIDATION canonical (must be 4.0):", round(true_rlct(20,0,1),4))
    print("\n-- node-1 pivots (fixed shear; 8/9 over-vanish) --")
    for p1 in C0:
        r=true_rlct(p1,0,1); print(f"  leaf(p1={p1:2d},0,1): true rlct = {round(r,4)}  "
                                   f"[{'>=4 SAFE' if r>=4-1e-6 else 'BELOW 4 << must-exclude'}]")
    print("\n-- node-2 pivots (p1=20; {1,5,6,7} over-vanish) --")
    for p2 in C1:
        r=true_rlct(20,p2,1); print(f"  leaf(20,p2={p2},1): true rlct = {round(r,4)}  "
                                    f"[{'>=4 SAFE' if r>=4-1e-6 else 'BELOW 4 << must-exclude'}]")
    print("\n-- node-3 pivots (p1=20,p2=0) --")
    for p3 in C2:
        r=true_rlct(20,0,p3); print(f"  leaf(20,0,p3={p3}): true rlct = {round(r,4)}  "
                                    f"[{'>=4 SAFE' if r>=4-1e-6 else 'BELOW 4 << must-exclude'}]")
