#!/usr/bin/env python3
"""
The cover/value SEAM, constructive half: the RIGHT {g_c} for a moved dominant.

FINDING (true_rlct_perleaf_334.py): the fixed-shear gWrapFan has genuine rlct violations --
node-1 pivots p1 in {4,5,6,7} give true toric rlct 2.5,1.0,1.0,1.0 (< 4).  So the fixed-shear
fan is NOT a valid value family.

CLAIM to verify: for each dominant A0-entry there is a VALID resolution chart with toric rlct 4,
obtained by conjugating gWrap with a loss-symmetry sigma (the (3,3,4) loss is permutation-symmetric
and transitive on A0's 9 entries).  g' = sigma^{-1} o gWrap o sigma has its born-alpha = the
conjugated shear (a PER-PIVOT born-alpha, NOT the fixed shearH), toric rlct 4, divisorMin 8.
We verify for the WORST fixed-shear leaf: dominant moved A0[0,0]=u20 -> A0[1,1]=u4 (was rlct 2.5).
"""
import sympy as sp, numpy as np
from scipy.optimize import linprog
u = sp.symbols('u0:21')
def A0(w): return sp.Matrix([[w[20],w[2],w[3]],[w[0],w[4],w[6]],[w[1],w[5],w[7]]])
def A1(w): return sp.Matrix(4,3, lambda a,b: w[8+4*b+a])
def bb(S,p):
    S=set(S); return lambda w: [ (w[p] if j==p else (w[p]*w[j] if j in S else w[j])) for j in range(21) ]
PERMIDX={0:8,1:9,2:10,3:11,4:1,5:5,6:6,7:7,8:0,9:2,10:3,11:4}
def permP(w): return [ w[PERMIDX[k]] if k in PERMIDX else w[k] for k in range(21) ]
def shearH(w):
    g=list(w)
    g[4]=w[4]+w[0]*w[2]; g[5]=w[5]+w[1]*w[2]; g[6]=w[6]+w[0]*w[3]; g[7]=w[7]+w[1]*w[3]
    g[8]=w[8]-w[0]*w[12]-w[1]*w[16]; g[9]=w[9]-w[0]*w[13]-w[1]*w[17]
    g[10]=w[10]-w[0]*w[14]-w[1]*w[18]; g[11]=w[11]-w[0]*w[15]-w[1]*w[19]
    return g
def gWrap(u):
    w=bb({1,5,6,7},1)(list(u)); w=bb({0,1,2,3,4,5,6,7},0)(w); w=permP(w); w=shearH(w)
    w=bb({0,1,2,3,4,5,6,7,20},20)(w); return w

# --- loss-symmetry sigma moving A0[0,0]->A0[1,1] ---
# slot map of A0[i,j]:
A0slot={(0,0):20,(0,1):2,(0,2):3,(1,0):0,(1,1):4,(1,2):6,(2,0):1,(2,1):5,(2,2):7}
# middle-index swap k:0<->1 : swap A0 rows 0,1 and A1 cols 0,1
def sym_mid(k):
    m={}
    for j in range(3): m[A0slot[(0,j)]]=A0slot[(1,j)]; m[A0slot[(1,j)]]=A0slot[(0,j)]
    for a in range(4): m[8+a]=12+a; m[12+a]=8+a           # A1 col0<->col1
    return m.get(k,k)
# output-index swap j:0<->1 : swap A0 cols 0,1
def sym_out(k):
    m={}
    for i in range(3): m[A0slot[(i,0)]]=A0slot[(i,1)]; m[A0slot[(i,1)]]=A0slot[(i,0)]
    return m.get(k,k)
def sigma(k): return sym_out(sym_mid(k))        # composite (mid then out)
inv={sigma(k):k for k in range(21)}
def sigma_inv(k): return inv[k]
def act(perm, w): return [ w[ [pp for pp in range(21) if perm(pp)==k][0] ] for k in range(21) ]
# act(perm,w)[k] = w[perm^{-1}(k)]
def act_sigma(w):     return [ w[sigma_inv(k)] for k in range(21) ]
def act_sigma_inv(w): return [ w[sigma(k)] for k in range(21) ]

def gConj(u):
    return act_sigma_inv(gWrap(act_sigma(list(u))))   # sigma^{-1} o gWrap o sigma

def true_rlct_of(w):
    J=sp.Matrix(21,21, lambda i,j: sp.diff(w[i],u[j]))
    dp=sp.Poly(sp.expand(J.det()),*u); kappa=np.array([min(m[i] for m in dp.monoms()) for i in range(21)],float)
    P=A1(w)*A0(w); gens=[sp.expand(P[i,j]) for i in range(4) for j in range(3)]
    mons=set()
    for g in gens:
        if g==0: continue
        for m in sp.Poly(g,*u).monoms(): mons.add(m)
    mons=[np.array(m,float) for m in mons]
    res=linprog(kappa+1.0, A_ub=-np.array(mons), b_ub=-np.ones(len(mons)), bounds=[(0,None)]*21, method='highs')
    # value monomial (GCD) + survivor
    gg=None
    for g in gens:
        if g==0: continue
        pp=sp.Poly(g,*u); e=[min(m[i] for m in pp.monoms()) for i in range(21)]
        gg=e if gg is None else [min(a,b) for a,b in zip(gg,e)]
    vm=sp.prod([u[i]**gg[i] for i in range(21)])
    quots=[sp.expand(sp.cancel(g/vm)).subs({s:0 for s in u}) for g in gens]
    surv=[i for i,v in enumerate(quots) if v!=0]
    jm=" * ".join(f"u{i}^{int(kappa[i])}" for i in range(21) if kappa[i]>0)
    return res.fun/2.0, vm, surv, jm

print("dominant A0[1,1]=u4 was rlct 2.5 with the FIXED shear; the sigma-conjugate chart:")
r,vm,surv,jm = true_rlct_of(gConj(u))
print(f"  g' = sigma^-1 o gWrap o sigma :  true rlct = {round(r,4)}   "
      f"[{'== 4 RESOLVED' if abs(r-4)<1e-6 else 'NOT 4'}]")
print(f"  value monomial = {vm}   survivor idx = {surv}   (single-entry: {len(surv)==1})")
print(f"  jacDet monomial = {jm}")
print(f"  born-alpha here = sigma^-1 o shearH o sigma (the PER-PIVOT recoord, NOT fixed shearH)")
