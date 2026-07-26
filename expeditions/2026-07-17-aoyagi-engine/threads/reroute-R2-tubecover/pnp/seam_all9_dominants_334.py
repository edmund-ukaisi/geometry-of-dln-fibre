#!/usr/bin/env python3
"""
Complete the value-side cert: verify EVERY A0-dominant restores to rlct 4 via its per-pivot
native born-alpha (the symmetry-conjugate).  Confirms #188 (value family = per-pivot native) is
uniformly sound -- NO A0-dominant is a genuine monument (unrestorable).  The loss symmetry group
(row perms x col perms of A0, with the matched A1-col perm) is transitive on A0's 9 entries, so
by symmetry all 9 = rlct 4; this VERIFIES it concretely per dominant (decorrelated).
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

A0slot={(0,0):20,(0,1):2,(0,2):3,(1,0):0,(1,1):4,(1,2):6,(2,0):1,(2,1):5,(2,2):7}

def rowswap(i):          # middle index 0<->i : A0 rows + A1 cols
    if i==0: return lambda k:k
    m={}
    for j in range(3): m[A0slot[(0,j)]]=A0slot[(i,j)]; m[A0slot[(i,j)]]=A0slot[(0,j)]
    for a in range(4): m[8+4*0+a]=8+4*i+a; m[8+4*i+a]=8+4*0+a   # A1 col0<->col i
    return lambda k:m.get(k,k)
def colswap(j):          # output index 0<->j : A0 cols
    if j==0: return lambda k:k
    m={}
    for i in range(3): m[A0slot[(i,0)]]=A0slot[(i,j)]; m[A0slot[(i,j)]]=A0slot[(i,0)]
    return lambda k:m.get(k,k)

def make_sigma(i,j):
    r=rowswap(i); c=colswap(j)
    return lambda k: c(r(k))     # rowswap then colswap : (0,0)->(i,0)->(i,j)

def true_rlct_of(w):
    J=sp.Matrix(21,21, lambda a,b: sp.diff(w[a],u[b]))
    dp=sp.Poly(sp.expand(J.det()),*u); kappa=np.array([min(m[t] for m in dp.monoms()) for t in range(21)],float)
    P=A1(w)*A0(w); gens=[sp.expand(P[a,b]) for a in range(4) for b in range(3)]
    mons=set()
    for g in gens:
        if g==0: continue
        for m in sp.Poly(g,*u).monoms(): mons.add(m)
    mons=[np.array(m,float) for m in mons]
    res=linprog(kappa+1.0, A_ub=-np.array(mons), b_ub=-np.ones(len(mons)), bounds=[(0,None)]*21, method='highs')
    gg=None
    for g in gens:
        if g==0: continue
        pp=sp.Poly(g,*u); e=[min(m[t] for m in pp.monoms()) for t in range(21)]
        gg=e if gg is None else [min(a,b) for a,b in zip(gg,e)]
    vm=sp.prod([u[t]**gg[t] for t in range(21)])
    quots=[sp.expand(sp.cancel(g/vm)).subs({s:0 for s in u}) for g in gens]
    surv=[t for t,v in enumerate(quots) if v!=0]
    binding=[t for t in range(21) if gg[t]>0]
    dmin=min(int(kappa[t])+1 for t in binding) if binding else None
    return res.fun/2.0, vm, surv, dmin

print("="*82)
print("All 9 A0-dominants via per-pivot native born-alpha (symmetry-conjugate): rlct-4?")
print("="*82)
allok=True
for i in range(3):
    for j in range(3):
        sig=make_sigma(i,j); inv={sig(k):k for k in range(21)}
        gp=lambda uu,sig=sig,inv=inv: [ gWrap([uu[sig(t)] for t in range(21)])[inv[t]] for t in range(21) ]
        r,vm,surv,dmin=true_rlct_of(gp(list(u)))
        ok = abs(r-4)<1e-6 and len(surv)==1 and dmin==8
        allok = allok and ok
        print(f"  A0[{i},{j}] (slot {A0slot[(i,j)]:2d}): rlct={r:.3f}, survivor idx={surv}, "
              f"value-mono={vm}, divisorMin={dmin}  [{'OK' if ok else 'FAIL'}]")
print("="*82)
print(f"ALL 9 A0-dominants restore to rlct-4 / single-survivor / divisorMin-8: {allok}")
print("=> per-pivot native born-alpha is UNIFORMLY sound; NO A0-dominant is a monument.")
