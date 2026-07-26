#!/usr/bin/env python3
"""
CONCRETE per-leaf divisorMin (answering Codex kill-(c): composition can deepen a divisor's
Jacobian order; center-size alone is not the total order).  For each leaf that exposes a
survivor (fixed-shear census), compute:
  - jacDet(g_leaf) EXACTLY (full composite symbolic determinant) -> jac_exp of each coord
  - value_monomial = GCD of the 12 loss generators -> which divisors bind, with mono_exp
  - divisorMin = min over binding divisors of (jac_exp+1) [mono_exp=1 squarefree pivot]
    and the ratio (jac_exp+1)/(2*mono_exp) = per-divisor threshold; rlct_chart = min ratio.
This is the DIRECT test (no center-size heuristic): does the composite pullback ever drop
divisorMin below 8 on a survivor leaf?
"""
import sympy as sp
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

def min_exps(polys):
    g=None
    for p in polys:
        p=sp.expand(p)
        if p==0: continue
        pp=sp.Poly(p,*u); e=[min(m[i] for m in pp.monoms()) for i in range(21)]
        g=e if g is None else [min(a,b) for a,b in zip(g,e)]
    return g

def analyse(p1,p2,p3):
    w=g_leaf(p1,p2,p3)
    # jacDet exactly
    J=sp.Matrix(21,21, lambda i,j: sp.diff(w[i],u[j]))
    detpoly=sp.Poly(sp.expand(J.det()),*u)
    jexp=[min(m[i] for m in detpoly.monoms()) for i in range(21)]
    # value monomial = GCD of loss gens
    P=A1(w)*A0(w); gens=[sp.expand(P[i,j]) for i in range(4) for j in range(3)]
    vexp=min_exps(gens)
    # binding divisors = coords with vexp>0 ; check survivor exists
    quots=[sp.cancel(g/sp.prod([u[i]**vexp[i] for i in range(21)])) for g in gens]
    at0=[sp.expand(q).subs({s:0 for s in u}) for q in quots]
    surv=[i for i,v in enumerate(at0) if v!=0]
    binding=[i for i in range(21) if vexp[i]>0]
    vm=" * ".join(f"u{i}^{vexp[i]}" for i in binding) if binding else "1"
    print(f"  leaf(p1={p1:2d},p2={p2},p3={p3}) survivor={'Y' if surv else 'N'} "
          f"value-mono={vm}")
    if surv:
        ratios=[]
        for d in binding:
            r=sp.Rational(jexp[d]+1, 2*vexp[d])
            ratios.append(r)
            print(f"      divisor u{d}: jac_exp={jexp[d]}, mono_exp={vexp[d]}, "
                  f"threshold=(jac+1)/(2*mono)={r}")
        print(f"      rlct_chart = min threshold = {min(ratios)}   "
              f"[{'>= 4 OK' if min(ratios)>=4 else 'BELOW 4  <<< RED'}]")

if __name__=='__main__':
    print("="*90)
    print("CONCRETE per-leaf divisorMin on the survivor leaves (Codex kill-(c) direct test)")
    print("="*90)
    print("-- canonical + node-2 survivor variants (p1=20, p3=1) --")
    for p2 in [0,2,3,4]:
        analyse(20,p2,1)
    print("-- node-3 pivot variants (p1=20,p2=0) --")
    for p3 in [1,5,6,7]:
        analyse(20,0,p3)
