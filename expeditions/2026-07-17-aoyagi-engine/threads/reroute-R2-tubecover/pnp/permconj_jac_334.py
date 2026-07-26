#!/usr/bin/env python3
"""
Kill-(c) closure for a MOVED dominant (Codex's residual): the singular leaves whose
dominant c11 is a DIFFERENT A0-entry are coordinate-permutation-conjugates of the canonical.
A coordinate permutation pi (an ISOMETRY, |det|=1) sends gWrap -> pi o gWrap o pi^{-1}; then
    jacDet(pi o g o pi^{-1})(u) = jacDet(g)(pi^{-1} u)  (chain rule, |det pi|=1),
so the jac EXPONENTS are exactly PERMUTED (7,3,8 stays {7,3,8}), never deepened.  This is
EXACT transport (isometry), NOT a center-size heuristic -- it rebuts "composition deepens".

We VERIFY concretely: conjugate gWrap by a permutation pi that moves the A0-pivot from
(0,0)=u20 to (1,1)=u4 (a genuinely different dominant), and read the survivor + jac + divisorMin.
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
def gWrap(u):
    w=bb({1,5,6,7},1)(list(u)); w=bb({0,1,2,3,4,5,6,7},0)(w); w=permP(w); w=shearH(w)
    w=bb({0,1,2,3,4,5,6,7,20},20)(w); return w

def min_exps(polys):
    g=None
    for p in polys:
        p=sp.expand(p)
        if p==0: continue
        pp=sp.Poly(p,*u); e=[min(m[i] for m in pp.monoms()) for i in range(21)]
        g=e if g is None else [min(a,b) for a,b in zip(g,e)]
    return g

def analyse_map(w, label):
    J=sp.Matrix(21,21, lambda i,j: sp.diff(w[i],u[j]))
    detpoly=sp.Poly(sp.expand(J.det()),*u); jexp=[min(m[i] for m in detpoly.monoms()) for i in range(21)]
    P=A1(w)*A0(w); gens=[sp.expand(P[i,j]) for i in range(4) for j in range(3)]
    vexp=min_exps(gens)
    quots=[sp.cancel(g/sp.prod([u[i]**vexp[i] for i in range(21)])) for g in gens]
    at0=[sp.expand(q).subs({s:0 for s in u}) for q in quots]; surv=[i for i,v in enumerate(at0) if v!=0]
    binding=[i for i in range(21) if vexp[i]>0]
    vm=" * ".join(f"u{i}^{vexp[i]}" for i in binding) if binding else "1"
    jm=" * ".join(f"u{i}^{jexp[i]}" for i in range(21) if jexp[i]>0)
    print(f"[{label}] jacDet monomial = {jm}")
    print(f"    value-mono = {vm}, survivor={'Y' if surv else 'N'} idx={surv}")
    if surv and binding:
        ratios=[sp.Rational(jexp[d]+1,2*vexp[d]) for d in binding]
        for d in binding:
            print(f"      divisor u{d}: jac={jexp[d]}, mono={vexp[d]}, thr=(jac+1)/(2mono)={sp.Rational(jexp[d]+1,2*vexp[d])}")
        print(f"    rlct_chart = {min(ratios)}  [{'>=4 OK' if min(ratios)>=4 else 'RED <4'}], divisorMin={min(jexp[d]+1 for d in binding)}")

# canonical (dominant = A0[0,0] = u20)
analyse_map(gWrap(u), "canonical dominant A0[0,0]=u20")

# a coordinate permutation pi moving A0-pivot (0,0)<->(1,1): swap the A0 slots u20<->u4,
# and their coupled partners, as a full 21-coord involution (an isometry, |det|=1).
# A0[0,0]=u20, A0[1,1]=u4.  For a clean isometry-conjugate we swap the two A0-entry slots
# and leave the rest; this realises a DIFFERENT dominant leaf of the K-orbit.
def pi(k):
    sw={20:4,4:20}
    return sw.get(k,k)
def conj_gWrap(u):
    up=[u[pi(k)] for k in range(21)]     # pi^{-1} u  (pi is an involution)
    w=gWrap(up)
    return [w[pi(k)] for k in range(21)]  # pi o gWrap o pi^{-1}
analyse_map(conj_gWrap(u), "perm-conjugate dominant A0[1,1]=u4 (isometry, |det|=1)")
