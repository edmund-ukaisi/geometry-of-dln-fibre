#!/usr/bin/env python3
"""
DE-RISK the all-288 divisorMin >= 8 for the BORN-NATIVE fan (potential inner-pivot RED, F8-analog).

The fixed-shear gWrapFan (g_leaf, shearH o permP) fails on the node-1 Delta-block dominants
p1 in {4,5,6,7} (true rlct 2.5,1,1,1 -- F8 RED).  The BORN-NATIVE fan replaces the fixed shear
with a per-node-1-pivot NATIVE shear  nativeSel(p1) = sigma_p1^{-1} o (shearH o permP) o sigma_p1
(the symmetry-conjugate; sigma_p1 = the loss-symmetry perm mapping the canonical A0-dominant slot
20 -> p1's A0 slot).  F9 verified the 9 node-1 dominants ONLY at their sigma-induced (canonical)
inner pivots -- NOT all 288.

This script builds, for ALL 288 born-native leaves (p1 in C0 x p2 in C1 x p3 in C2):
    g_c = bb(C0,p1) o nativeSel(p1) o bb(C1,p2) o bb(C2,p3)
(the literal mandate structure: native shear per p1, node-2/node-3 blow-ups range freely with
their standard direction sets C1,C2), and computes:
  (1) the SURVIVOR support ek0 (loss-GCD quotient nonzero at 0) + its binding jac exponents,
  (2) the TRUE per-chart toric rlct = min_{w>=0} (w.kappa + sum w)/2  s.t.  w.m>=1 all gen monomials m,
  (3) divisorMin = min over value-monomial (binding) axes of (jac_exp + 1),
  (4) CHECK: true rlct >= 4  (<=> divisorMin >= 8, i.e. ek0's support lands only on jac>=7 coords).

KILL: any leaf with true rlct < 4 = RED (survivor lands on a jac<7 coord -> the born-native family
does NOT uniformly give >=8).
"""
import sympy as sp, numpy as np
from scipy.optimize import linprog
from collections import Counter
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
def shear_perm(w): return shearH(permP(w))   # the fixed born shear (shearH o permP)

C0=[0,1,2,3,4,5,6,7,20]; C1=[0,1,2,3,4,5,6,7]; C2=[1,5,6,7]

# ---- loss-symmetry sigma (row/col perms of A0 + matched A1-col perm), transitive on A0's 9 slots
A0slot={(0,0):20,(0,1):2,(0,2):3,(1,0):0,(1,1):4,(1,2):6,(2,0):1,(2,1):5,(2,2):7}
slot2ij={v:k for k,v in A0slot.items()}
def rowswap(i):
    m={}
    if i==0: return m
    for j in range(3): m[A0slot[(0,j)]]=A0slot[(i,j)]; m[A0slot[(i,j)]]=A0slot[(0,j)]
    for a in range(4): m[8+a]=8+4*i+a; m[8+4*i+a]=8+a          # A1 col0 <-> col i
    return m
def colswap(j):
    m={}
    if j==0: return m
    for i in range(3): m[A0slot[(i,0)]]=A0slot[(i,j)]; m[A0slot[(i,j)]]=A0slot[(i,0)]
    return m
def make_sigma(i,j):
    r=rowswap(i); c=colswap(j)
    def s(k):
        k1=r.get(k,k); return c.get(k1,k1)
    return s
def conj(F, sig):
    inv={sig(k):k for k in range(21)}
    def G(w):
        v=[w[sig(t)] for t in range(21)]; gv=F(v)
        return [gv[inv[t]] for t in range(21)]
    return G
def nativeSel(p1):
    i,j=slot2ij[p1]
    return conj(shear_perm, make_sigma(i,j))

def g_native(p1,p2,p3):
    w=bb(C2,p3)(list(u)); w=bb(C1,p2)(w); w=nativeSel(p1)(w); w=bb(C0,p1)(w)
    return w

def analyse(p1,p2,p3):
    w=g_native(p1,p2,p3)
    # jac exponents (jacDet is a single monomial for these charts; take min-exp = the exponent)
    J=sp.Matrix(21,21, lambda a,b: sp.diff(w[a],u[b]))
    dp=sp.Poly(sp.expand(J.det()),*u)
    kappa=np.array([min(m[t] for m in dp.monoms()) for t in range(21)],float)
    # loss generators + all monomials for the toric LP
    P=A1(w)*A0(w); gens=[sp.expand(P[a,b]) for a in range(4) for b in range(3)]
    mons=set()
    for g in gens:
        if g==0: continue
        for m in sp.Poly(g,*u).monoms(): mons.add(m)
    mons=[np.array(m,float) for m in mons]
    res=linprog(kappa+1.0, A_ub=-np.array(mons), b_ub=-np.ones(len(mons)),
                bounds=[(0,None)]*21, method='highs')
    rlct=res.fun/2.0 if res.success else None
    # value monomial (loss-GCD) -> binding axes -> survivor support ek0
    gg=None
    for g in gens:
        if g==0: continue
        pp=sp.Poly(g,*u); e=[min(m[t] for m in pp.monoms()) for t in range(21)]
        gg=e if gg is None else [min(a,b) for a,b in zip(gg,e)]
    vm=sp.prod([u[t]**gg[t] for t in range(21)])
    quots=[sp.expand(sp.cancel(g/vm)).subs({s:0 for s in u}) for g in gens]
    surv=[t for t,v in enumerate(quots) if v!=0]          # generators with a unit survivor at 0
    binding=[t for t in range(21) if gg[t]>0]             # value-monomial (survivor-support) axes
    jac_on_binding={t:int(kappa[t]) for t in binding}
    dmin=min(int(kappa[t])+1 for t in binding) if binding else None
    return dict(rlct=rlct, vm=vm, surv=surv, binding=binding,
                jac_on_binding=jac_on_binding, kappa=kappa, dmin=dmin)

if __name__=='__main__':
    import sys, time
    print("="*92)
    print("BORN-NATIVE fan: true toric rlct + divisorMin over ALL 288 leaves (F8-analog inner-pivot de-risk)")
    print("="*92)
    # --- validations ---
    print("\n[VALIDATE] canonical g_native(20,0,1) (native=fixed, must be 4.0):",
          round(analyse(20,0,1)['rlct'],4))
    print("[VALIDATE] worst fixed-shear dominant g_native(4,0,1) (was 2.5 fixed; native must be >=4):",
          round(analyse(4,0,1)['rlct'],4))
    print("[VALIDATE] 9 node-1 dominants at inner (p2=0,p3=1):")
    for p1 in C0:
        a=analyse(p1,0,1)
        print(f"    p1={p1:2d}: rlct={a['rlct']:.3f} surv={a['surv']} dmin={a['dmin']} "
              f"jac_binding={a['jac_on_binding']}")
    sys.stdout.flush()

    # --- full 288 sweep ---
    print("\n[SWEEP] all 288 born-native leaves:")
    t0=time.time()
    reds=[]; rlct_hist=Counter(); dmin_hist=Counter(); nsurv_hist=Counter()
    jacmin_on_surv=[]  # min jac over binding axes per leaf (== dmin-1)
    rows=[]
    for p1 in C0:
        for p2 in C1:
            for p3 in C2:
                a=analyse(p1,p2,p3)
                r=a['rlct']; d=a['dmin']
                rlct_hist[round(r,3)]+=1
                if d is not None: dmin_hist[d]+=1
                nsurv_hist[len(a['surv'])]+=1
                if d is not None: jacmin_on_surv.append(d-1)
                rows.append((p1,p2,p3,round(r,3),d,tuple(a['surv']),a['jac_on_binding']))
                if r is None or r < 4-1e-6:
                    reds.append((p1,p2,p3,round(r,4),d,tuple(a['surv']),a['jac_on_binding']))
    dt=time.time()-t0
    print(f"  (swept 288 leaves in {dt:.1f}s)")
    print("\n  rlct distribution:", dict(sorted(rlct_hist.items())))
    print("  divisorMin distribution:", dict(sorted(dmin_hist.items())))
    print("  #survivors-per-leaf distribution:", dict(sorted(nsurv_hist.items())))
    if jacmin_on_surv:
        print(f"  min jac on any survivor-support axis over all 288: {min(jacmin_on_surv)} "
              f"(need >=7 for divisorMin>=8)")
    print("\n"+"="*92)
    if reds:
        print(f"RED: {len(reds)} leaves with true rlct < 4 (KILL-CONDITION TRIPPED):")
        for (p1,p2,p3,r,d,surv,jb) in reds:
            print(f"   leaf(p1={p1:2d},p2={p2},p3={p3}): rlct={r} divisorMin={d} "
                  f"survivor={surv} jac_on_binding={jb}")
    else:
        print("SURVIVED: ALL 288 born-native leaves have true rlct >= 4  (<=> divisorMin >= 8).")
        print("=> the survivor support ek0 ALWAYS lands on jac>=7 coords; NEVER a low-jac axis.")
    print("="*92)
