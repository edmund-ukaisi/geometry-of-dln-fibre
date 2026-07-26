#!/usr/bin/env python3
"""
FULL gWrapFan per-leaf census (3,3,4): the 288 = 9*8*4 pivot-choice leaves.

Objects taken EXACTLY from the Lean source (Corank2GWrapDecomp, Corank2FaithfulComposite,
Corank2CoreGenWrap, BlockBlowup):
  gWrap = sigmaPiv o shearH o permP o bbA0 o bbA1        (canonical leaf, pivots 20,0,1)
  bb(S,p)(w)[j] = w[p] if j==p ; w[p]*w[j] if j in S ; else w[j]     (blockBlowupMap)
  node1 = bb({0..7,20}, p1) o (shearH o permP)     p1 in {0,1,2,3,4,5,6,7,20}  (9)
  node2 = bb({0..7},     p2)                        p2 in {0..7}                 (8)
  node3 = bb({1,5,6,7},  p3)                        p3 in {1,5,6,7}              (4)
  g_leaf(p1,p2,p3) = node1blow o shearH o permP o node2blow o node3blow

Loss:  coreGen o gWrap = c11 * (flat(Pmat) o gFaithful),  c11 = u20 (node1 pivot slot),
       Pmat = A1 * A0.  loss = sum (Pmat entries at g_leaf)^2.

For each leaf: monomial GCD m of the 12 pullback generators, residuals = gens/m at center,
SURVIVOR iff some residual(0) != 0 (single_le_sum fires with that entry as the KEPT survivor).
This is the DIRECT test of the FIXED-shear gWrapFan (whether the born shearH exposes a survivor
for a NON-canonical pivot).  N_singular / N_smooth read off the node-1 pivot classes.
"""
import sympy as sp
from itertools import product

u = sp.symbols('u0:21')

# ---- the loss matrices (exact, from loss_gcd_toggle.py = the Lean A0,A1) ----
def A0(w): return sp.Matrix([[w[20],w[2],w[3]],[w[0],w[4],w[6]],[w[1],w[5],w[7]]])
def A1(w): return sp.Matrix(4,3, lambda a,b: w[8+4*b+a])   # 4x3

# ---- the chart atoms (exact, from the Lean defs) ----
def bb(S, p):
    """blockBlowupMap S p : w -> (j |-> w[p] if j==p ; w[p]*w[j] if j in S ; w[j])."""
    S = set(S)
    def f(w):
        return [ (w[p] if j==p else (w[p]*w[j] if j in S else w[j])) for j in range(21) ]
    return f

PERMIDX = {0:8,1:9,2:10,3:11,4:1,5:5,6:6,7:7,8:0,9:2,10:3,11:4}
def permP(w):
    return [ w[PERMIDX[k]] if k in PERMIDX else w[k] for k in range(21) ]

def shearH(w):
    g=list(w)
    g[4]=w[4]+w[0]*w[2]; g[5]=w[5]+w[1]*w[2]; g[6]=w[6]+w[0]*w[3]; g[7]=w[7]+w[1]*w[3]
    g[8]=w[8]-w[0]*w[12]-w[1]*w[16]; g[9]=w[9]-w[0]*w[13]-w[1]*w[17]
    g[10]=w[10]-w[0]*w[14]-w[1]*w[18]; g[11]=w[11]-w[0]*w[15]-w[1]*w[19]
    return g

C0 = [0,1,2,3,4,5,6,7,20]   # node1 center = 9 entries of A0
C1 = [0,1,2,3,4,5,6,7]      # node2 center (bbA0)
C2 = [1,5,6,7]              # node3 center (bbA1)

def g_leaf(p1,p2,p3):
    w = bb(C2,p3)(list(u))
    w = bb(C1,p2)(w)
    w = permP(w)
    w = shearH(w)
    w = bb(C0,p1)(w)
    return w

def loss_gens(p1,p2,p3):
    w = g_leaf(p1,p2,p3)
    P = A1(w)*A0(w)
    return [sp.expand(P[i,j]) for i in range(4) for j in range(3)]

def monomial_gcd(polys):
    g=None
    for p in polys:
        p=sp.expand(p)
        if p==0: continue
        pp=sp.Poly(p,*u)
        exps=[min(m[i] for m in pp.monoms()) for i in range(len(u))]
        g=exps if g is None else [min(a,b) for a,b in zip(g,exps)]
    if g is None: return [0]*21
    return g

def report_leaf(p1,p2,p3, show=True):
    G=loss_gens(p1,p2,p3)
    gexp=monomial_gcd(G)
    m=sp.prod([u[i]**gexp[i] for i in range(21)])
    quots=[sp.cancel(g/m) for g in G]
    at0=[sp.expand(q).subs({s:0 for s in u}) for q in quots]
    surv=[i for i,v in enumerate(at0) if v!=0]
    # a CLEAN single-monomial survivor: the generator is exactly (monomial)*const
    cleans=[i for i in surv if len(sp.Poly(sp.expand(quots[i]),*u).monoms())==1]
    mono_syms=[i for i in range(21) if gexp[i]>0]
    if show:
        print(f"  leaf(p1={p1:2d},p2={p2},p3={p3}): GCD={m}, "
              f"survivor={'YES' if surv else 'NO '}, clean-survivors={cleans}, "
              f"resid(0) nz idx={surv}")
    return dict(gcd=m, gexp=gexp, mono=mono_syms, surv=surv, cleans=cleans, at0=at0)

if __name__=='__main__':
    print("="*95)
    print("gWrapFan FIXED-shear census: the 9 node-1 pivot types (p2=0,p3=1 canonical inner)")
    print("="*95)
    for p1 in C0:
        report_leaf(p1,0,1)

    print("\n"+"="*95)
    print("Vary node-2 pivot (canonical node1=20, node3=1): the 8 p2 sub-choices")
    print("="*95)
    for p2 in C1:
        report_leaf(20,p2,1)

    print("\n"+"="*95)
    print("Vary node-3 pivot (canonical node1=20, node2=0): the 4 p3 sub-choices")
    print("="*95)
    for p3 in C2:
        report_leaf(20,0,p3)
