#!/usr/bin/env python3
"""
Honest SMOOTH/SINGULAR test via the GCD-monomial of the 12 loss generators (exact).

For each shear toggle: compute the 12 generators g_i = P_i o chart, take their monomial GCD m,
divide, and read residuals at center.  Also report per-generator monomial factorisation to SEE the
over-vanishing (a generator = single-monomial*unit is a clean survivor; a generator = SUM of
monomials with no dominant one is over-vanishing).
"""
import sympy as sp
u = sp.symbols('u0:21')

def A0(u): return sp.Matrix([[u[20],u[2],u[3]],[u[0],u[4],u[6]],[u[1],u[5],u[7]]])
def A1(u): return sp.Matrix(4,3, lambda a,b: u[8+4*b+a])

def gFaithful(u, schur=True, recoord=True):
    g=list(u); sA=1 if schur else 0; rA=1 if recoord else 0
    g[0]=u[8]; g[1]=u[9]; g[2]=u[10]; g[3]=u[11]
    g[4]=u[0]*u[1]+sA*u[8]*u[10]; g[5]=u[0]*u[1]*u[5]+sA*u[9]*u[10]
    g[6]=u[0]*u[1]*u[6]+sA*u[8]*u[11]; g[7]=u[0]*u[1]*u[7]+sA*u[9]*u[11]
    g[8]=u[0]-rA*(u[8]*u[12]+u[9]*u[16]); g[9]=u[0]*u[2]-rA*(u[8]*u[13]+u[9]*u[17])
    g[10]=u[0]*u[3]-rA*(u[8]*u[14]+u[9]*u[18]); g[11]=u[0]*u[4]-rA*(u[8]*u[15]+u[9]*u[19])
    return g

def sigmaPiv(w):
    S=set(range(8))|{20}
    return [ (w[20] if k==20 else (w[20]*w[k] if k in S else w[k])) for k in range(21)]

def gens(schur,recoord):
    g=sigmaPiv(gFaithful(u,schur,recoord))
    P=sp.expand(A1(g)*A0(g))
    return [sp.expand(P[i,j]) for i in range(4) for j in range(3)]

def monomial_gcd(polys):
    """monomial gcd of a list of polynomials over u."""
    g=None
    for p in polys:
        if p==0: continue
        pp=sp.Poly(p,*u)
        # min exponent of each var across all monomials of pp
        exps=[min(m[i] for m in pp.monoms()) for i in range(len(u))]
        g=exps if g is None else [min(a,b) for a,b in zip(g,exps)]
    if g is None: return sp.Integer(1)
    return sp.prod([u[i]**g[i] for i in range(len(u))])

def report(name,schur,recoord):
    G=gens(schur,recoord)
    m=monomial_gcd(G)
    print(f"\n[{name}]  monomial GCD of the 12 generators = {m}")
    quots=[sp.expand(sp.cancel(g/m)) for g in G]
    at0=[q.subs({s:0 for s in u}) for q in quots]
    surv=any(v!=0 for v in at0)
    print(f"   residuals at center = {at0}")
    print(f"   SURVIVOR (some residual !=0 at center): {surv}  =>  {'SMOOTH' if surv else 'SINGULAR (over-vanishes)'}")
    # show the clean-survivor generators: those that are a single monomial (residual is a constant)
    cleans=[i for i,q in enumerate(quots) if len(sp.Poly(q,*u).monoms())==1 and at0[i]!=0]
    print(f"   clean single-monomial*unit generators (indices): {cleans}")
    return m,at0,surv

if __name__=='__main__':
    print("="*90); print("(3,3,4) loss pullback: GCD-monomial residual-at-center, per shear toggle"); print("="*90)
    report("FULL  (schur+recoord ON) = canonical done-leaf", True, True)
    report("recoord OFF (drop the S=2 recoord support b)", True, False)
    report("schur  OFF (drop the within-layer Schur support a)", False, True)
    report("BOTH OFF (pure blow-up, shear-free)", False, False)
