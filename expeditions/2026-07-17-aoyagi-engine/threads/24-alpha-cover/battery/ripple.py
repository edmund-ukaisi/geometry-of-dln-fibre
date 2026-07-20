#!/usr/bin/env python3
# Ripple: under interior-only alpha, does frobSq(prod) still factor as D^2 * residualCore
# (D = divisor product), and is residualCore bounded BELOW on the CLOSED unit box?
import sympy as sp

def beta_blowup(C, piv):
    pi,pj=piv; u=C[pi,pj]; m,n=C.shape
    return sp.Matrix(m,n, lambda i,j: u if (i,j)==piv else u*C[i,j])
def alpha_interior(C, cl):
    m,n=C.shape; C=C.as_mutable()
    for i in range(cl+1,m):
        for j in range(cl+1,n):
            C[i,j]=C[i,j]-C[i,cl]*C[cl,j]
    return C
def process(C,ncl):
    C=C.as_mutable()
    for c in range(ncl):
        C=alpha_interior(C,c); C=beta_blowup(C,(c,c))
    return sp.simplify(C)

# (2,2,2): C0=u*[[1,a],[b,rho]], C1=v*[[1,a'],[b',rho']]
u,a,b,rho = sp.symbols('u a b rho', real=True)
v,ap,bp,rhop = sp.symbols('v ap bp rhop', real=True)
C0 = u*sp.Matrix([[1,a],[b,rho]])
C1 = v*sp.Matrix([[1,ap],[bp,rhop]])
P = sp.expand(C0*C1)
frob = sp.expand(sum(P[i,j]**2 for i in range(2) for j in range(2)))
D2 = (u*v)**2
resid = sp.simplify(frob/D2)
print("frobSq(prod) / (u*v)^2  =")
sp.pprint(sp.expand(resid))
print("\nD = u*v factors out cleanly?", sp.simplify(frob - D2*resid)==0)
# residualCore = || [[1,a],[b,rho]]*[[1,ap],[bp,rhop]] ||^2 ; can it vanish on closed unit box?
# W3-style zero: a=1,b=0,rho=0,ap=0,bp=-1,rhop=0
z = resid.subs({a:1,b:0,rho:0,ap:0,bp:-1,rhop:0})
print("\nresidualCore at (a,b,rho,ap,bp,rhop)=(1,0,0,0,-1,0)  [all ratios in [-1,1]] =", sp.simplify(z))
# search the closed box corners for a zero of residualCore
import itertools
minval=None; argm=None
for vals in itertools.product([-1,0,1],repeat=6):
    zz=resid.subs(dict(zip([a,b,rho,ap,bp,rhop],vals)))
    zz=sp.simplify(zz)
    if minval is None or zz<minval: minval=zz; argm=vals
print("min residualCore over {-1,0,1}^6 =", minval, "at", argm)
print("\n=> D factors out (frobSq = D^2 * residualCore) EVEN with interior-alpha;")
print("   but residualCore hits 0 on the closed unit box => lower bound 0<lo FAILS (W3 leak).")
print("   Diagonalization (full Q,P) is what forces residualCore = 1 + sum(ratios)^2 >= 1.")
