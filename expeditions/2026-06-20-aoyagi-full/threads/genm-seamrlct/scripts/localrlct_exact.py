import sympy as sp, numpy as np, itertools
from scipy.optimize import linprog
# Local rlct of a Frobenius-squared DLN loss germ at a fiber point, via:
#   rlct(f) = rank(Hess)/2 + rlct(residual g on ker Hess),  g = f restricted to ker(Hess) (leading proxy),
#   rlct(g) = 1/t0 (Varchenko, Newton-nondegenerate), t0 = diagonal exit of Newton polyhedron of g.
def newton_t0(support):
    # support: list of exponent vectors (monomials with nonzero coeff). t0=min t: (t..t) in conv(support)+R+^n
    support=[np.array(s,float) for s in support]; n=len(support[0]); K=len(support)
    c=np.zeros(K+1); c[-1]=1.0
    A_ub=[]; b_ub=[]
    for i in range(n):
        row=np.zeros(K+1); 
        for k in range(K): row[k]=support[k][i]
        row[-1]=-1.0; A_ub.append(row); b_ub.append(0.0)
    A_eq=[np.concatenate([np.ones(K),[0.0]])]; b_eq=[1.0]
    res=linprog(c,A_ub=np.array(A_ub),b_ub=np.array(b_ub),A_eq=np.array(A_eq),b_eq=np.array(b_eq),
                bounds=[(0,None)]*K+[(None,None)])
    return res.fun
def local_rlct(loss_poly, allv):
    poly=sp.Poly(loss_poly,*allv)
    # Hessian at 0
    H=sp.hessian(loss_poly, allv).subs({v:0 for v in allv})
    H=sp.Matrix(H); r=H.rank(); ns=H.nullspace()
    n=len(allv)
    if not ns:
        return sp.Rational(r,2), r, "all-Morse (rlct=rank/2)"
    # restrict to kernel: x = sum_k y_k * ns[k]
    y=sp.symbols(f'y0:{len(ns)}')
    subs={}
    Kmat=sp.Matrix.hstack(*ns)   # n x len(ns)
    xvec=Kmat*sp.Matrix(y)
    g=sp.expand(loss_poly.subs({allv[i]:xvec[i] for i in range(n)}))
    if g==0:
        return sp.Rational(r,2), r, "residual identically 0 on ker (rlct=rank/2, kernel tangent)"
    gp=sp.Poly(g,*y)
    supp=[m for m in gp.monoms()]
    t0=newton_t0(supp)
    rl_g=sp.Rational(1)/sp.nsimplify(t0, rational=True) if t0 else sp.oo
    return sp.Rational(r,2)+rl_g, r, f"residual deg-support t0={t0:.4f}, rlct(g)={float(rl_g):.4f}, #ker={len(ns)}"

def dln_loss_germ(bases):
    p=len(bases); shapes=[sp.Matrix(b).shape for b in bases]
    syms=[]; pert=[]
    for i,sh in enumerate(shapes):
        s=sp.symbols(f'p{i}_0:{sh[0]*sh[1]}'); syms+=list(s); pert.append(sp.Matrix(sh[0],sh[1],s))
    Ls=[sp.Matrix(bases[i])+pert[i] for i in range(p)]
    Z=Ls[0]
    for L in Ls[1:]: Z=Z*L
    Z=sp.expand(Z)
    # verify fiber point
    Zb=sp.Matrix(bases[0])
    for b in bases[1:]: Zb=Zb*sp.Matrix(b)
    assert sp.expand(Zb)==sp.zeros(*Zb.shape), "not a fiber point"
    loss=sp.expand(sum(z**2 for z in Z))
    return loss, syms

# VALIDATE on knowns
print("=== validation ===")
# (2,2,2) origin: 2-layer, rlct should be 3/2
loss,vs=dln_loss_germ([sp.zeros(2,2), sp.zeros(2,2)])
print("(2,2,2) origin:", local_rlct(loss,vs), " expect 3/2")
# single matrix (2,2): rlct=2
loss,vs=dln_loss_germ([sp.zeros(2,2)])
print("single 2x2 origin:", local_rlct(loss,vs), " expect 2")
