import sympy as sp
# 3-layer chain (2,2,2,2): Z = L2 L1 L0, each 2x2. Compute the LOCAL loss germ at an intermediate
# fiber point x0 and read its Newton polyhedron / leading form (chain-like=benign vs cyclic=deficit).
# x0: L0=diag(1,0) rank1, L1=diag(0,1) rank1 (so L1 L0=0 => Z=0), L2=I.  A GENUINE intermediate deep point.
e=sp.symbols('e')   # single scale for homogeneity read
# perturbation variables
a=sp.symbols('a0:4'); b=sp.symbols('b0:4'); c=sp.symbols('c0:4')
A=sp.Matrix(2,2,a); B=sp.Matrix(2,2,b); C=sp.Matrix(2,2,c)
L0=sp.Matrix([[1,0],[0,0]])+A
L1=sp.Matrix([[0,0],[0,1]])+B
L2=sp.eye(2)+C
Z=sp.expand(L2*L1*L0)
loss=sp.expand(sum(z**2 for z in Z))
# leading (lowest total-degree) part in the perturbations a,b,c
allv=list(a)+list(b)+list(c)
poly=sp.Poly(loss, *allv)
mindeg=min(sum(m) for m in poly.monoms())
print("min total degree of loss germ at x0 =",mindeg)
lead=sum(coef*sp.prod([v**k for v,k in zip(allv,m)]) for m,coef in poly.terms() if sum(m)==mindeg)
print("leading form:", sp.simplify(lead))
# which variables appear in the leading form, and its structure
lp=sp.Poly(lead,*allv)
print("leading-form monomials (exponent tuples over a0..a3,b0..b3,c0..c3):")
for m,cf in lp.terms(): 
    supp={allv[i]:m[i] for i in range(len(m)) if m[i]>0}
    print("   ",cf, supp)
