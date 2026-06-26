import sympy as sp
# (C1) vs (C2): is the det-1 GL-straightening a NEEDED piece, or can pure blow-up (C1) do it alone?
#
# THE DECISIVE TEST: take the (2,2,2) zero-core F = ||A1 A2||^2. The resolution's FIRST node.
# (C1) reading: directly blow up a rank-defect center (a coordinate-subspace) and read off monomial×core.
# (C2) reading: first GL-straighten (det-1) so the center IS a coordinate subspace, THEN blow up.
#
# The center to blow up = the rank-defect stratum. For ||A1 A2||^2 the deepest is {A1=0} (or {A2=0}).
# {A1=0} IS ALREADY a coordinate subspace (the 4 entries of A1 = 0)! No GL-straightening needed to
# blow it up. So the FIRST blow-up {A1=0} is pure (C1) -- coordinate subspace, no straightening.
a=sp.symbols('a0:4'); b=sp.symbols('b0:4'); x=sp.symbols('x')
print("=== (2,2,2) zero-core, first node: blow up {A1=0} (a coordinate subspace, NO straightening) ===")
# chart: A1 = x*Ahat, Ahat[0,0]=1. i.e. a0=x, a1=x*p, a2=x*q, a3=x*r. Jacobian of (x,p,q,r,b)->(a,b):
p,q,r=sp.symbols('p q r')
A1=sp.Matrix([[x, x*p],[x*q, x*r]]); A2=sp.Matrix(2,2,b)
P=sp.expand(A1*A2)
F=sp.expand(sum(P[i,j]**2 for i in range(2) for j in range(2)))
print("  F = ||A1 A2||^2 pulled back =", sp.factor(F))
# Jacobian of (a0,a1,a2,a3)=(x,xp,xq,xr) wrt (x,p,q,r):
J=sp.Matrix([[x,x*p],[x*q,x*r]])
jac=sp.Matrix([[sp.diff(e, v) for v in [x,p,q,r]] for e in [x, x*p, x*q, x*r]])
print("  |Jacobian| =", sp.factor(jac.det()), "= x^3 (the codim-4 blow-up Jacobian, h=3)")
print("  F = x^2 * ||Ahat A2||^2, Ahat[0,0]=1 (now a UNIT).")
print()
print("=> The FIRST blow-up {A1=0} is pure (C1): coordinate subspace, NO GL-straightening needed.")
print("   It produces x^2 * ||Ahat A2||^2 with Ahat[0,0] a unit.")
print()
print("=== Now: is GL-straightening (det-1) needed for the NEXT step? ===")
print("After: ||Ahat A2||^2, Ahat[0,0]=1 unit. The residual rank-defect center is NOT a clean coordinate")
print("subspace in the (p,q,r,b) coords -- it's {Ahat A2 has rank defect}. To blow it up as a coordinate")
print("subspace, you FIRST straighten (Lemma-2 / det-1 Schur: clear Ahat's pivot row/col of the product),")
print("making the residual center {E=F0=delta=0} a coordinate subspace. THEN blow up.")
print("So the det-1 Schur IS needed at the 2nd+ nodes to EXPOSE the coordinate-subspace center.")
