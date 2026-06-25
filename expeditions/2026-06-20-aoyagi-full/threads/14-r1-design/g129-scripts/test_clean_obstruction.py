import sympy as sp
# OBSTRUCTION: can ANY change of variables χ (MP or not) bring F to the LITERAL clean form
# u·(ΣEᵢ² + G²) with u(0)≠0 and G E-free? Necessary condition via the 2-jet (Hessian) at a generic
# nearby point, or via the structure of the lowest-degree part. Here all gens are bilinear ⇒ F is a
# sum of products of two linear forms; its lowest-degree part is degree 2. Examine the degree-2 part:
p,q,r,s,t,u_,v,w = sp.symbols('p q r s t u v w', real=True)
b = sp.symbols('b0:9', real=True)
Ahat = sp.Matrix([[1,p,q],[r,s,t],[u_,v,w]]); A2 = sp.Matrix(3,3,b)
M = sp.expand(Ahat*A2)
def fro2(X): return sp.expand(sum(X[i,j]**2 for i in range(X.rows) for j in range(X.cols)))
F = fro2(M)
allv = [p,q,r,s,t,u_,v,w]+[b[i] for i in range(9)]
# lowest-degree (deg-2) part of F at 0:
# get degree-2 homogeneous part:
poly = sp.Poly(F,*allv)
terms = poly.terms()
F_deg2 = sum(sp.prod(v**e for v,e in zip(allv,monom))*coeff for monom,coeff in terms if sum(monom)==2)
F_deg2 = sp.expand(F_deg2)
print("Lowest-degree (deg-2) part of F at origin:")
print(" ", F_deg2)
# The clean form u·(ΣEᵢ²+G²) with u(0)=u0>0: its deg-2 part = u0·(ΣEᵢ(lin)² + Gquad?) — but Eᵢ are
# the regular gens E_j = M[0,j] = b_{j} + p·b_{3+j}+q·b_{6+j}; their LINEAR parts (at 0) are just b_j.
# So Σ Eᵢ² has deg-2 part = b0²+b1²+b2². G is E-free, G(0)=0; if G is the Schur-core sqrt, G is bilinear ⇒
# G² is deg-4, contributing NOTHING at deg 2. So clean-form deg2 = u0·(b0²+b1²+b2²) — RANK 3 quadratic.
# Compare F's deg-2 part:
print("\nF_deg2 as a quadratic form — its rank:")
Q = sp.hessian(F_deg2, allv)/2  # /2 since hessian of x² is 2
rank = Q.rank()
print("  rank of deg-2 quadratic form of F =", rank, "(only b0²+b1²+b2² present?)")
print("  F_deg2 depends only on b0,b1,b2? ", F_deg2.free_symbols == {b[0],b[1],b[2]})
# So at deg-2, F = b0²+b1²+b2², rank 3. That's EXACTLY ΣEᵢ²'s deg-2 part (rank 3). Consistent w/ clean form
# having deg2 = u0·rank3. So the OBSTRUCTION is NOT at deg 2. The coupling (the reason clean form fails)
# is at deg 3-4: the cross terms 2·E·(core-perturbation). Confirm the deg-3 part couples b0,b1,b2 with core:
F_deg3 = sp.expand(sum(sp.prod(v**e for v,e in zip(allv,monom))*coeff for monom,coeff in terms if sum(monom)==3))
print("\nF deg-3 part (the COUPLING that blocks the clean form) =", F_deg3)
print("  deg-3 part nonzero ⟹ F has odd-degree cross terms between the regular block (b0,b1,b2) and core")
print("  vars — a clean u·(ΣEᵢ²+G²) (with G bilinear ⟹ G² deg-4 EVEN) has NO deg-3 part. CONTRADICTION.")
