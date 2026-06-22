import sympy as sp
# THE CONTROLLER'S ROUTE: deepest core = the LEADING HOMOGENEOUS PART of every v's core. Does this give
# rlctAt(deepest) ≤ rlctAt(v) value-independently, AVOIDING the semicontinuity primitive (L1-b)?
#
# Setup: at a general fibre point v, the core (in v's local coords w) is F_v(w) = ‖∏(v+w)‖² (B=0 core,
# v ∈ {∏=0}). Expand in w: F_v(w) = (leading form) + (higher order). The LEADING form (lowest degree in
# w) — is it the deepest core ‖∏(w)‖²? And does leading-form domination give the rlct inequality?
#
# Concrete: (2,2,2) B=0, deepest=0, F(w)=‖A1 A2‖² (A1,A2 the two 2×2 layers, w=(A1,A2)). A general v with
# A1,A2 ≠ 0, ∏=0. Take v: A1=[[1,0],[0,0]], A2=[[0,0],[0,1]] (A1 A2=0). F_v(w) = ‖(A1+w1)(A2+w2)‖²,
# w1,w2 the layer perturbations. Leading (lowest-degree) form in (w1,w2)?
a = sp.symbols('a0:4'); b = sp.symbols('b0:4')  # w1 = perturbation of A1, w2 of A2
A1v = sp.Matrix([[1,0],[0,0]]); A2v = sp.Matrix([[0,0],[0,1]])
W1 = sp.Matrix(2,2,a); W2 = sp.Matrix(2,2,b)
P = sp.expand((A1v+W1)*(A2v+W2))
Fv = sp.expand(sum(P[i,j]**2 for i in range(2) for j in range(2)))
allw = list(a)+list(b)
# lowest-degree part of Fv in w:
poly = sp.Poly(Fv, *allw)
mindeg = min(sum(mono) for mono in poly.monoms())
leading = sum(sp.prod(v**e for v,e in zip(allw,mono))*co for mono,co in poly.terms() if sum(mono)==mindeg)
print(f"=== (2,2,2) B=0: F_v(w) at v=(rank1,rank1 aligned), leading-form degree = {mindeg} ===")
print(f"  F_v leading form (deg {mindeg}) = {sp.expand(leading)}")
# the DEEPEST core F_0(w) = ‖W1 W2‖², lowest-degree = degree 4 (bilinear² ). Compare degrees:
F0 = sp.expand(sum((W1*W2)[i,j]**2 for i in range(2) for j in range(2)))
print(f"  deepest core F_0(w)=‖W1 W2‖² lowest degree = {min(sum(m) for m in sp.Poly(F0,*allw).monoms())} (=4, the homogeneous core)")
print()
print("OBSERVATION: F_v's leading form has degree", mindeg, "(LOWER than the deepest's degree 4) — the")
print("leading form is NOT the deepest core; it's a LOWER-degree form (v's regular directions give")
print("quadratic leading terms). So 'deepest core = leading part of v's core' is FALSE as stated — the")
print("leading part of F_v is LOWER degree (less vanishing) than the deepest core. This is the OPPOSITE")
print("of what's needed (deepest should be MORE vanishing = higher leading degree).")
print()
print("RECONCILE: rlct is governed by the LEADING (Newton) behavior — LOWER leading degree = LESS singular")
print("= LARGER rlct. F_v has leading degree", mindeg, "< 4 = deepest's ⟹ rlct(v) ≥ rlct(deepest)? Let me")
print("check: lower leading degree ⟹ larger rlct (for the leading form's rlct). deepest leading deg 4,")
print("v leading deg", mindeg, ". If rlct ~ (controlled by leading form) and lower-degree leading ⟹ larger")
print("rlct, then rlct(deepest) ≤ rlct(v). ✓ direction. BUT this needs 'rlct = rlct of the leading form'")
print("(Newton-nondegeneracy / the leading form determines the rlct) — which is ITSELF a nontrivial")
print("analytic fact (NOT automatic; needs the leading form to be 'non-degenerate' à la Varchenko).")
