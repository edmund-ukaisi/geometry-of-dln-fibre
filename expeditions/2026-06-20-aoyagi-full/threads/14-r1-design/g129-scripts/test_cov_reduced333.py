import sympy as sp
# The HONEST question: at the (3,3,3) reduced node, F = ‖Â A2‖², Â[0,0]=1 (hard pivot).
# Coordinates (the LOSS's parameter coords): Â's free entries p,q,r,s,t,u,v,w (8) and A2's 9 entries.
# Is there an MEASURE-PRESERVING change of variables χ on THESE 17 coords such that
#   F∘χ = u(coords)·( Σ Eᵢ² + G² ),  u a bounded unit, G E-free?
#
# The natural candidate c-o-v (the "right" one suggested by g127): change A2 ↦ R⁻¹ A2 is NOT what we want;
# instead we want to introduce NEW regular coords E := (row0 of Â A2) and keep a reduced E-free core.
#
# F = ‖Â A2‖² = Σ_j (row0 of ÂA2)_j² + Σ_j (row1 of ÂA2)_j² + Σ_j (row2 of ÂA2)_j².
# row0 of ÂA2 = (A2row0) + p(A2row1) + q(A2row2)  [since Â row0 = (1,p,q)]
# rows 1,2 are bilinear-ish. The g127 idea: the LOWER rows, after the col-clear R on A2, become S·A2red.
# But the col-clear changes A2's coords, and the ROW0 (the E's) also change under that.
#
# Let me set up the candidate MP c-o-v honestly and test F∘χ.
p,q,r,s,t,u_,v,w = sp.symbols('p q r s t u v w', real=True)
b = sp.symbols('b0:9', real=True)
Ahat = sp.Matrix([[1,p,q],[r,s,t],[u_,v,w]])
A2 = sp.Matrix(3,3,b)
M = sp.expand(Ahat*A2)
def fro2(X): return sp.expand(sum(X[i,j]**2 for i in range(X.rows) for j in range(X.cols)))
F = fro2(M)

# Candidate: introduce E_j := M[0,j] = (ÂA2)[0,j]  (the 3 regular pivot-row entries), j=0,1,2.
# These 3 are "regular" generators (unit pivot in A2 row0: ∂E_j/∂b_j = 1). They can be straightened to
# coordinates by a UNIT-JAC (det=1 since lower-triangular w/ 1's) change of A2's row0:  b_j ↦ E_j.
# After that, rows 1,2 of M depend on (r,s,t,u,v,w,p,q) and b3..b8 — these are the "E-free core" candidate?
# NO: rows 1,2 of M = Â rows 1,2 times A2, and A2 row0 (now expressed via E) STILL appears (Â[1,0]=r times A2row0).
# So row1 = r·A2row0 + s·A2row1 + t·A2row2;  A2row0 = E - p·A2row1 - q·A2row2 (inverting the E-def).
# => row1 = r·(E - p A2row1 - q A2row2) + s A2row1 + t A2row2 = r·E + (s-pr)A2row1 + (t-qr)A2row2
#         = r·E + [S row0]·A2red   where S=[[s-pr,t-qr],[v-pu,w-qu]], A2red = rows1,2.
# SO rows 1,2 = r·E (resp u·E) + S·A2red.  The E-dependence does NOT vanish — it has coefficient r (resp u).
# Substitute b0,b1,b2 -> E0,E1,E2 (with b0 = E0 - p b3 - q b6, etc.) and recompute F:
E0,E1,E2 = sp.symbols('E0 E1 E2', real=True)
sub = {b[0]: E0 - p*b[3] - q*b[6], b[1]: E1 - p*b[4] - q*b[7], b[2]: E2 - p*b[5] - q*b[8]}
F_E = sp.expand(F.subs(sub))
# Now: is F_E = E0²+E1²+E2² + (E-free core)?  Check the E-free part and the cross/coupling.
# Collect terms by E-degree.
poly = sp.Poly(F_E, E0, E1, E2)
print("=== F in (E0,E1,E2) coords (b0,b1,b2 replaced) ===")
# E-free part (the would-be core G):
Efree = F_E.subs({E0:0,E1:0,E2:0})
Efree = sp.expand(Efree)
print("E-free part G_core =", Efree)
# pure-quadratic-in-E part:
quad = sp.expand(F_E - Efree)
print("\nE-dependent part (should be Σ Eᵢ² if clean) =")
print(quad)
# Extract coefficient of E0² and the cross/linear-in-E terms:
print("\ncoeff E0² =", poly.coeff_monomial(E0**2))
print("coeff E0 (linear) =", sp.expand(F_E.diff(E0).subs({E0:0,E1:0,E2:0})))
