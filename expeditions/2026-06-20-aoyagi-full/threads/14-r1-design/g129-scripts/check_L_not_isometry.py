import sympy as sp
# CRUX CHECK 1: Is ‖Â A2‖² = ‖L·(Â A2)‖²?  L is unipotent (det 1) but NOT orthogonal.
# If ‖M‖² ≠ ‖L M‖², the g127 "loss identity" does NOT preserve the loss VALUE — it block-diagonalizes
# the MATRIX but the Frobenius norm (the loss) is NOT invariant under left-mult by a non-orthogonal L.
p,q,r,s,t,u_,v,w = sp.symbols('p q r s t u v w', real=True)
b = sp.symbols('b0:9', real=True)
Ahat = sp.Matrix([[1,p,q],[r,s,t],[u_,v,w]]); A2 = sp.Matrix(3,3,b)
M = sp.expand(Ahat*A2)
L = sp.Matrix([[1,0,0],[-r,1,0],[-u_,0,1]])
R = sp.Matrix([[1,-p,-q],[0,1,0],[0,0,1]])

def fro2(X):
    return sp.expand(sum(X[i,j]**2 for i in range(X.rows) for j in range(X.cols)))

normM   = fro2(M)
normLM  = fro2(sp.expand(L*M))
print("‖Â A2‖²  - ‖L·(Â A2)‖²  = ", sp.simplify(normM - normLM))
print("   (if NONZERO: L is NOT an isometry; the loss VALUE changes under the g127 left-mult)")

# Also check ‖Â A2‖² vs ‖(L Â R)(R⁻¹ A2)‖² = ‖L Â A2‖² (R R⁻¹ cancels) — same as above.
# And check ‖Â A2‖² vs ‖blockdiag[1,S] · (R⁻¹ A2)‖² which is what a real c-o-v on A2 would give:
Rinv = R.inv()
A2new = sp.expand(Rinv*A2)
BD = sp.expand(L*Ahat*R)
prod2 = sp.expand(BD*A2new)
print("\nblockdiag[1,S]·(R⁻¹A2) - L·Â·A2 =", sp.simplify(prod2 - sp.expand(L*M)), " (0 ⟹ same matrix)")
print("‖blockdiag·(R⁻¹A2)‖² - ‖Â A2‖² =", sp.simplify(fro2(prod2) - normM))
