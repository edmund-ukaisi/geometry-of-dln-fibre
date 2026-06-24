import sympy as sp
# Try to COMPLETE THE SQUARE on E to absorb the cross terms. If F_E = Σ a_i (E_i - β_i(core))² + G'(core)
# with a_i a positive unit and the shift E_i ↦ E_i - β_i an MP (translation) change of vars, THEN we'd
# have a clean factorisation F∘χ = (unit)·(ΣEᵢ'² ) + G'. The question: is the leftover G' E-FREE and does
# it equal the Schur core ‖S·A2red‖²?  AND is the shift β_i a valid (smooth, MP) c-o-v near 0?
p,q,r,s,t,u_,v,w = sp.symbols('p q r s t u v w', real=True)
b = sp.symbols('b0:9', real=True)
Ahat = sp.Matrix([[1,p,q],[r,s,t],[u_,v,w]])
A2 = sp.Matrix(3,3,b)
M = sp.expand(Ahat*A2)
def fro2(X): return sp.expand(sum(X[i,j]**2 for i in range(X.rows) for j in range(X.cols)))
F = fro2(M)
E0,E1,E2 = sp.symbols('E0 E1 E2', real=True)
sub = {b[0]: E0 - p*b[3] - q*b[6], b[1]: E1 - p*b[4] - q*b[7], b[2]: E2 - p*b[5] - q*b[8]}
F_E = sp.expand(F.subs(sub))

# F_E is quadratic in (E0,E1,E2). Its E-quadratic form: each E_i has coeff (1+r²+u²) (diagonal, no E_iE_j cross? check).
# Cross E_iE_j:
for i,Ei in enumerate([E0,E1,E2]):
    for j,Ej in enumerate([E0,E1,E2]):
        if i<j:
            print(f"coeff E{i}E{j} =", sp.Poly(F_E,E0,E1,E2).coeff_monomial(Ei*Ej))
a = sp.Poly(F_E,E0,E1,E2).coeff_monomial(E0**2)
print("a (= coeff E_i², same for all i) =", a)
# Complete square: F_E = a·Σ(E_i + lin_i/(2a))² + [G' = E-free remainder]. lin_i = coeff of E_i.
Gprime = F_E
shifts = {}
for Ei in [E0,E1,E2]:
    lin = sp.expand(F_E.diff(Ei).subs({E0:0,E1:0,E2:0}))  # linear coeff in E_i
    beta = sp.simplify(-lin/(2*a))
    shifts[Ei] = beta
# G' = F_E with E_i -> beta_i (the minimum over E) -- the E-free completed-square remainder:
Gprime = sp.expand(F_E.subs({E0:shifts[E0], E1:shifts[E1], E2:shifts[E2]}))
Gprime = sp.simplify(Gprime)
print("\nCompleted-square shift β0 = -lin0/(2a) =", sp.simplify(shifts[E0]))
print("\nE-free completed-square remainder G' = min_E F_E =")
print(Gprime)

# Now compare G' to the Schur core ‖S·A2red‖² (S=D-ba, the g127 reduced node):
S = sp.Matrix([[s-p*r, t-q*r],[v-p*u_, w-q*u_]])
A2red = A2[1:,:]   # rows 1,2 of original A2 (b3..b8) -- note these are NOT substituted (E only touched b0,b1,b2)
Score = fro2(sp.expand(S*A2red))
print("\nSchur core ‖S·A2red‖² =", sp.expand(Score))
print("\nG' - ‖S·A2red‖² =", sp.simplify(Gprime - Score))
