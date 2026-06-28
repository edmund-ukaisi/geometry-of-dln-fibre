import sympy as sp
# Name blocks directly to avoid row-major confusion.
m11 = sp.Matrix(2,2, sp.symbols('p0 p1 p2 p3', real=True))
m12 = sp.Matrix(2,2, sp.symbols('q0 q1 q2 q3', real=True))   # spectator (M12)
m21 = sp.Matrix(2,2, sp.symbols('s0 s1 s2 s3', real=True))   # spectator (M21)
m22 = sp.Matrix(2,2, sp.symbols('w0 w1 w2 w3', real=True))   # the M22 block
Sc = m22 - m21*m11.inv()*m12
m22vars = list(m22)
print("Sc - M22 contains any M22 vars (w*)?",
      (set(Sc - m22).pop().free_symbols if False else (set().union(*[ (e-m).free_symbols for e,m in zip(Sc, m22)]) & set(m22vars))) or "NONE")
# Jacobian d(Sc)/d(M22)
Scflat = list(Sc); 
J = sp.Matrix(4,4, lambda i,k: sp.diff(Scflat[i], m22vars[k]))
print("d(Sc)/d(M22) =")
sp.pprint(J)
print("det =", sp.simplify(J.det()), "  (identity => TRANSLATION, Jac=1, for j=2)")
