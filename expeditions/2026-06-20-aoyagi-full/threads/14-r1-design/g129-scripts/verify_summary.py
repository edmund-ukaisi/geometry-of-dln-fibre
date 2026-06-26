import sympy as sp
# CONSOLIDATED VERIFICATION (the load-bearing exact facts, all in one place):
p,q,r,s,t,u_,v,w = sp.symbols('p q r s t u v w', real=True)
b = sp.symbols('b0:9', real=True)
Ahat = sp.Matrix([[1,p,q],[r,s,t],[u_,v,w]]); A2 = sp.Matrix(3,3,b)
M = sp.expand(Ahat*A2)
def fro2(X): return sp.expand(sum(X[i,j]**2 for i in range(X.rows) for j in range(X.cols)))
F = fro2(M)
L = sp.Matrix([[1,0,0],[-r,1,0],[-u_,0,1]]); R = sp.Matrix([[1,-p,-q],[0,1,0],[0,0,1]])
# FACT 1: L,R det=1
print("FACT 1  det L =", L.det(), ", det R =", R.det(), " (both transvections, det=1)")
# FACT 2: matrix identity L Â R = blockdiag[1,S]
S = sp.Matrix([[s-p*r,t-q*r],[v-p*u_,w-q*u_]])
BD = sp.zeros(3); BD[0,0]=1; BD[1:,1:]=S
print("FACT 2  L·Â·R - blockdiag[1,S] =", sp.simplify(L*Ahat*R - BD), " (matrix identity holds)")
# FACT 3: L NOT an isometry => loss VALUE not preserved by the transvection
diff = sp.expand(F - fro2(sp.expand(L*M)))
print("FACT 3  ‖ÂA2‖² - ‖L(ÂA2)‖² ≡ 0 ?", diff==0, " (FALSE ⟹ transvection changes the loss VALUE)")
# FACT 4: F has a degree-3 part (odd) => not literal u·(ΣE²+G²) with bilinear G
allv=[p,q,r,s,t,u_,v,w]+[b[i] for i in range(9)]; poly=sp.Poly(F,*allv)
d3=sp.expand(sum(sp.prod(v**e for v,e in zip(allv,mo))*co for mo,co in poly.terms() if sum(mo)==3))
print("FACT 4  deg-3 part of F =", d3, " (nonzero ⟹ no literal even clean form)")
# FACT 5: structural squeeze  F - Φ ∈ ideal(E),  Φ = ΣE² + ‖S·A2red‖²
E=[M[0,j] for j in range(3)]; Phi=sp.expand(sum(e**2 for e in E)+fro2(sp.expand(S*A2[1:,:])))
subE={b[0]:-(p*b[3]+q*b[6]), b[1]:-(p*b[4]+q*b[7]), b[2]:-(p*b[5]+q*b[8])}
print("FACT 5  (F-Φ)|{E=0} =", sp.simplify((F-Phi).subs(subE)), " (0 ⟹ F-Φ ∈ ideal(E): structural squeeze)")
# FACT 6: the MP completed-square c-o-v gives a·ΣE'² + G', a=1+r²+u² a unit (not single overall unit)
sub={b[0]:sp.Symbol('E0')-p*b[3]-q*b[6], b[1]:sp.Symbol('E1')-p*b[4]-q*b[7], b[2]:sp.Symbol('E2')-p*b[5]-q*b[8]}
FE=sp.expand(F.subs(sub)); E0,E1,E2=sp.symbols('E0 E1 E2')
aa=sp.Poly(FE,E0,E1,E2).coeff_monomial(E0**2)
print("FACT 6  E-square coeff after MP rename =", aa, " (a unit ≠1 ⟹ weighted, not clean single-unit form)")
