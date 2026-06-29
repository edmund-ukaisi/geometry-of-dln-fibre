import sympy as sp, random
random.seed(5)
x=sp.symbols('x0:27',real=True);u=x[0];active=[13,14,24,25,26]
B1=sp.Matrix([[x[1],x[1]*x[2]],[x[1]*x[3],x[1]*x[2]*x[3]+x[4]],[x[1]*x[3]*x[6]+x[1]*x[5],x[1]*x[2]*x[5]+x[6]*(x[1]*x[2]*x[3]+x[4])]])
B2=sp.Matrix([[x[9]],[x[10]*x[9]]]);N1=sp.Matrix([[x[7]],[x[8]]]);N2=sp.Matrix([[x[11],x[12]]])
W1=sp.Matrix([[x[15],x[16],x[17]]]);W2=sp.Matrix([[x[18],x[19],x[20]],[x[21],x[22],x[23]]])
R1=sp.Matrix([[0,0,0],[0,0,0],[0,0,1]]);R2=sp.Matrix([[0,0,0],[0,x[13],x[14]]]);Rf=sp.Matrix([[x[24],x[25],x[26]]])
C3=u*Rf;C2=B2*sp.Matrix.hstack(sp.eye(1),N2)+u*R2;C1=B1*sp.Matrix.hstack(sp.eye(2),N1)+u*R1
A0=C1;A1=sp.Matrix.vstack(C2-N1*W1,W1);A2=sp.Matrix.vstack(C3-N2*W2,W2)
phi=[sp.expand(A[i,j]) for A in (A0,A1,A2) for i in range(A.rows) for j in range(A.cols)]
n=27; y=sp.symbols('y0:27',real=True)
sub={x[i]: y[i] for i in range(n)}; sub[u]=y[0]
for i in active: sub[x[i]]=y[i]/y[0]
B=[sp.cancel(e.subs(sub,simultaneous=True)) for e in phi]
JB=sp.Matrix(B).jacobian(sp.Matrix(list(y)))
# det DB should be u-free and = the boundary monomial in the K/q pivots. The full chart det = u^5 * (boundary).
# det DB must equal that boundary = y1^4 * y4^2 * y9^3  (the |K_s|^{r+c}*q-prod part).
# Keep y1,y4,y9 symbolic, randomize the rest exact-rational, check det DB matches c*y1^4 y4^2 y9^3.
keep={1,4,9}
s2={v: sp.Rational(random.randint(-9,9),random.randint(1,6)) for i,v in enumerate(y) if i not in keep}
detB=sp.factor(sp.cancel(JB.subs(s2).det()))
print("det DB (y1,y4,y9 symbolic; rest exact rational) =", detB)
# compare exponent structure to y1^4 y4^2 y9^3
P=sp.Poly(sp.expand(sp.numer(sp.together(JB.subs(s2).det()))), y[1],y[4],y[9])
print("monomials (e1,e4,e9):", [m for m,_ in P.terms()], " (expect single (4,2,3))")
print("y0 in det DB?", y[0] in detB.free_symbols, " (expect False -- DB is u-free)")
