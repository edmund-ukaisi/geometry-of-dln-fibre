import sympy as sp
a,l,w,p,q,t = sp.symbols('a l w p q t', real=True)

# rational orthogonal frame of R^3
n  = sp.Matrix([1,p,q])
f1 = sp.Matrix([-p,1,0])
f2 = sp.Matrix([-q,-p*q,1+p**2])
print("(i) orthogonality & norms:")
print("  <n,f1> =",sp.simplify(n.dot(f1)),"  <n,f2> =",sp.simplify(n.dot(f2)),"  <f1,f2> =",sp.simplify(f1.dot(f2)))
D = sp.simplify(n.dot(n)); nf1=sp.simplify(f1.dot(f1)); nf2=sp.simplify(f2.dot(f2))
print("  ||n||^2 =",D,"  ||f1||^2 =",nf1,"  ||f2||^2 =",sp.factor(nf2),"  (expect D, 1+p^2, (1+p^2)D)")

# A1 rows
row1 = a*n
row2 = l*n + w*(f1 + t*f2)
A1 = sp.Matrix.hstack(row1, row2).T          # 2x3
# ---- Jacobian of Phi:(a,l,w,p,q,t) -> vec(A1) (6 entries) ----
vecA1 = sp.Matrix([A1[i,j] for i in range(2) for j in range(3)])
Jac = vecA1.jacobian(sp.Matrix([a,l,w,p,q,t]))
detJ = sp.simplify(Jac.det())
print("\n(iii) |det DPhi| =", sp.factor(detJ), "   (expect a^2 * w * (1+p^2) * D)")
print("      matches a^2*w*(1+p^2)*D ?", sp.simplify(detJ - a**2*w*(1+p**2)*D)==0,
      " or with sign:", sp.simplify(sp.Abs(detJ) - sp.Abs(a**2*w*(1+p**2)*D))==0)

# ---- loss L = ||A0 A1||^2 with A0=[x|y], and the front shear g = x + (l/a) y ----
x = sp.Matrix(sp.symbols('x0 x1 x2', real=True))
y = sp.Matrix(sp.symbols('y0 y1 y2', real=True))
A0 = sp.Matrix.hstack(x,y)                    # 3x2
P = A0*A1                                      # 3x3
L = sp.expand(sum(P[i,j]**2 for i in range(3) for j in range(3)))
g = x + (l/a)*y
claim = D*a**2*(g.dot(g)) + (1+p**2)*(1+D*t**2)*w**2*(y.dot(y))
print("\n(ii) L - [ D a^2||g||^2 + (1+p^2)(1+D t^2) w^2 ||y||^2 ] == 0 :",
      sp.simplify(L - claim)==0)
print("     => loss is EXACTLY block-additive (no cross term) in this chart.")

# ---- lower bound feeding qPeel: L >= a^2||g||^2 + w^2||y||^2 (since D>=1, (1+p^2)(1+Dt^2)>=1) ----
print("\n(charge) qPeel data: (h_a,h_w)=(2,1) from Jacobian a^2 w ; blocks g,y in R^3 => (m_a,m_w)=(2,2)")
print("   gates 2<=2, 1<=2 hold ; threshold 1/2*((2+1)+(1+1)) =", sp.Rational((2+1)+(1+1),2), " = 5/2  TIGHT")
