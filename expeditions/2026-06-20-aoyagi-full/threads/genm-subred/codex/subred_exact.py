import sympy as sp
print("="*72)
print("EXACT threshold certificates (no MC) -- the twist, decisively")
print("="*72)

# (b=1,m=1,q=2): Y=y (1x1), A=(a1,a2) (1x2). Qb = y*(a1,a2).
y,a1,a2 = sp.symbols('y a1 a2', real=True)
Qb = sp.Matrix([[y*a1, y*a2]])
G = Qb*Qb.T
det = sp.factor(G.det())
print("(b=1,m=1,q=2): det(QbQb^T) =", det)
print("  = y^2 * (a1^2+a2^2).  det^{-a/2} = |y|^{-a} * (a1^2+a2^2)^{-a/2}.")
print("  int|y|^{-a}dy < inf  iff a<1  ;  int(a1^2+a2^2)^{-a/2} < inf iff a<2.")
print("  PRODUCT finite iff a<1  =  min(m,q)-b+1 = min(1,2)-1+1 = 1.")
print("  FREE q-b+1 = 2.  ==> twist LOWERS 2 -> 1.  [J = |y|^{-a}, the deeper Gram]")
print()

# The recursion made literal via the |y| factor = a lower-chain Gram weight.
# (b=1,m1=1,m2=2,q=2): Y=y, A2=(u1,u2) 1x2, A3 2x2. Qb = y * (A2 A3).
u1,u2 = sp.symbols('u1 u2', real=True)
A3 = sp.Matrix(2,2, lambda i,j: sp.Symbol(f'c{i}{j}', real=True))
A2 = sp.Matrix([[u1,u2]])
Qb3 = y*(A2*A3)
G3 = (Qb3*Qb3.T)
det3 = sp.factor(G3.det())
print("(b=1,m1=1,m2=2,q=2): det(QbQb^T) =")
print("   ", det3)
print("  factors as y^2 * ||A2 A3||^2  -> int|y|^{-a} caps a<1 = min(1,2,2)-1+1.")
print("  The narrow INTERNAL width m1=1 (not the final q=2) sets the threshold.")
print()
print("="*72)
print("wtint SUBMERSION-SCOPE audit: is 'codim q-b+1' right for M2<q ?")
print("="*72)
print("Y (b x M2) -> Q = Y*Atail (b x q).  Submersion onto R^{b x q} needs")
print("rank(Atail)=q  <=>  M2>=q.  If b<=M2<q: rank(Atail)=M2>=b (Q CAN be full")
print("rank b), BUT image = (rowspace Atail)^b has dim b*M2 < b*q -- NOT onto.")
print("Pullback of {rank Qb<b} has codim rank(Atail)-b+1 = min(M2,q)-b+1,")
print("NOT q-b+1.  wtint conflated 'rank>=b' (Q full rank possible) with")
print("'submersion' (needs rank=q).  'same codim q-b+1' holds ONLY for M2>=q.")
