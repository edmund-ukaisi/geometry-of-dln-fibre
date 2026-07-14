import sympy as sp
# Exact rational det at fully-numeric rational points: compare to -8*Vand/(1+|S|^2)^2.
a_,b_,c_,l1,l2,l3=sp.symbols('a_ b_ c_ l1 l2 l3')
I3=sp.eye(3)
S2=sp.Matrix([[0,-c_,b_],[c_,0,-a_],[-b_,a_,0]])
Q2=(I3-S2)*(I3+S2).inv()
G2=Q2*sp.diag(l1,l2,l3)*Q2.T
comps2=[G2[0,0],G2[1,1],G2[2,2],G2[0,1],G2[0,2],G2[1,2]]
# symbolic jacobian ONCE (columns are entries; rows vars) - keep symbolic entries but eval fast per point
J2=sp.Matrix(comps2).jacobian([l1,l2,l3,a_,b_,c_])
R=sp.Rational
pts=[(R(1,2),R(-1,3),R(2,5),R(3),R(2),R(1)),
     (R(3,7),R(1,4),R(-1,2),R(5),R(3),R(1)),
     (R(2),R(1),R(-1),R(4),R(2),R(1)),
     (R(-1,5),R(3,4),R(1,6),R(7,2),R(2),R(1,2))]
for (a,b,c,x1,x2,x3) in pts:
    sub={a_:a,b_:b,c_:c,l1:x1,l2:x2,l3:x3}
    d=J2.subs(sub).det()
    vand=(x1-x2)*(x1-x3)*(x2-x3)
    den=(1+a*a+b*b+c*c)**2
    pred=-8*vand/den
    print(f"pt: det={d}  pred(-8*vand/den^2)={pred}  MATCH={sp.simplify(d-pred)==0}")
