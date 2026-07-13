import sympy as s
# codex's device with radials = sigma directly (D = diag(sigma_i^2)); verify at exact rational points.
t1,t2,t3=s.symbols('t1 t2 t3')
xx,yy,zz=s.symbols('xx yy zz')
K=s.Matrix([[0,-xx,-yy],[xx,0,-zz],[yy,zz,0]])
I=s.eye(3)
Q=(I-K)*(I+K).inv()
G=Q*s.diag(t1**2,t2**2,t3**2)*Q.T
outs=[G[0,0],G[1,1],G[2,2],G[0,1],G[0,2],G[1,2]]
J=s.Matrix(outs).jacobian([t1,t2,t3,xx,yy,zz])
R=s.Rational
pts=[(R(1,2),R(-1,3),R(2,5),R(3),R(2),R(1)),
     (R(2),R(1),R(-1),R(5),R(3),R(2)),
     (R(-1,5),R(3,4),R(1,6),R(4),R(2),R(1))]
for (a,b,c,s1,s2,s3) in pts:
    sub={xx:a,yy:b,zz:c,t1:s1,t2:s2,t3:s3}
    d=J.subs(sub).det()
    pred=64*s1*s2*s3*(s1**2-s2**2)*(s1**2-s3**2)*(s2**2-s3**2)/ (1+a*a+b*b+c*c)**2
    print(f"det={d}  codexPred={pred}  MATCH={s.simplify(d-pred)==0}")
