import sympy as sp, random
random.seed(11)
r,m0,mmid,mlast=1,1,2,1
def rnd(a,b): return sp.Matrix(a,b, lambda i,j: sp.Rational(random.randint(-3,3),random.choice([5,7])))
def fb(A,B,C,D): return sp.Matrix(sp.BlockMatrix([[A,B],[C,D]]))
def run(P0,QL,label):
    bad=0;tot=0
    for _ in range(8):
        X0=rnd(r,r);X1=rnd(r,r);Y0=rnd(r,mmid);Z0=rnd(m0,r);T0=rnd(m0,mmid)
        Z1=rnd(mmid,r);Y1=rnd(r,mlast);T1=rnd(mmid,mlast)
        A0=sp.eye(r)+X0;A1=sp.eye(r)+X1
        try:
            A0i=A0.inv();A1i=A1.inv();P00f=A0*A1+Y0*Z1;P00fi=P00f.inv()
            W=sp.eye(mmid)+Z1*A1i*A0i*Y0; Wi=W.inv()
        except Exception: continue
        K=Z1*P00fi*Y0;S1=T1-Z1*A1i*Y1
        T1p=Wi*((sp.eye(mmid)-K)*S1+Z1*A1i*Y1+Z1*A1i*A0i*Y0*T1)
        Y1p=Y1+A0i*Y0*(T1-T1p)
        def prodP(Yv,Tv): return fb(A0,Y0,Z0,T0)*fb(A1,Yv,Z1,Tv)
        Bfix=fb(sp.eye(r),sp.zeros(r,mlast),sp.zeros(m0,r),sp.zeros(m0,mlast))
        def energy(Yv,Tv):
            M=P0*(prodP(Yv,Tv)-Bfix)*QL
            B11=M[0:r,0:r]; B12=M[0:r,r:r+mlast]; B21=M[r:r+m0,0:r]
            return sum(B[i,j]**2 for B in (B11,B12,B21) for i in range(B.rows) for j in range(B.cols))
        d=sp.nsimplify(sp.simplify(energy(Y1,T1)-energy(Y1p,T1p))); tot+=1
        if d!=0: bad+=1
    print(f"{label}: bad={bad} / tot={tot}")
run(sp.eye(2),sp.eye(2),"Mw P0=QL=I")
run(sp.Matrix([[2,sp.Rational(1,3)],[sp.Rational(-1,2),sp.Rational(3,2)]]),
    sp.Matrix([[1,sp.Rational(2,5)],[sp.Rational(1,4),-1]]),"Mw GENERAL")
run(sp.Matrix([[2,0],[sp.Rational(-1,2),sp.Rational(3,2)]]),
    sp.Matrix([[1,sp.Rational(2,5)],[0,-1]]),"Mw P0-lower QL-upper")
