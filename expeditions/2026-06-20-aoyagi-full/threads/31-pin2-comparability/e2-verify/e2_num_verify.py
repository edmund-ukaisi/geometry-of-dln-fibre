import sympy as sp, random
random.seed(7)
r, m0, mmid, mlast = 1, 1, 2, 1
def rnd(rows,cols, small=True):
    return sp.Matrix(rows,cols, lambda i,j: sp.Rational(random.randint(-3,3), random.choice([5,7,10]) if small else 1))

def run(Pf0, Qf1, label):
    bad=0
    for trial in range(6):
        X0=rnd(r,r);X1=rnd(r,r);Y0=rnd(r,mmid);Z0=rnd(m0,r);T0=rnd(m0,mmid)
        Z1=rnd(mmid,r);Y1=rnd(r,mlast);T1=rnd(mmid,mlast)
        A0=sp.eye(r)+X0;A1=sp.eye(r)+X1
        try:
            A0i=A0.inv();A1i=A1.inv()
            P00f=A0*A1+Y0*Z1;P00fi=P00f.inv()
        except Exception: continue
        K=Z1*P00fi*Y0;S1=T1-Z1*A1i*Y1;S0=T0-Z0*A0i*Y0
        W=sp.eye(mmid)+Z1*A1i*A0i*Y0
        try: Wi=W.inv()
        except Exception: continue
        T1p=Wi*((sp.eye(mmid)-K)*S1+Z1*A1i*Y1+Z1*A1i*A0i*Y0*T1)
        Y1p=Y1+A0i*Y0*(T1-T1p)
        def fb(A,B,C,D): return sp.Matrix(sp.BlockMatrix([[A,B],[C,D]]))
        def lay0(): 
            corner=fb(sp.eye(r),sp.zeros(r,mmid),sp.zeros(m0,r),sp.zeros(m0,mmid))
            return corner+Pf0*fb(X0,Y0,Z0,T0)*sp.eye(r+mmid)
        def lay1(Yv,Tv):
            corner=fb(sp.eye(r),sp.zeros(r,mlast),sp.zeros(mmid,r),sp.zeros(mmid,mlast))
            return sp.eye(r+mmid)*fb(X1,Yv,Z1,Tv)*Qf1+corner
        def energy(Yv,Tv):
            Mh=lay0()*lay1(Yv,Tv)
            B11=Mh[0:r,0:r]-sp.eye(r);B12=Mh[0:r,r:r+mlast];B21=Mh[r:r+m0,0:r]
            return sum(B[i,j]**2 for B in (B11,B12,B21) for i in range(B.rows) for j in range(B.cols))
        d=sp.simplify(energy(Y1,T1)-energy(Y1p,T1p))
        if d!=0: bad+=1
    print(f"{label}: bad/{6} = {bad}")

# (a) GENERAL boundary frames
Pf0g=sp.Matrix([[sp.Rational(2),sp.Rational(1,3)],[sp.Rational(-1,2),sp.Rational(3,2)]])
Qf1g=sp.Matrix([[sp.Rational(1),sp.Rational(2,5)],[sp.Rational(1,4),sp.Rational(-1)]])
run(Pf0g,Qf1g,"GENERAL Pf0,Qf1")
# (b) Pf0 block LOWER-tri (u12=0), Qf1 block UPPER-tri (v21=0)  [r+ (.-r) order]
Pf0lt=sp.Matrix([[sp.Rational(2),0],[sp.Rational(-1,2),sp.Rational(3,2)]])
Qf1ut=sp.Matrix([[sp.Rational(1),sp.Rational(2,5)],[0,sp.Rational(-1)]])
run(Pf0lt,Qf1ut,"Pf0 LOWER-tri, Qf1 UPPER-tri")
# (c) identity boundary frames (deepest-point trivial case)
run(sp.eye(r+m0),sp.eye(r+mlast),"IDENTITY boundary frames")
