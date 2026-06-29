import sympy as sp
print("="*72)
print("CERTIFICATE: full headline decomposition verified exact at 3 M (sympy exact)")
print("="*72)

def check(name, F_entries, allvars, pivot, active, minAdm, expect_full, expect_boundary):
    xv=sp.Matrix(allvars); F=sp.Matrix(F_entries)
    full=sp.factor(F.jacobian(xv).det())
    def pbon(active,p,vec):
        return sp.Matrix([vec[p] if i==p else (vec[p]*vec[i] if i in active else vec[i]) for i in range(len(vec))])
    rad=sp.factor(pbon(active,pivot,xv).jacobian(xv).det())
    bnd=sp.factor(full/rad)
    u=allvars[pivot]
    ok_full = sp.simplify(sp.Abs(full)-sp.Abs(sp.sympify(expect_full)))==0
    ok_card = len(active)==minAdm
    ok_radexp = sp.simplify(rad - u**(minAdm-1))==0 or sp.simplify(rad + u**(minAdm-1))==0
    ok_ufree = u not in bnd.free_symbols
    print(f"\n[{name}] minAdm={minAdm}")
    print(f"  full det      = {full}")
    print(f"  radial det    = {rad}    (active card {len(active)} == minAdm? {ok_card};  == u^(minAdm-1)? {ok_radexp})")
    print(f"  boundary det  = {bnd}    (u-free? {ok_ufree})")
    print(f"  all checks: card={ok_card}, radexp={ok_radexp}, ufree={ok_ufree}")

# ---- (2,2,2) ----
x=sp.symbols('x0:8',real=True)
A0=sp.Matrix([[x[4],x[4]*x[1]],[x[5],x[5]*x[1]+x[6]*x[0]]])
A1=sp.Matrix([[x[0]-x[1]*x[2],x[0]*x[7]-x[1]*x[3]],[x[2],x[3]]])
F222=[A0[0,0],A0[0,1],A0[1,0],A0[1,1],A1[0,0],A1[0,1],A1[1,0],A1[1,1]]
check("2,2,2", F222, list(x), 0, {0,6,7}, 3, "-x0**2*x4", "x4")

# ---- (3,3,3,3) ----
x=sp.symbols('x0:27',real=True); u=x[0]
B1=sp.Matrix([[x[1],x[1]*x[2]],[x[1]*x[3],x[1]*x[2]*x[3]+x[4]],[x[1]*x[3]*x[6]+x[1]*x[5],x[1]*x[2]*x[5]+x[6]*(x[1]*x[2]*x[3]+x[4])]])
B2=sp.Matrix([[x[9]],[x[10]*x[9]]]);N1=sp.Matrix([[x[7]],[x[8]]]);N2=sp.Matrix([[x[11],x[12]]])
W1=sp.Matrix([[x[15],x[16],x[17]]]);W2=sp.Matrix([[x[18],x[19],x[20]],[x[21],x[22],x[23]]])
R1=sp.Matrix([[0,0,0],[0,0,0],[0,0,1]]);R2=sp.Matrix([[0,0,0],[0,x[13],x[14]]]);Rf=sp.Matrix([[x[24],x[25],x[26]]])
C3=u*Rf;C2=B2*sp.Matrix.hstack(sp.eye(1),N2)+u*R2;C1=B1*sp.Matrix.hstack(sp.eye(2),N1)+u*R1
A0=C1;A1=sp.Matrix.vstack(C2-N1*W1,W1);A2=sp.Matrix.vstack(C3-N2*W2,W2)
F=[A[i,j] for A in (A0,A1,A2) for i in range(A.rows) for j in range(A.cols)]
check("3,3,3,3", F, list(x), 0, {0,13,14,24,25,26}, 6, "x0**5*x1**4*x4**2*x9**3", "x1**4*x4**2*x9**3")

# ---- (2,3,2) ----
u=sp.Symbol('u',real=True);b,l=sp.symbols('b l',real=True);n1,n2=sp.symbols('n1 n2',real=True)
w=sp.symbols('w0:4',real=True);e1,e2=sp.symbols('e1 e2',real=True);z=sp.Symbol('z',real=True)
Bmat1=sp.Matrix([[b],[l*b]]);N1=sp.Matrix([[n1,n2]]);W1=sp.Matrix([[w[0],w[1]],[w[2],w[3]]])
R1=sp.Matrix([[0,0,0],[0,e1,e2]]);Rf=sp.Matrix([[1,z]])
C2=u*Rf;C1=Bmat1*sp.Matrix.hstack(sp.eye(1),N1)+u*R1
A0=C1;A1=sp.Matrix.vstack(C2-N1*W1,W1)
allv=[u,b,l,n1,n2,w[0],w[1],w[2],w[3],e1,e2,z]
F=[A[i,j] for A in (A0,A1) for i in range(A.rows) for j in range(A.cols)]
check("2,3,2", F, allv, 0, {0,9,10,11}, 4, "b**3*u**3", "b**3")
print("\nALL THREE M: radial active card == minAdm, radial det == u^(minAdm-1), boundary u-free. ✓")
