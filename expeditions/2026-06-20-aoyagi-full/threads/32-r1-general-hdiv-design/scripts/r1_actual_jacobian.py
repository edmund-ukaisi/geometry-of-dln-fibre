"""
Actual symbolic Jacobian determinant of the VERIFIED hand-frames for the two
non-trivial anchors (3,3,4) [Lean banked] and (3,3,3,3) [Lean chart banked, det deferred],
plus (4,4,2,2) [pure radial], confirming:
   |det Dphi| = u^{minAdm-1} * (spectator pivot monomial),  det != 0 off {u=0}.

These use the EXACT frames transcribed from the Lean files / thread-26, with one free coord
per flat slot (a genuine square chart).  We compute the full Jacobian and factor its det.
"""
import sympy as sp
from sympy import symbols, Matrix, zeros, Poly, factor

def report(name, A_list, coords, u, minAdm):
    flat=[a[i,j] for a in A_list for i in range(a.rows) for j in range(a.cols)]
    print(f"\n== {name}  #flat={len(flat)}  #coords={len(coords)}  minAdm={minAdm}")
    assert len(flat)==len(coords), f"not square: {len(flat)} vs {len(coords)}"
    J=Matrix([[sp.diff(f,c) for c in coords] for f in flat])
    d=J.det()
    df=factor(d)
    if d==0:
        print("   det = 0  -> DEGENERATE CHART (FAIL)")
        return
    dp=Poly(sp.expand(d),u); uexp=min(m for(m,)in dp.monoms())
    print(f"   det(Dphi) = {df}")
    print(f"   u-exponent = {uexp}  (need minAdm-1 = {minAdm-1})  {'OK' if uexp==minAdm-1 else 'FAIL'}")
    # det != 0 off {u=0}: the cofactor of u^uexp is a nonzero polynomial in the spectator coords
    cof=sp.expand(d/u**uexp)
    print(f"   det/u^{uexp} (off-divisor factor) nonzero: {'OK' if cof!=0 else 'FAIL'}")

# ---------- (4,4,2,2) pure radial (matches Lean phi4422) ----------
def case_4422():
    u=symbols('u')
    coords=[u]
    A0=zeros(4,4); A1=zeros(4,2)
    for i in range(4):
        for j in range(4):
            s=symbols(f'p{i}{j}'); coords.append(s); A0[i,j]=s
    for i in range(4):
        for j in range(2):
            s=symbols(f'q{i}{j}'); coords.append(s); A1[i,j]=s
    a,b,c=symbols('a b c'); coords+= [a,b,c]
    A2=u*Matrix([[1,a],[b,c]])
    report("(4,4,2,2) pure radial", [A0,A1,A2], coords, u, 4)

# ---------- (3,3,4) verified hand-frame (matches Lean phi334, det -u0^7 u1^2) ----------
def case_334():
    # coords: u0=u (radial), u1=a (spectator pivot), then beta(2),c(2),Delta(4),tau(3),S(8) = 21
    u=symbols('u'); a=symbols('a')
    be1,be2=symbols('be1 be2'); c0,c1=symbols('c0 c1')
    D00,D01,D10,D11=symbols('D00 D01 D10 D11')
    t1,t2,t3=symbols('t1 t2 t3')
    S=[[symbols(f'S{i}{j}') for j in range(4)] for i in range(2)]
    coords=[u,a,be1,be2,c0,c1,D00,D01,D10,D11,t1,t2,t3]+[S[i][j] for i in range(2) for j in range(4)]
    beta=Matrix([[be1,be2]]); c=Matrix([[c0],[c1]])
    Delta=Matrix([[D00,D01],[D10,D11]])
    tau=Matrix([[1,t1,t2,t3]])
    Sm=Matrix(S)
    A=zeros(3,3)
    A[0,0]=a; A[0,1]=a*be1; A[0,2]=a*be2
    A[1,0]=c0; A[2,0]=c1
    sub=c*beta+u*Delta
    A[1,1]=sub[0,0]; A[1,2]=sub[0,1]; A[2,1]=sub[1,0]; A[2,2]=sub[1,1]
    Crow0=u*tau-beta*Sm
    C=zeros(3,4)
    for j in range(4):
        C[0,j]=Crow0[0,j]; C[1,j]=Sm[0,j]; C[2,j]=Sm[1,j]
    report("(3,3,4) weighted radial (Lean phi334)", [A,C], coords, u, 8)

# ---------- (3,3,3,3) verified hand-frame (matches Lean phi3333, det u^5 a^4 de^2 b^3) ----------
def case_3333():
    u=symbols('u')
    a,al,ga,de=symbols('a al ga de')
    l1,l2,m1,m2=symbols('l1 l2 m1 m2')
    b,ll,n1,n2,e1,e2=symbols('b ll n1 n2 e1 e2')
    r0,r1,r2=symbols('r0 r1 r2')
    h10,h11,h12,h20,h21,h22=symbols('h10 h11 h12 h20 h21 h22')
    z0,z1,z2=symbols('z0 z1 z2')
    coords=[u,a,al,ga,de,l1,l2,m1,m2,b,ll,n1,n2,e1,e2,r0,r1,r2,
            h10,h11,h12,h20,h21,h22,z0,z1,z2]  # 27
    K=Matrix([[a,a*al],[ga*a,ga*a*al+de]])
    P=Matrix([[1,0],[0,1],[l1,l2]]); Qm=Matrix([[1,0,m1],[0,1,m2]])
    E22=zeros(3,3); E22[2,2]=1
    A=P*K*Qm+u*E22
    D=Matrix([[1],[ll]])*b*Matrix([[1,n1,n2]])
    Y=Matrix([[0,0,0],[e1,e2,0]])
    D=D+u*Y
    r=Matrix([[r0,r1,r2]]); m=Matrix([[m1],[m2]])
    Dmr=D-m*r
    B=zeros(3,3)
    for j in range(3): B[0,j]=Dmr[0,j]; B[1,j]=Dmr[1,j]; B[2,j]=r[0,j]
    h1=Matrix([[h10,h11,h12]]); h2=Matrix([[h20,h21,h22]]); zeta=Matrix([[z0,z1,z2]])
    Crow0=u*zeta-n1*h1-n2*h2
    C=zeros(3,3)
    for j in range(3): C[0,j]=Crow0[0,j]; C[1,j]=h1[0,j]; C[2,j]=h2[0,j]
    report("(3,3,3,3) LDU+chaining (Lean phi3333)", [A,B,C], coords, u, 6)

case_4422()
case_334()
case_3333()
