import sympy as sp
x = sp.symbols('x0:27', real=True); u=x[0]; xv=sp.Matrix(x)

# rebuild chart
B1 = sp.Matrix([[x[1], x[1]*x[2]],[x[1]*x[3], x[1]*x[2]*x[3] + x[4]],
                [x[1]*x[3]*x[6] + x[1]*x[5], x[1]*x[2]*x[5] + x[6]*(x[1]*x[2]*x[3] + x[4])]])
B2 = sp.Matrix([[x[9]],[x[10]*x[9]]]); N1=sp.Matrix([[x[7]],[x[8]]]); N2=sp.Matrix([[x[11],x[12]]])
W1=sp.Matrix([[x[15],x[16],x[17]]]); W2=sp.Matrix([[x[18],x[19],x[20]],[x[21],x[22],x[23]]])
R1=sp.Matrix([[0,0,0],[0,0,0],[0,0,1]]); R2=sp.Matrix([[0,0,0],[0,x[13],x[14]]]); Rfin3=sp.Matrix([[x[24],x[25],x[26]]])
qN1=sp.Matrix.hstack(sp.eye(2),N1); qN2=sp.Matrix.hstack(sp.eye(1),N2)
C3=u*Rfin3; C2=B2*qN2+u*R2; C1=B1*qN1+u*R1
A0=C1; A1=sp.Matrix.vstack(C2-N1*W1,W1); A2=sp.Matrix.vstack(C3-N2*W2,W2)
F=[]
for A in (A0,A1,A2):
    for i in range(A.rows):
        for j in range(A.cols):
            F.append(sp.expand(A[i,j]))
F=sp.Matrix(F)
Jfull=sp.factor(F.jacobian(xv).det())
print("full chart det =", Jfull)

# The radial blow-up factor on active = {0,13,14,24,25,26}, pivot 0.
active={0,13,14,24,25,26}; p=0
def pbon(active,p,vec):
    return sp.Matrix([vec[p] if i==p else (vec[p]*vec[i] if i in active else vec[i]) for i in range(27)])
Jrad = sp.factor(pbon(active,p,xv).jacobian(xv).det())
print("radial blow-up det (active {0,13,14,24,25,26}) =", Jrad, " (expect u0^5)")

# The COMPLEMENT factor: chart with the radial blow-up 'undone'. 
# Substitute the radial blow-up's INVERSE direction is awkward; instead directly check:
# chart det / radial det should be the 'boundary+spectator' part = u1^4 u4^2 u9^3.
boundary = sp.simplify(Jfull / Jrad)
print("chart det / radial det =", sp.factor(boundary), " (expect u1^4 u4^2 u9^3 -- the u-FREE boundary part)")
print()
# Check the boundary part is u-FREE (no x0):
print("boundary part depends on x0?", x[0] in sp.factor(boundary).free_symbols)
