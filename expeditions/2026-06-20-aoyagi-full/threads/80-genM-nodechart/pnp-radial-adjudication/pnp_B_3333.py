import sympy as sp
x = sp.symbols('x0:27', real=True); u=x[0]
B1 = sp.Matrix([[x[1],x[1]*x[2]],[x[1]*x[3],x[1]*x[2]*x[3]+x[4]],[x[1]*x[3]*x[6]+x[1]*x[5],x[1]*x[2]*x[5]+x[6]*(x[1]*x[2]*x[3]+x[4])]])
B2=sp.Matrix([[x[9]],[x[10]*x[9]]]);N1=sp.Matrix([[x[7]],[x[8]]]);N2=sp.Matrix([[x[11],x[12]]])
W1=sp.Matrix([[x[15],x[16],x[17]]]);W2=sp.Matrix([[x[18],x[19],x[20]],[x[21],x[22],x[23]]])
R1=sp.Matrix([[0,0,0],[0,0,0],[0,0,1]]);R2=sp.Matrix([[0,0,0],[0,x[13],x[14]]]);Rf=sp.Matrix([[x[24],x[25],x[26]]])
C3=u*Rf;C2=B2*sp.Matrix.hstack(sp.eye(1),N2)+u*R2;C1=B1*sp.Matrix.hstack(sp.eye(2),N1)+u*R1
A0=C1;A1=sp.Matrix.vstack(C2-N1*W1,W1);A2=sp.Matrix.vstack(C3-N2*W2,W2)
phi=[sp.expand(A[i,j]) for A in (A0,A1,A2) for i in range(A.rows) for j in range(A.cols)]
# active = {0,13,14,24,25,26}. Check each active i (!=0) appears ONLY as x0*x_i (paired with pivot).
active=[13,14,24,25,26]
allok=True
for k in active:
    appears=[e for e in phi if x[k] in e.free_symbols]
    # check: in each occurrence, x_k always multiplied by x0 (degree of x0 in every x_k-term is >=1)
    paired=True
    for e in appears:
        p=sp.Poly(e,*x)
        for mono,co in p.terms():
            if mono[k]>0 and mono[0]==0:  # x_k appears WITHOUT x0
                paired=False
    print(f"x{k}: appears in {len(appears)} outputs; always paired with x0? {paired}")
    allok = allok and paired
print("\nALL actives appear ONLY as x0*x_active (=> B division-free) ?", allok)
